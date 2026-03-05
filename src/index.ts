import { type ReactiveNode, type Link, ReactiveFlags } from './system.js';
export { createReactiveSystem, ReactiveFlags, type ReactiveNode, type Link } from './system.js';

interface EffectNode extends ReactiveNode {
	fn(): void;
}

interface ComputedNode<T = any> extends ReactiveNode {
	value: T | undefined;
	getter: (previousValue?: T) => T;
}

interface SignalNode<T = any> extends ReactiveNode {
	currentValue: T;
	pendingValue: T;
}

let cycle = 0;
let batchDepth = 0;
let notifyIndex = 0;
let queuedLength = 0;
let activeSub: ReactiveNode | undefined;

const queued: (EffectNode | undefined)[] = [];

// === System functions (inlined to avoid closure/callback overhead) ===

function link(dep: ReactiveNode, sub: ReactiveNode, version: number): void {
	const prevDep = sub.depsTail;
	if (prevDep !== undefined && prevDep.dep === dep) {
		return;
	}
	const nextDep = prevDep !== undefined ? prevDep.nextDep : sub.deps;
	if (nextDep !== undefined && nextDep.dep === dep) {
		nextDep.version = version;
		sub.depsTail = nextDep;
		return;
	}
	const prevSub = dep.subsTail;
	if (prevSub !== undefined && prevSub.version === version && prevSub.sub === sub) {
		return;
	}
	const newLink
		= sub.depsTail
		= dep.subsTail
		= {
			version,
			dep,
			sub,
			prevDep,
			nextDep,
			prevSub,
			nextSub: undefined,
		};
	if (nextDep !== undefined) {
		nextDep.prevDep = newLink;
	}
	if (prevDep !== undefined) {
		prevDep.nextDep = newLink;
	} else {
		sub.deps = newLink;
	}
	if (prevSub !== undefined) {
		prevSub.nextSub = newLink;
	} else {
		dep.subs = newLink;
	}
}

function unlinkNode(l: Link, sub = l.sub): Link | undefined {
	const dep = l.dep;
	const prevDep = l.prevDep;
	const nextDep = l.nextDep;
	const nextSub = l.nextSub;
	const prevSub = l.prevSub;
	if (nextDep !== undefined) {
		nextDep.prevDep = prevDep;
	} else {
		sub.depsTail = prevDep;
	}
	if (prevDep !== undefined) {
		prevDep.nextDep = nextDep;
	} else {
		sub.deps = nextDep;
	}
	if (nextSub !== undefined) {
		nextSub.prevSub = prevSub;
	} else {
		dep.subsTail = prevSub;
	}
	if (prevSub !== undefined) {
		prevSub.nextSub = nextSub;
	} else if ((dep.subs = nextSub) === undefined) {
		handleUnwatched(dep);
	}
	return nextDep;
}

interface StackNode {
	value: Link | undefined;
	prev: StackNode | undefined;
}

function propagate(l: Link): void {
	let next = l.nextSub;
	let stack: StackNode | undefined;

	top: do {
		const sub = l.sub;
		let flags = sub.flags;

		if (!(flags & (ReactiveFlags.RecursedCheck | ReactiveFlags.Recursed | ReactiveFlags.Dirty | ReactiveFlags.Pending))) {
			sub.flags = flags | ReactiveFlags.Pending;
		} else if (!(flags & (ReactiveFlags.RecursedCheck | ReactiveFlags.Recursed))) {
			flags = ReactiveFlags.None;
		} else if (!(flags & ReactiveFlags.RecursedCheck)) {
			sub.flags = (flags & ~ReactiveFlags.Recursed) | ReactiveFlags.Pending;
		} else if (!(flags & (ReactiveFlags.Dirty | ReactiveFlags.Pending)) && isValidLink(l, sub)) {
			sub.flags = flags | (ReactiveFlags.Recursed | ReactiveFlags.Pending);
			flags &= ReactiveFlags.Mutable;
		} else {
			flags = ReactiveFlags.None;
		}

		if (flags & ReactiveFlags.Watching) {
			notifyEffect(sub as EffectNode);
		}

		if (flags & ReactiveFlags.Mutable) {
			const subSubs = sub.subs;
			if (subSubs !== undefined) {
				const nextSub = (l = subSubs).nextSub;
				if (nextSub !== undefined) {
					stack = { value: next, prev: stack };
					next = nextSub;
				}
				continue;
			}
		}

		if ((l = next!) !== undefined) {
			next = l.nextSub;
			continue;
		}

		while (stack !== undefined) {
			l = stack.value!;
			stack = stack.prev;
			if (l !== undefined) {
				next = l.nextSub;
				continue top;
			}
		}

		break;
	} while (true);
}

function checkDirty(l: Link, sub: ReactiveNode): boolean {
	const prevActiveSub = activeSub;
	let stack: StackNode | undefined;
	let checkDepth = 0;
	let dirty = false;
	++cycle;

	try {
	top: do {
		const dep = l.dep;
		const flags = dep.flags;

		if (sub.flags & ReactiveFlags.Dirty) {
			dirty = true;
		} else if ((flags & (ReactiveFlags.Mutable | ReactiveFlags.Dirty)) === (ReactiveFlags.Mutable | ReactiveFlags.Dirty)) {
			// Direct dispatch: check depsTail to determine computed vs signal
			if (dep.depsTail !== undefined) {
				if (updateComputedDirect(dep as ComputedNode)) {
					const subs = dep.subs!;
					if (subs.nextSub !== undefined) {
						shallowPropagate(subs);
					}
					dirty = true;
				}
			} else if (updateSignal(dep as SignalNode)) {
				const subs = dep.subs!;
				if (subs.nextSub !== undefined) {
					shallowPropagate(subs);
				}
				dirty = true;
			}
		} else if ((flags & (ReactiveFlags.Mutable | ReactiveFlags.Pending)) === (ReactiveFlags.Mutable | ReactiveFlags.Pending)) {
			if (l.nextSub !== undefined || l.prevSub !== undefined) {
				stack = { value: l, prev: stack };
			}
			l = dep.deps!;
			sub = dep;
			++checkDepth;
			continue;
		}

		if (!dirty) {
			const nextDep = l.nextDep;
			if (nextDep !== undefined) {
				l = nextDep;
				continue;
			}
		}

		while (checkDepth--) {
			const firstSub = sub.subs!;
			const hasMultipleSubs = firstSub.nextSub !== undefined;
			if (hasMultipleSubs) {
				l = stack!.value!;
				stack = stack!.prev;
			} else {
				l = firstSub;
			}
			if (dirty) {
				if (updateComputedDirect(sub as ComputedNode)) {
					if (hasMultipleSubs) {
						shallowPropagate(firstSub);
					}
					sub = l.sub;
					continue;
				}
				dirty = false;
			} else {
				sub.flags &= ~ReactiveFlags.Pending;
			}
			sub = l.sub;
			const nextDep = l.nextDep;
			if (nextDep !== undefined) {
				l = nextDep;
				continue top;
			}
		}

		return dirty;
	} while (true);
	} catch (e) {
		// activeSub points to the computed whose getter threw
		if (activeSub !== prevActiveSub) {
			(activeSub as ComputedNode).flags &= ~ReactiveFlags.RecursedCheck;
			purgeDeps(activeSub!);
		}
		throw e;
	} finally {
		activeSub = prevActiveSub;
	}
}

function shallowPropagate(l: Link): void {
	do {
		const sub = l.sub;
		const flags = sub.flags;
		if ((flags & (ReactiveFlags.Pending | ReactiveFlags.Dirty)) === ReactiveFlags.Pending) {
			sub.flags = flags | ReactiveFlags.Dirty;
			if ((flags & (ReactiveFlags.Watching | ReactiveFlags.RecursedCheck)) === ReactiveFlags.Watching) {
				notifyEffect(sub as EffectNode);
			}
		}
	} while ((l = l.nextSub!) !== undefined);
}

function isValidLink(checkLink: Link, sub: ReactiveNode): boolean {
	let l = sub.depsTail;
	while (l !== undefined) {
		if (l === checkLink) {
			return true;
		}
		l = l.prevDep;
	}
	return false;
}

// === Notify / Unwatched ===

function notifyEffect(effect: EffectNode): void {
	let insertIndex = queuedLength;
	let firstInsertedIndex = insertIndex;

	do {
		queued[insertIndex++] = effect;
		effect.flags &= ~ReactiveFlags.Watching;
		effect = effect.subs?.sub as EffectNode;
		if (effect === undefined || !(effect.flags & ReactiveFlags.Watching)) {
			break;
		}
	} while (true);

	queuedLength = insertIndex;

	while (firstInsertedIndex < --insertIndex) {
		const left = queued[firstInsertedIndex];
		queued[firstInsertedIndex++] = queued[insertIndex];
		queued[insertIndex] = left;
	}
}

function handleUnwatched(node: ReactiveNode): void {
	if (!(node.flags & ReactiveFlags.Mutable)) {
		effectScopeOper.call(node);
	} else if (node.depsTail !== undefined) {
		node.depsTail = undefined;
		node.flags = ReactiveFlags.Mutable | ReactiveFlags.Dirty;
		purgeDeps(node);
	}
}

// === Public API ===

export function getActiveSub(): ReactiveNode | undefined {
	return activeSub;
}

export function setActiveSub(sub?: ReactiveNode) {
	const prevSub = activeSub;
	activeSub = sub;
	return prevSub;
}

export function getBatchDepth(): number {
	return batchDepth;
}

export function startBatch() {
	++batchDepth;
}

export function endBatch() {
	if (!--batchDepth) {
		flush();
	}
}

export function isSignal(fn: () => void): boolean {
	return fn.name === 'bound ' + signalOper.name;
}

export function isComputed(fn: () => void): boolean {
	return fn.name === 'bound ' + computedOper.name;
}

export function isEffect(fn: () => void): boolean {
	return fn.name === 'bound ' + effectOper.name;
}

export function isEffectScope(fn: () => void): boolean {
	return fn.name === 'bound ' + effectScopeOper.name;
}

export function signal<T>(): {
	(): T | undefined;
	(value: T | undefined): void;
};
export function signal<T>(initialValue: T): {
	(): T;
	(value: T): void;
};
export function signal<T>(initialValue?: T): {
	(): T | undefined;
	(value: T | undefined): void;
} {
	return signalOper.bind({
		currentValue: initialValue,
		pendingValue: initialValue,
		subs: undefined,
		subsTail: undefined,
		flags: ReactiveFlags.Mutable,
	}) as () => T | undefined;
}

export function computed<T>(getter: (previousValue?: T) => T): () => T {
	return computedOper.bind({
		value: undefined,
		subs: undefined,
		subsTail: undefined,
		deps: undefined,
		depsTail: undefined,
		flags: ReactiveFlags.None,
		getter: getter as (previousValue?: unknown) => unknown,
	}) as () => T;
}

export function effect(fn: () => void): () => void {
	const e: EffectNode = {
		fn,
		subs: undefined,
		subsTail: undefined,
		deps: undefined,
		depsTail: undefined,
		flags: ReactiveFlags.Watching | ReactiveFlags.RecursedCheck,
	};
	const prevSub = activeSub;
	activeSub = e;
	if (prevSub !== undefined) {
		link(e, prevSub, 0);
	}
	try {
		e.fn();
	} finally {
		activeSub = prevSub;
		e.flags &= ~ReactiveFlags.RecursedCheck;
	}
	return effectOper.bind(e);
}

export function effectScope(fn: () => void): () => void {
	const e: ReactiveNode = {
		deps: undefined,
		depsTail: undefined,
		subs: undefined,
		subsTail: undefined,
		flags: ReactiveFlags.None,
	};
	const prevSub = activeSub;
	activeSub = e;
	if (prevSub !== undefined) {
		link(e, prevSub, 0);
	}
	try {
		fn();
	} finally {
		activeSub = prevSub;
	}
	return effectScopeOper.bind(e);
}

export function trigger(fn: () => void) {
	const sub: ReactiveNode = {
		deps: undefined,
		depsTail: undefined,
		flags: ReactiveFlags.Watching,
	};
	const prevSub = activeSub;
	activeSub = sub;
	try {
		fn();
	} finally {
		activeSub = prevSub;
		let l = sub.deps;
		while (l !== undefined) {
			const dep = l.dep;
			l = unlinkNode(l, sub);
			const subs = dep.subs;
			if (subs !== undefined) {
				sub.flags = ReactiveFlags.None;
				propagate(subs);
				shallowPropagate(subs);
			}
		}
		if (!batchDepth) {
			flush();
		}
	}
}

// Fast path: no try/finally, activeSub managed by caller (checkDirty)
// cycle is incremented once in checkDirty, not per-call
function updateComputedDirect(c: ComputedNode): boolean {
	c.depsTail = undefined;
	c.flags = ReactiveFlags.Mutable | ReactiveFlags.RecursedCheck;
	activeSub = c;
	const oldValue = c.value;
	const newValue = c.getter(oldValue);
	c.value = newValue;
	c.flags = ReactiveFlags.Mutable;
	const dt = c.depsTail;
	if (dt !== undefined) {
		let d = dt.nextDep;
		while (d !== undefined) {
			d = unlinkNode(d, c);
		}
	} else {
		let d = c.deps;
		while (d !== undefined) {
			d = unlinkNode(d, c);
		}
	}
	return oldValue !== newValue;
}

// Safe path: with try/finally for use by computedOper and external callers
function updateComputed(c: ComputedNode): boolean {
	++cycle;
	c.depsTail = undefined;
	c.flags = ReactiveFlags.Mutable | ReactiveFlags.RecursedCheck;
	const prevSub = activeSub;
	activeSub = c;
	try {
		const oldValue = c.value;
		return oldValue !== (c.value = c.getter(oldValue));
	} finally {
		activeSub = prevSub;
		c.flags = ReactiveFlags.Mutable;
		const dt = c.depsTail;
		if (dt !== undefined) {
			let d = dt.nextDep;
			while (d !== undefined) {
				d = unlinkNode(d, c);
			}
		} else {
			let d = c.deps;
			while (d !== undefined) {
				d = unlinkNode(d, c);
			}
		}
	}
}

function updateSignal(s: SignalNode): boolean {
	s.flags = ReactiveFlags.Mutable;
	return s.currentValue !== (s.currentValue = s.pendingValue);
}

function run(e: EffectNode): void {
	const flags = e.flags;
	if (
		flags & ReactiveFlags.Dirty
		|| (
			flags & ReactiveFlags.Pending
			&& checkDirty(e.deps!, e)
		)
	) {
		++cycle;
		e.depsTail = undefined;
		e.flags = ReactiveFlags.Watching | ReactiveFlags.RecursedCheck;
		const prevSub = activeSub;
		activeSub = e;
		try {
			(e as EffectNode).fn();
		} finally {
			activeSub = prevSub;
			e.flags = ReactiveFlags.Watching;
			const dt = e.depsTail;
			if (dt !== undefined) {
				let d = dt.nextDep;
				while (d !== undefined) {
					d = unlinkNode(d, e);
				}
			} else {
				let d = e.deps;
				while (d !== undefined) {
					d = unlinkNode(d, e);
				}
			}
		}
	} else {
		e.flags = ReactiveFlags.Watching;
	}
}

function flush(): void {
	try {
		while (notifyIndex < queuedLength) {
			const effect = queued[notifyIndex]!;
			queued[notifyIndex++] = undefined;
			run(effect);
		}
	} finally {
		while (notifyIndex < queuedLength) {
			const effect = queued[notifyIndex]!;
			queued[notifyIndex++] = undefined;
			effect.flags |= ReactiveFlags.Watching | ReactiveFlags.Recursed;
		}
		notifyIndex = 0;
		queuedLength = 0;
	}
}

function computedOper<T>(this: ComputedNode<T>): T {
	const flags = this.flags;
	if (
		flags & ReactiveFlags.Dirty
		|| (
			flags & ReactiveFlags.Pending
			&& (
				checkDirty(this.deps!, this)
				|| (this.flags = flags & ~ReactiveFlags.Pending, false)
			)
		)
	) {
		if (updateComputed(this)) {
			const subs = this.subs;
			if (subs !== undefined) {
				shallowPropagate(subs);
			}
		}
	} else if (!flags) {
		this.flags = ReactiveFlags.Mutable | ReactiveFlags.RecursedCheck;
		const prevSub = activeSub;
		activeSub = this;
		try {
			this.value = this.getter();
		} finally {
			activeSub = prevSub;
			this.flags &= ~ReactiveFlags.RecursedCheck;
		}
	}
	const sub = activeSub;
	if (sub !== undefined) {
		const prevDep = sub.depsTail;
		if (prevDep === undefined) {
			const nextDep = sub.deps;
			if (nextDep !== undefined && nextDep.dep === (this as ReactiveNode)) {
				nextDep.version = cycle;
				sub.depsTail = nextDep;
			} else {
				link(this, sub, cycle);
			}
		} else if (prevDep.dep !== (this as ReactiveNode)) {
			const nextDep = prevDep.nextDep;
			if (nextDep !== undefined && nextDep.dep === (this as ReactiveNode)) {
				nextDep.version = cycle;
				sub.depsTail = nextDep;
			} else {
				link(this, sub, cycle);
			}
		}
	}
	return this.value!;
}

function signalOper<T>(this: SignalNode<T>): T | void {
	if (arguments.length) {
		const value = arguments[0] as T;
		if (this.pendingValue !== (this.pendingValue = value)) {
			this.flags = ReactiveFlags.Mutable | ReactiveFlags.Dirty;
			const subs = this.subs;
			if (subs !== undefined) {
				propagate(subs);
				if (!batchDepth) {
					flush();
				}
			}
		}
	} else {
		if (this.flags & ReactiveFlags.Dirty) {
			if (updateSignal(this)) {
				const subs = this.subs;
				if (subs !== undefined) {
					shallowPropagate(subs);
				}
			}
		}
		let sub = activeSub;
		while (sub !== undefined) {
			if (sub.flags & (ReactiveFlags.Mutable | ReactiveFlags.Watching)) {
				link(this, sub, cycle);
				break;
			}
			sub = sub.subs?.sub;
		}
		return this.currentValue;
	}
}

function effectOper(this: EffectNode): void {
	effectScopeOper.call(this);
}

function effectScopeOper(this: ReactiveNode): void {
	this.depsTail = undefined;
	this.flags = ReactiveFlags.None;
	purgeDeps(this);
	const sub = this.subs;
	if (sub !== undefined) {
		unlinkNode(sub);
	}
}

function purgeDeps(sub: ReactiveNode) {
	const depsTail = sub.depsTail;
	let dep = depsTail !== undefined ? depsTail.nextDep : sub.deps;
	while (dep !== undefined) {
		dep = unlinkNode(dep, sub);
	}
}
