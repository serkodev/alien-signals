export interface ReactiveNode {
	deps?: Link;
	depsTail?: Link;
	subs?: Link;
	subsTail?: Link;
	flags: ReactiveFlags;
}

export interface Link {
	version: number;
	dep: ReactiveNode;
	sub: ReactiveNode;
	prevSub: Link | undefined;
	nextSub: Link | undefined;
	prevDep: Link | undefined;
	nextDep: Link | undefined;
}

export const enum ReactiveFlags {
	None = 0,
	Mutable = 1,
	Watching = 2,
	RecursedCheck = 4,
	Recursed = 8,
	Dirty = 16,
	Pending = 32,
}

export function createReactiveSystem({
	update,
	notify,
	unwatched,
}: {
	update(sub: ReactiveNode): boolean;
	notify(sub: ReactiveNode): void;
	unwatched(sub: ReactiveNode): void;
}) {
	const stackProp: (Link | undefined)[] = [];
	const stackDirty: Link[] = [];

	return {
		link,
		unlink,
		propagate,
		checkDirty,
		shallowPropagate,
	};

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

	function unlink(link: Link, sub = link.sub): Link | undefined {
		const dep = link.dep;
		const prevDep = link.prevDep;
		const nextDep = link.nextDep;
		const nextSub = link.nextSub;
		const prevSub = link.prevSub;
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
			unwatched(dep);
		}
		return nextDep;
	}

	function propagate(link: Link): void {
		let currLink: Link = link;
		let next = currLink.nextSub;
		let stackIndex = 0;

		top: do {
			const sub = currLink.sub;
			let flags = sub.flags;

			if (!(flags & (ReactiveFlags.RecursedCheck | ReactiveFlags.Recursed | ReactiveFlags.Dirty | ReactiveFlags.Pending))) {
				sub.flags = flags | ReactiveFlags.Pending;
			} else if (!(flags & (ReactiveFlags.RecursedCheck | ReactiveFlags.Recursed))) {
				flags = ReactiveFlags.None;
			} else if (!(flags & ReactiveFlags.RecursedCheck)) {
				sub.flags = (flags & ~ReactiveFlags.Recursed) | ReactiveFlags.Pending;
			} else if (!(flags & (ReactiveFlags.Dirty | ReactiveFlags.Pending))) {
				let linkCheck = sub.depsTail;
				while (linkCheck !== undefined && linkCheck !== currLink) {
					linkCheck = linkCheck.prevDep;
				}
				if (linkCheck !== undefined) {
					sub.flags = flags | (ReactiveFlags.Recursed | ReactiveFlags.Pending);
					flags &= ReactiveFlags.Mutable;
				} else {
					flags = ReactiveFlags.None;
				}
			} else {
				flags = ReactiveFlags.None;
			}

			if (flags & ReactiveFlags.Watching) {
				notify(sub);
			}

			if (flags & ReactiveFlags.Mutable) {
				const subSubs = sub.subs;
				if (subSubs !== undefined) {
					const nextSub = (currLink = subSubs).nextSub;
					if (nextSub !== undefined) {
						stackProp[stackIndex++] = next;
						next = nextSub;
					}
					continue;
				}
			}
			if ((currLink = next!) !== undefined) {
				next = currLink.nextSub;
				continue;
			}

			while (stackIndex > 0) {
				currLink = stackProp[--stackIndex]!;
				if (currLink !== undefined) {
					next = currLink.nextSub;
					continue top;
				}
			}

			break;
		} while (true);
	}

	function checkDirty(link: Link, sub: ReactiveNode): boolean {
		let currLink: Link = link;
		let currSub: ReactiveNode = sub;
		let stackIndex = 0;
		let checkDepth = 0;
		let dirty = false;

		top: do {
			const dep = currLink.dep;
			const flags = dep.flags;

			if (currSub.flags & ReactiveFlags.Dirty) {
				dirty = true;
			} else if ((flags & (ReactiveFlags.Mutable | ReactiveFlags.Dirty)) === (ReactiveFlags.Mutable | ReactiveFlags.Dirty)) {
				if (update(dep)) {
					const subs = dep.subs!;
					if (subs.nextSub !== undefined) {
						shallowPropagate(subs);
					}
					dirty = true;
				}
			} else if ((flags & (ReactiveFlags.Mutable | ReactiveFlags.Pending)) === (ReactiveFlags.Mutable | ReactiveFlags.Pending)) {
				if (currLink.nextSub !== undefined || currLink.prevSub !== undefined) {
					stackDirty[stackIndex++] = currLink;
				}
				currLink = dep.deps!;
				currSub = dep;
				checkDepth++;
				continue;
			}

			if (!dirty) {
				const nextDep = currLink.nextDep;
				if (nextDep !== undefined) {
					currLink = nextDep;
					continue;
				}
			}

			while (checkDepth > 0) {
				checkDepth--;
				const firstSub = currSub.subs!;
				const hasMultipleSubs = firstSub.nextSub !== undefined;
				currLink = hasMultipleSubs ? stackDirty[--stackIndex] : firstSub;
				if (dirty) {
					if (update(currSub)) {
						if (hasMultipleSubs) {
							shallowPropagate(firstSub);
						}
						currSub = currLink.sub;
						continue;
					}
					dirty = false;
				} else {
					currSub.flags &= ~ReactiveFlags.Pending;
				}
				currSub = currLink.sub;
				const nextDep = currLink.nextDep;
				if (nextDep !== undefined) {
					currLink = nextDep;
					continue top;
				}
			}

			return dirty;
		} while (true);
	}

	function shallowPropagate(link: Link): void {
		let curr: Link | undefined = link;
		while (curr !== undefined) {
			const sub = curr.sub;
			const flags = sub.flags;
			if ((flags & (ReactiveFlags.Pending | ReactiveFlags.Dirty)) === ReactiveFlags.Pending) {
				sub.flags = flags | ReactiveFlags.Dirty;
				if (flags & ReactiveFlags.Watching) {
					notify(sub);
				}
			}
			curr = curr.nextSub;
		}
	}
}
