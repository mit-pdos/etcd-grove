"""The linearization search: is there an order of a component's operations, consistent with their
real-time intervals, in which every step is one the (lazy) model allows?

Wing & Gong's search with Lowe's memoization, as porcupine and dsverify-lab's lincheck.py do it,
generalized in three ways:

- **Several successors per step.** An operation's step returns a list of (state, choice); the
  search tries each (most of the model's hidden choices are lazy, lazy.py, so most steps have one).
- **Optional operations.** An operation cut short by its process's end (a `B` record with no `E`)
  may take effect or not: its step's successors, plus "dropped" (no effect). Its `ret` is the
  latest time it could have taken effect (its process's end), or None if unbounded; like every
  operation with a `ret`, it must be linearized or dropped before the search passes its return.
- **Operations of several steps.** A successor may be partial, (state, choice, True): the step
  happens, the operation is not done (a Go Write is a loop of the extension's steps, each at its
  own point in the call's interval). Its next step is tried from the new state like any other
  candidate; steps must make progress (lazy.py's do), so that the search terminates. The
  linearization lists every step, partial ones included.
- **Precedence.** An operation may name operations that must be done (linearized or dropped)
  before it (`preds`, a bit mask): a node's crash follows its old process's operations.

Real time: `a` must precede `b` iff `a.ret < b.call` (strictly); calls are sorted before returns
at equal times, so such operations count as concurrent. The search walks the call and return
events in time order; it may linearize any call that precedes the first return of an operation
not yet done; reaching such a return, it backtracks. A (done set, state) pair seen before is not
explored again. It is exhaustive: it answers no only when no order (and no choice of successors)
works, or reports that it hit its step limit.
"""


class Op:
    __slots__ = ("call", "ret", "step", "optional", "preds", "desc", "ref")

    def __init__(self, call, ret, step, desc, ref=None, optional=False, preds=0):
        # step(state, is_done) -> (list of (state', choice), reason when empty); is_done(i)
        # tells whether op i (an index into the list given to search) is done
        self.call, self.ret, self.step, self.desc, self.ref = call, ret, step, desc, ref
        self.optional, self.preds = optional, preds


class Result:
    def __init__(self, ok, order=None, fail=None, steps=0, limit=False):
        self.ok = ok
        self.order = order    # when ok: [(op index, choice)] in linearization order (dropped ops omitted)
        self.fail = fail      # when not ok: dict, see search()
        self.steps = steps
        self.limit = limit    # the step limit was reached (no verdict)


class _E:
    __slots__ = ("is_ret", "id", "prev", "next", "match")

    def __init__(self, is_ret, i):
        self.is_ret, self.id, self.prev, self.next, self.match = is_ret, i, None, None, None


def _lift(e):
    e.prev.next = e.next
    if e.next:
        e.next.prev = e.prev
    m = e.match
    if m:
        m.prev.next = m.next
        if m.next:
            m.next.prev = m.prev


def _unlift(e):
    m = e.match
    if m:
        m.prev.next = m
        if m.next:
            m.next.prev = m
    e.prev.next = e
    if e.next:
        e.next.prev = e


def _key(done, state):
    # the done set is mostly a prefix of the ops (sorted by call): (its length, the rest)
    p = (~done & (done + 1)).bit_length() - 1
    return (p, done >> p, state)


DROP = "dropped"


def search(ops, init, limit=5_000_000):
    """ops: list of Op (any order; indices in the result are into this list). Returns a Result.
    When not ok, fail has: 'op' (index of the operation whose return could not be passed at the
    deepest point of the search: the first operation no linearization admits), 'state' (the state
    there), 'prefix' (the linearization up to there, [(index, choice)]), 'why' (that operation's
    step's reason there, or why it could not be tried), 'tried' ([(index, reason)] for the other
    operations that were candidates there)."""
    n = len(ops)
    order_idx = sorted(range(n), key=lambda i: (ops[i].call, i))
    pos = {i: j for j, i in enumerate(order_idx)}  # op index -> bit position
    sops = [ops[i] for i in order_idx]
    # preds re-expressed over bit positions
    preds = []
    for op in sops:
        m = 0
        p = op.preds
        i = 0
        while p:
            if p & 1:
                m |= 1 << pos[i]
            p >>= 1
            i += 1
        preds.append(m)
    evs = []
    for j, op in enumerate(sops):
        evs.append((op.call, 0, j))
        if op.ret is not None:
            evs.append((op.ret, 1, j))
    evs.sort()
    head = _E(False, -1)
    prev = head
    calls = {}
    for t, kind, j in evs:
        e = _E(kind == 1, j)
        if kind == 0:
            calls[j] = e
        else:
            calls[j].match = e
        e.prev = prev
        prev.next = e
        prev = e
    remaining = sum(1 for op in sops if op.ret is not None)
    state = init
    done = 0
    stack = []  # frames: [entry, state before, done before, successors, index tried]
    seen = set()
    best = None
    steps = 0
    entry = head.next
    reasons = {}

    def succs_of(j, st, dn):
        op = sops[j]
        lst, why = op.step(st, lambda i: (dn >> pos[i]) & 1 == 1)
        lst = list(lst)
        if op.optional:
            lst.append((st, DROP))
        return lst, why

    def push(entry, lst, start):
        nonlocal state, done, remaining
        j = entry.id
        bit = 1 << j
        for x in range(start, len(lst)):
            ns, ch = lst[x][0], lst[x][1]
            partial = len(lst[x]) > 2 and lst[x][2]
            nd = done if partial else done | bit
            k = _key(nd, ns)
            if k in seen:
                continue
            seen.add(k)
            stack.append([entry, state, done, lst, x])
            state, done = ns, nd
            if not partial:
                if sops[j].ret is not None:
                    remaining -= 1
                _lift(entry)
            return True
        return False

    def _partial(f):
        s = f[3][f[4]]
        return len(s) > 2 and s[2]

    while True:
        if remaining == 0:
            order = [(order_idx[f[0].id], f[3][f[4]][1]) for f in stack if f[3][f[4]][1] != DROP]
            return Result(True, order=order, steps=steps)
        steps += 1
        if steps > limit:
            return Result(False, fail={"op": None, "why": f"search limit ({limit} steps) reached"},
                          steps=steps, limit=True)
        if entry is not None and not entry.is_ret:
            j = entry.id
            if preds[j] & ~done:
                reasons[j] = "waits for an operation that must come first (a crash's process)"
            else:
                lst, why = succs_of(j, state, done)
                if push(entry, lst, 0):
                    reasons = {}
                    entry = head.next
                    continue
                reasons[j] = why or "every outcome leads to a dead end explored before"
            entry = entry.next
            continue
        # a return of an operation not done (or the end): backtrack
        if entry is not None:
            j = entry.id
            depth = len(stack)
            if best is None or depth > best[0] or (depth == best[0] and sops[j].ret < sops[best[1]].ret):
                why = reasons.get(j)
                if why is None:
                    why = "it was not reached (an earlier return blocks it)"
                tried = [(order_idx[x], r) for x, r in reasons.items() if x != j]
                best = (depth, j, state, [(order_idx[f[0].id], f[3][f[4]][1]) for f in stack], why, tried)
        while True:
            if not stack:
                if best is None:
                    return Result(False, fail={"op": None, "why": "no operation can be linearized"}, steps=steps)
                depth, j, st, prefix, why, tried = best
                return Result(False, fail={"op": order_idx[j], "state": st, "prefix": prefix,
                                           "why": why, "tried": tried}, steps=steps)
            f = stack.pop()
            e, state, done, lst, x = f
            if not _partial(f):
                if sops[e.id].ret is not None:
                    remaining += 1
                _unlift(e)
            if push(e, lst, x + 1):
                reasons = {}
                entry = head.next
                break
            entry = e.next
            reasons = {}
            break
