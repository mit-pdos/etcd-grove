"""The witness of an admitted run: the components' linearizations merged into one, made concrete
(every hidden choice of the model taken), and replayed through model.py's literal transcription
of Impl.lean: each step is checked by `model.net_step` (or `model.crash`). A step that does not
replay is a checker bug (the lazy model of lazy.py, or the merge, disagrees with model.py).

The merge (README.md, "The witness"): each operation of a component's linearization gets the
point tau = the latest call time of it and of every operation before it in that linearization
(a point in its interval, non-decreasing along the linearization); the witness is every
component's operations sorted by tau (address components before connections at equal tau), with
a node's crash between its processes. This order respects real time and each component's order.

Concrete choices, made here as the lazy model leaves them: a Read cuts only when its result needs
it (EOF of a direction with bytes left or open: keeping nothing; a sys error of one not cut and
empty: keeping nothing, v3.5), except a Read marked to cut (keeping every byte, nothing for a sys
error): when a Write's result needs
its direction cut and it is shut (FIN), the direction's reader's last Read before it is marked and
the replay starts over (lazy.py's `a`: that is the cut gamma has). A connection no Dial returned
(an Accept's) is the first one pending at the address the search chose for it (lazy.py's
`accept`, choice {"token": address}, an address its listener takes) that a failed or unfinished
Dial left (in witness order); a failed Dial whose connection no Accept took is a plain failure; an unfinished
Dial no Accept needed is left out.

Each model step is checked on the connections it touches only (a one-connection NetGlobal): the
steps of NetStep change at most one connection (`NetGlobal.setConn`) and read no other, so this is
the relation on the whole state with the others unchanged.
"""

import model as M
import lazy as Z

FORMAT = "net-witness"
VERSION = 2  # v3.4: no plan, and a Listen step has no `a0` (it listens at its own address)


class ReplayError(Exception):
    pass


class _Restart(Exception):
    pass


def _entries(ck):
    ents = []
    n = 0
    for ci, cp in enumerate(ck.comps):
        tau = None
        for pos, (i, ch) in enumerate(cp.result.order):
            item = cp.items[i]
            if item["kind"] == "crash":
                continue
            op = cp.ops[i]
            tau = op.call if tau is None else max(tau, op.call)
            ents.append(((tau, 0 if cp.kind == "addr" else 1, ci, pos), ("op", cp, i, ch)))
    for ch in ck.chains:
        for i in range(len(ch.procs) - 1):
            tau = ck.death[ch.procs[i].pid] + 1  # after the process's end, at or before the next's start
            n += 1
            ents.append(((tau, -1, -1, n), ("crash", ch, i, None)))
    ents.sort(key=lambda e: e[0])
    return ents


def build(ck):
    ents = _entries(ck)
    # connections no Dial returned: each unmatched Accept takes the first token (in witness order)
    # of the address the search chose for it, not taken yet
    queue = {}
    token_of = {}   # entry index of an Accept -> entry index of the Dial whose connection it took
    used = set()
    for x, (_, (kind, cp, i, ch)) in enumerate(ents):
        if kind != "op" or cp.kind != "addr":
            continue
        c = cp.calls[i]
        if c.op in ("Dial", "DialTimeout") and isinstance(ch, dict):
            queue.setdefault(c.b.get("addr", "").encode(), []).append(x)
        elif c.op == "Accept" and c.e is not None:
            m = ck.mapped[id(c)]
            if m.res[0] == "ok" and ck.accept_conn.get(id(c)) is None:
                a = (ch or {}).get("token")
                q = queue.get(a, [])
                if not q:
                    raise ReplayError(f"{c.where()}: no connection no Dial returned is pending at {a}")
                token_of[x] = q.pop(0)
                used.add(token_of[x])
    marks = set()
    for _ in range(10000):
        try:
            return _replay(ck, ents, token_of, used, marks)
        except _Restart:
            continue
    raise ReplayError("too many restarts")


def _read_result(m, choice, d):
    """The ReadRes of a returned Read (mapped), or of an unfinished one (the search's choice)."""
    if choice is None:
        return m.res
    code = choice["code"]
    if code == 0:
        return M.R_BYTES(d.bytes[:choice.get("k", 0)])
    if code == M.EOF_CODE:
        return M.R_EOF
    return M.R_ERR(M.CODE_ERR[code])


def _read_after(st, d, n, r, cut):
    """The direction after a Read with result r (concrete choice): (d', keep)."""
    if st.closed or n == 0:
        return d, None
    if cut:
        dc = M.NetDir(d.bytes, M.CUT)
        if r[0] == "bytes":
            return M.NetDir(d.bytes[len(r[1]):], M.CUT), len(d.bytes)
        if r == M.R_ERR(M.SYS):
            return M.NetDir(b"", M.CUT), 0
        return dc, len(d.bytes)
    if r[0] == "bytes":
        return d._replace(bytes=d.bytes[len(r[1]):]), None
    if r == M.R_EOF:
        if d.bytes == b"" and d.status != M.OPEN:
            return d, None
        return M.NetDir(b"", M.CUT), 0
    if r == M.R_ERR(M.SYS):
        if d.status == M.CUT and d.bytes == b"":
            return d, None
        return M.NetDir(b"", M.CUT), 0
    return d, None  # timeout


def _write_after(est, d, rs, k, res):
    """The direction after a Write step (WriteOutcome's d', as its result determines it)."""
    if est.closed or d.status != M.OPEN:
        return d
    if res is None:
        return d._replace(bytes=d.bytes + rs[:k])
    if res == M.SYS:
        return d._replace(status=M.CUT)
    return d


def _replay(ck, ents, token_of, used, marks):
    conns = {}
    local = {ch.name: M.NetLocal({}) for ch in ck.chains}
    conn_num = {}
    token_conn = {}
    lis_num = {}
    next_conn = 1
    next_lid = {ch.name: 1 for ch in ck.chains}
    cut_point = {}   # (conn, side of the writer) -> entry index of the direction's reader's last cut point
    wprog = {}       # (component, op) -> the bytes a Write call's steps have taken so far
    wpart = {}       # (component, op) -> the number of its steps so far
    steps = []
    G0 = M.NetGlobal({})

    def one(c, cn):
        return M.NetGlobal({c: cn})

    def fail(x, what):
        raise ReplayError(f"witness step {len(steps)} ({what}) is not a step of model.py")

    for x, (tau, (kind, cp, i, ch)) in enumerate(ents):
        if kind == "crash":
            chain, idx = cp, i
            L = local[chain.name]
            L2 = M.NetLocal({})
            if not M.crash(L, L2):
                fail(x, "crash")
            local[chain.name] = L2
            steps.append({"op": "Crash", "node": chain.name, "t": tau[0],
                          "between": [chain.procs[idx].pid, chain.procs[idx + 1].pid]})
            continue
        c = cp.calls[i]
        item = cp.items[i]
        choice = ch
        m = ck.mapped.get(id(c))
        pending = c.e is None
        st = {"op": None, "t": tau[0], "trace": {"pid": c.proc.pid, "s": c.s}}
        if pending:
            st["pending"] = True
        if cp.kind == "addr":
            node = item["node"]
            L = local[node]
            if c.op == "Listen":
                a = ck.listen_addr[id(c)]
                if m.res[0] == "ok":
                    lid = next_lid[node]
                    next_lid[node] += 1
                    L2 = M.NetLocal({**L.lis, lid: (a, True)})
                    e2 = (lid, 0)
                    lis_num[(c.proc.pid, m.res[1]["id"])] = (node, lid)
                else:
                    L2, e2 = L, M.fail_v(M.SYS)
                if not M.net_step("Listen", a, L, G0, e2, L2, G0):
                    fail(x, f"Listen {a}")
                local[node] = L2
                st.update(op="Listen", node=node, addr=a.decode(),
                          res={"code": e2[1], **({"lis": e2[0]} if e2[1] == 0 else {})})
            elif c.op == "Accept":
                lnode, lid = lis_num[(c.proc.pid, c.id)]
                if m.res[0] == "ok":
                    ckey = ck.accept_conn.get(id(c))
                    if ckey is not None:
                        cnum = conn_num[ckey]
                    else:
                        cnum = token_conn[token_of[x]]
                        conn_num[("A", c.proc.pid, m.res[1]["id"])] = cnum
                    cn = conns[cnum]
                    cn2 = cn._replace(accepted=True)
                    e2 = (M.end_id(cnum, True), 0)
                    if not M.net_step("Accept", lid, L, one(cnum, cn), e2, L, one(cnum, cn2)):
                        fail(x, f"Accept of conn {cnum}")
                    conns[cnum] = cn2
                    st.update(op="Accept", node=node, lis=lid, res={"code": 0, "conn": cnum, "end": e2[0]})
                else:
                    e2 = M.fail_v(m.res[1])
                    if not M.net_step("Accept", lid, L, G0, e2, L, G0):
                        fail(x, "Accept failure")
                    st.update(op="Accept", node=node, lis=lid, res={"code": e2[1]})
            elif c.op == "ListenerClose":
                lnode, lid = lis_num[(c.proc.pid, c.id)]
                res = None if pending else m.res
                a, o = L.lis[lid]
                L2 = M.NetLocal({**L.lis, lid: (a, False)})
                e2 = M.err_code(res)
                if not M.net_step("LisClose", lid, L, G0, e2, L2, G0):
                    fail(x, "LisClose")
                local[node] = L2
                st.update(op="LisClose", node=node, lis=lid, res={"code": e2})
            else:  # Dial, DialTimeout
                a = c.b.get("addr", "").encode()
                if not pending and m.res[0] == "ok":
                    cnum = next_conn
                    next_conn += 1
                    conn_num[("D", c.proc.pid, m.res[1]["id"])] = cnum
                    cn = M.conn_fresh(a)
                    e2 = (M.end_id(cnum, False), 0)
                    if cnum in conns or not M.net_step("Dial", a, L, G0, e2, L, one(cnum, cn)):
                        fail(x, "Dial")
                    conns[cnum] = cn
                    st.update(op="Dial", node=node, addr=a.decode(), res={"code": 0, "conn": cnum, "end": e2[0]})
                elif x in used:
                    cnum = next_conn
                    next_conn += 1
                    token_conn[x] = cnum
                    if pending:  # it succeeded, and its process ended before it returned
                        cn = M.conn_fresh(a)
                        e2 = (M.end_id(cnum, False), 0)
                        res = {"code": 0, "conn": cnum, "end": e2[0]}
                    else:        # D16: it failed, and left its connection, abandoned
                        cn = M.conn_abandoned(a)
                        e2 = M.fail_v(M.SYS)
                        res = {"code": e2[1], "abandoned": cnum}
                    if cnum in conns or not M.net_step("Dial", a, L, G0, e2, L, one(cnum, cn)):
                        fail(x, "Dial (a connection left for an Accept)")
                    conns[cnum] = cn
                    st.update(op="Dial", node=node, addr=a.decode(), res=res)
                elif pending:
                    continue  # unfinished, and no Accept needed it: left out
                else:
                    e2 = M.fail_v(M.SYS)
                    if not M.net_step("Dial", a, L, G0, e2, L, G0):
                        fail(x, "Dial failure")
                    st.update(op="Dial", node=node, addr=a.decode(), res={"code": e2[1]})
            steps.append(st)
            continue
        # a connection's operation
        cnum = conn_num[cp.key]
        side = item["side"]
        s = side == 1
        e = M.end_id(cnum, s)
        cn = conns[cnum]
        node = ck.chain_of[c.proc.pid][0].name
        L = local[node]
        est = M.end_st(cn, s)
        st.update(node=node, conn=cnum, side=side, end=e)
        if c.op == "Read":
            n = c.b.get("n", 0)
            d = M.out(cn, not s)
            r = _read_result(m, choice, d)
            d2, keep = _read_after(est, d, n, r, x in marks)
            if not est.closed and n > 0:
                cut_point[(cnum, not s)] = x
            cn2 = M.set_out(cn, not s, d2)
            if not M.net_step("Read", (e, n), L, one(cnum, cn), r, L, one(cnum, cn2), keep):
                fail(x, f"Read {r[0]}")
            conns[cnum] = cn2
            res = {"code": 0 if r[0] == "bytes" else (M.EOF_CODE if r == M.R_EOF else M.ERR_CODE[r[1]])}
            if r[0] == "bytes":
                res["k"] = len(r[1])
                res["data"] = r[1].hex()
            st.update(op="Read", n=n, res=res, cut=None if keep is None else {"keep": keep})
        elif c.op == "Write":
            # one or more steps of the call's loop (poll.FD.Write): progress {"k"}, a failure
            # {"fail"}, or, for a call cut short, its steps {"steps": [...]}
            data = cp.W[item["w"]]
            subs = choice["steps"] if "steps" in choice else [choice]
            for sub in subs:
                p = wprog.get((id(cp), i), 0)
                rs = data[p:]
                if "k" in sub:
                    k, res = sub["k"], None
                else:
                    k, res = 0, M.CODE_ERR[sub["fail"]]
                cn = conns[cnum]
                est = M.end_st(cn, s)
                d = M.out(cn, s)
                d2 = _write_after(est, d, rs, k, res)
                if not M.write_outcome(est, d, rs, k, res, d2):
                    if not est.closed and d.status != M.CUT:
                        # a step only a cut direction allows: cut at the reader's last Read
                        y = cut_point.get((cnum, s))
                        if y is None or y in marks:
                            raise ReplayError(f"witness step {len(steps)}: a Write step needs its direction "
                                              "cut and no Read of it can have cut it")
                        marks.add(y)
                        raise _Restart()
                    fail(x, f"Write step ({k}, {res})")
                first = wpart.get((id(cp), i), 0) == 0
                if M.lock(cn, s) == first:
                    fail(x, "Write step: the end's write lock is " +
                         ("held by another Write (D25)" if first else "not held by this Write"))
                cn2 = M.set_lock(M.set_out(cn, s, d2), s, not M.write_last(rs, k, res))
                if not M.net_step("Write", (e, rs, first), L, one(cnum, cn), (k, M.err_code(res)), L,
                                  one(cnum, cn2)):
                    fail(x, f"Write step ({k}, {res})")
                conns[cnum] = cn2
                wprog[(id(cp), i)] = p + k
                sst = dict(st)
                sst.update(op="Write", data=rs.hex(), res={"k": k, "code": M.err_code(res)},
                           part=wpart.get((id(cp), i), 0),
                           last=(res is not None or p + k == len(data)))
                wpart[(id(cp), i)] = sst["part"] + 1
                steps.append(sst)
            continue
        elif c.op in ("Close", "CloseWrite"):
            res = (None if choice["code"] == 0 else M.CODE_ERR[choice["code"]]) if choice is not None else m.res
            d = M.out(cn, s)
            if est.closed:
                cn2 = cn
            elif c.op == "Close":
                cn2 = M.set_out(M.set_end(cn, s, est._replace(closed=True)), s, M.shut(d))
            else:
                cn2 = M.set_out(cn, s, M.shut(d) if res is None else d)
            if not M.net_step(c.op, e, L, one(cnum, cn), M.err_code(res), L, one(cnum, cn2)):
                fail(x, f"{c.op} ({res})")
            conns[cnum] = cn2
            st.update(op=c.op, res={"code": M.err_code(res)})
        else:  # SetDeadline
            res = (None if choice["code"] == 0 else M.CODE_ERR[choice["code"]]) if choice is not None else m.res
            kind, set_ = item["dkind"], item["set"]
            wall, ext = (1, 0) if set_ else (0, 0)
            if est.closed:
                cn2 = cn
            else:
                cn2 = M.set_end(cn, s, est._replace(rdl=est.rdl if kind == 2 else set_,
                                                     wdl=est.wdl if kind == 1 else set_))
            if not M.net_step("SetDeadline", (e, kind, wall, ext), L, one(cnum, cn), M.err_code(res), L,
                              one(cnum, cn2)):
                fail(x, "SetDeadline")
            conns[cnum] = cn2
            st.update(op="SetDeadline", kind=kind, set=set_, wall=wall, ext=ext, res={"code": M.err_code(res)})
        steps.append(st)
    for i, stp in enumerate(steps):
        stp["i"] = i
    return {
        "format": FORMAT, "version": VERSION, "run": ck.run.name,
        "nodes": [{"node": ch.name, "host": ch.host.decode(), "procs": [p.pid for p in ch.procs]}
                  for ch in ck.chains],
        "conns": next_conn - 1,
        "retro_cuts": len(marks),
        "steps": steps,
    }
