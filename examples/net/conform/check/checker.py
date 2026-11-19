"""The conformance checker: does some execution of the net extension's semantics (Impl.lean,
transcribed in model.py) produce a traced run? README.md has the design; in short:

1. Load the run (trace.py): its node processes, and its drivers' process events.
2. Nodes: a node is its `node` name; its processes, in time order, are its incarnations, a crash
   (D10, D11) between each and the next (processes of one name that overlap in time are distinct
   nodes with the same host).
3. Map each call's result to the extension's (mapping.py, by net.lean), checking the shape rules;
   flag what the model has no step for (scope).
4. The plan (D13): given (`plan=`), or inferred from the run's Listen and Dial addresses, each
   address at the host of the node that listens there; checked well formed (D20).
5. Pair the two ends of each connection by their address 4-tuples.
6. Split the run into independent components: one per plan address (its listeners, Accepts, the
   listeners' Closes, the Dials of it, the crashes of its host) and one per connection (the
   operations on its two ends); search each for a linearization (lincheck.py) through the lazy
   model (lazy.py).
7. Merge the components' linearizations into one, and replay it through model.py's literal
   relations (replay.py): the witness.
"""

import collections
import time

import lazy as Z
import lincheck
import mapping as G
import model as M
import trace as T

IN_MODEL = {"Dial", "DialTimeout", "Listen", "Accept", "ListenerClose", "Read", "Write", "Close",
            "CloseWrite", "SetDeadline"}
ADDR_QUERIES = {"ListenerAddr", "LocalAddr", "RemoteAddr"}
HARD = ("not-admitted", "shape", "clock", "internal")
KIND_OF_WHICH = {"both": 0, "read": 1, "write": 2}


class Finding:
    def __init__(self, kind, where, what, context=None, t=0, op=None):
        self.kind, self.where, self.what = kind, where, what
        self.context, self.t, self.op = context or [], t, op

    def as_dict(self):
        return {"kind": self.kind, "where": self.where, "what": self.what, "context": self.context}


def _show(b, k=24):
    if len(b) <= k:
        return repr(b)
    return repr(b[:k])[:-1] + f"...'(+{len(b) - k})"


def describe(c):
    b, e = c.b, c.e
    s = f"{c.where()} g{c.g} {c.op}"
    if c.id:
        s += f" {c.id}"
    if c.op == "Read":
        s += f" buf={b.get('n')}"
    elif c.op == "Write":
        s += f" {b.get('n')} bytes {_show(bytes.fromhex(b.get('data', '')))}"
    elif c.op == "SetDeadline":
        s += f" {b.get('which')} set={b.get('set')}"
    elif c.op in ("Dial", "DialTimeout", "Listen"):
        s += f"({b.get('net')}, {b.get('addr')})"
    elif c.op == "Unmodeled":
        s += f" {b.get('api')}"
    if e is None:
        return s + f" [{b['t']}, -] (never returned)"
    s += f" [{b['t']}, {e['t']}] ->"
    if c.op == "Read":
        s += f" n={e.get('n')} {_show(bytes.fromhex(e.get('data', '')))}"
    elif c.op == "Write":
        s += f" n={e.get('n')}"
    new = e.get("new")
    if isinstance(new, dict):
        s += f" {new.get('id')} {(new.get('local') or {}).get('s')}->{(new.get('remote') or {}).get('s')}"
    if "err" in e:
        err = e["err"]
        if err is None:
            s += " nil"
        else:
            s += f" err {err.get('msg')!r} ({err.get('inner') or err.get('type')})"
    elif "addr" in e:
        s += f" {e['addr']}"
    return s


def show_conn_state(st, W):
    def d(x, name):
        segs, ln, stat, a = x
        return f"{name} {stat} {ln} unread {_show(Z.seg_bytes(Z.seg_take(segs, 16), W), 16)}" + \
            ("" if a is None else f" (a={a})")
    def e(x, name):
        return f"{name} closed={x.closed} rdl={x.rdl} wdl={x.wdl}"
    parts = [e(st[0], "dialer end"), e(st[1], "acceptor end"), d(st[2], "up (dialer->acceptor)"),
             d(st[3], "down (acceptor->dialer)")]
    if st[4]:
        parts.append("Writes in progress (op, bytes so far): " + ", ".join(f"{j}:{p}" for j, p, _ in sorted(st[4])))
    return "; ".join(parts)


def show_addr_state(st):
    open_, pend, tok = st
    return (f"open listeners {sorted(f'{n}:{l}' for n, l in open_)}; pending connections "
            f"{len(pend)}; pending connections no Dial returned: {tok}")


class Chain:
    """A node: a sequence of processes (incarnations), a crash between each and the next."""

    def __init__(self, name, host):
        self.name, self.host, self.procs = name, host, []


class Comp:
    def __init__(self, kind, key, init):
        self.kind, self.key, self.init = kind, key, init
        self.ops = []        # lincheck.Op
        self.calls = []      # the trace call of each op (None for a crash)
        self.items = []      # what each op is, for the witness: dicts
        self.W = []          # a connection's write data
        self.tainted = []    # reasons this component is out of scope
        self.result = None


class Checker:
    def __init__(self, run, plan=None, limit=5_000_000, replay=True):
        self.run, self.given_plan, self.limit, self.do_replay = run, plan, limit, replay
        self.findings = []
        self.notes = []
        self.stats = collections.Counter()
        self.witness = None

    def find(self, kind, c, what, context=None):
        where = c.where() if c is not None else "-"
        t = (c.ret or c.call) if c is not None else 0
        self.findings.append(Finding(kind, where, what, context or ([describe(c)] if c is not None else []), t, c))

    # -----------------------------------------------------------------------------------------
    def check(self):
        t0 = time.monotonic()
        run = self.run
        if not run.procs:
            return self.result("NO TRACES", t0)
        self.clock_checks()
        self.make_chains()
        self.classify()
        self.make_plan()
        self.resolve_listeners()
        self.pair()
        self.build_components()
        self.search_all()
        verdict = self.verdict()
        if verdict in ("ADMITTED", "OUT OF SCOPE") and self.do_replay and self.all_comps_ok():
            import replay
            try:
                self.witness = replay.build(self)
            except replay.ReplayError as ex:
                self.findings.append(Finding("internal", "-", f"the witness does not replay through "
                                             f"model.py: {ex} (a checker bug)"))
                verdict = self.verdict()
        return self.result(verdict, t0)

    def all_comps_ok(self):
        return all(cp.result is not None and cp.result.ok for cp in self.comps)

    def verdict(self):
        kinds = {f.kind for f in self.findings}
        if kinds & set(HARD):
            return "NOT ADMITTED"
        if kinds & {"scope", "inconclusive"}:
            return "OUT OF SCOPE"
        return "ADMITTED"

    def result(self, verdict, t0):
        return {"run": self.run.name, "verdict": verdict, "findings": self.findings,
                "notes": self.notes, "stats": self.stats, "seconds": time.monotonic() - t0,
                "witness": self.witness}

    # -----------------------------------------------------------------------------------------
    def clock_checks(self):
        run = self.run
        tns = {p.header.get("timens") for p in run.procs + run.drivers}
        if len(tns) > 1:
            self.findings.append(Finding("clock", "-", f"processes in {len(tns)} time namespaces: "
                                         "their monotonic times are not comparable"))
        offs = []
        for p in run.procs + run.drivers:
            h = p.header
            if "wall" in h and "t0" in h and "t1" in h:
                offs.append(h["wall"] - (h["t0"] + h["t1"]) / 2)
        if len(offs) > 1:
            self.notes.append(f"wall-minus-monotonic offsets spread over {(max(offs) - min(offs)) / 1e3:.1f} us "
                              f"across {len(offs)} processes")
        for p in run.procs:
            if p.truncated:
                self.notes.append(f"{p.tag}: its last line was cut short (killed mid-write)")
            ex = run.pevents.get(p.pid, {}).get("exit")
            if ex is not None:
                for c in p.calls:
                    for t in (c.call, c.ret):
                        if t is not None and t > ex["t"]:
                            self.find("clock", c, f"a record at {t}, after its process's exit event at "
                                      f"{ex['t']} (the process had ended: no call of it can step after)")
                            break

    def make_chains(self):
        run = self.run
        self.chains = []
        self.chain_of = {}   # pid -> (chain, index)
        bynode = collections.defaultdict(list)
        for p in run.procs:
            bynode[p.node].append(p)
        for node, ps in bynode.items():
            chains = []
            for p in ps:
                start = p.header.get("t0", p.first_t)
                placed = None
                for ch in chains:
                    q = ch.procs[-1]
                    ex = run.pevents.get(q.pid, {}).get("exit")
                    end = ex["t"] if ex is not None else (q.last_t if q.last_t is not None else q.header.get("t1"))
                    if end is not None and end < start:
                        placed = ch
                        break
                if placed is None:
                    name = node if not chains else f"{node}#{len(chains) + 1}"
                    placed = Chain(name, node.encode())
                    chains.append(placed)
                    self.chains.append(placed)
                placed.procs.append(p)
            if len(chains) > 1:
                self.notes.append(f"node {node!r}: processes overlapping in time, taken as {len(chains)} "
                                  "nodes with the same host")
        for ch in self.chains:
            for i, p in enumerate(ch.procs):
                self.chain_of[p.pid] = (ch, i)
        # death bounds: the latest time a process's calls can take effect
        self.death = {}
        for ch in self.chains:
            for i, p in enumerate(ch.procs):
                ex = run.pevents.get(p.pid, {}).get("exit")
                if ex is not None:
                    self.death[p.pid] = ex["t"]
                elif i + 1 < len(ch.procs):
                    self.death[p.pid] = ch.procs[i + 1].header["t0"] - 1
                else:
                    self.death[p.pid] = None
        self.stats["nodes"] = len(self.chains)
        self.stats["processes"] = len(run.procs)
        self.stats["crashes (a process followed by another of its node)"] = sum(len(ch.procs) - 1 for ch in self.chains)

    # -----------------------------------------------------------------------------------------
    def classify(self):
        """Which calls are in the model, their mapped results, the scope and shape findings."""
        self.calls = []
        self.mapped = {}
        self.out_sockets = set()   # sockets made by an out-of-scope call: their operations too
        self.taint = collections.defaultdict(list)   # socket -> reasons
        for p in self.run.procs:
            for c in p.calls:
                self.calls.append(c)
        self.calls.sort(key=lambda c: (c.call, c.proc.pid, c.s))
        for c in self.calls:
            self.stats[f"calls {c.op}" + ("" if c.e is not None else " (never returned)")] += 1
            if c.op == "Unmodeled":
                api = c.b.get("api")
                self.find("scope", c, f"{api}: not in the model (no step)")
                if c.id is not None and c.id != "nil" and not c.id.startswith("u"):
                    self.taint[c.sock()].append(f"{api} at {c.where()}")
                new = c.new()
                if isinstance(new, dict) and new.get("id"):
                    self.out_sockets.add((c.proc.pid, new["id"]))
                    self.taint[(c.proc.pid, new["id"])].append(f"made by {api} at {c.where()}")
                continue
            if c.id is not None and (c.id == "nil" or c.id.startswith("u")):
                self.find("scope", c, f"{c.op} on {'a nil or zero-value socket' if c.id == 'nil' else 'a socket no traced call made'}"
                          " (no step: the model's ids name only sockets it made)")
                continue
            if c.sock() in self.out_sockets:
                self.find("scope", c, f"{c.op} on a socket an out-of-scope call made")
                continue
            if c.op in ("Dial", "DialTimeout", "Listen") and c.b.get("net") != "tcp":
                self.find("scope", c, f"network {c.b.get('net')!r} (net.lean: \"tcp\" only, else a panic)")
                new = c.new()
                if isinstance(new, dict) and new.get("id"):
                    self.out_sockets.add((c.proc.pid, new["id"]))
                continue
            if c.op not in IN_MODEL and c.op not in ADDR_QUERIES:
                self.find("scope", c, f"unknown operation {c.op}")
                continue
            if c.e is None:
                continue
            if c.op in ADDR_QUERIES:
                a = c.e.get("addr")
                if not G.net_addr_ok(a):
                    self.find("shape", c, f"{c.op} returned {a} (net.lean, D18: a non-nil *TCPAddr)")
                continue
            m = G.map_call(c)
            self.mapped[id(c)] = m
            for pr in m.problems:
                self.find("shape", c, pr)
        # D18: the addresses are fixed at the socket's creation. The model's TCPAddr.String is
        # arbitrary (AnyString), so a changed string does not refute it: a warning only.
        made = {}
        for c in self.calls:
            new = c.new()
            if isinstance(new, dict) and new.get("id") and c.e.get("err") is None:
                made[(c.proc.pid, new["id"])] = new
        for c in self.calls:
            if c.op in ADDR_QUERIES and c.e is not None and c.sock() in made:
                new = made[c.sock()]
                want = new.get("remote" if c.op == "RemoteAddr" else "local")
                a = c.e.get("addr")
                if isinstance(want, dict) and isinstance(a, dict) and want.get("s") != a.get("s"):
                    self.findings.append(Finding("warning", c.where(), f"{c.op} {a.get('s')}, the socket was "
                                                 f"made with {want.get('s')} (net.lean's String is arbitrary: "
                                                 "not a refutation)", [describe(c)]))

    # -----------------------------------------------------------------------------------------
    def make_plan(self):
        """The plan: given, or inferred (README.md, "The plan")."""
        self.lenient = {}   # id(Listen call) -> the address it is checked as listening at
        if self.given_plan is not None:
            plan = {a.encode() if isinstance(a, str) else a: (h.encode() if isinstance(h, str) else h)
                    for a, h in self.given_plan}
        else:
            plan = {}
            wild = []
            for c in self.calls:
                if c.op != "Listen" or c.b.get("net") != "tcp" or c.sock() in self.out_sockets:
                    continue
                a = c.b.get("addr", "").encode()
                host = self.chain_of[c.proc.pid][0].host
                if M.wild_port(a) is not None:
                    wild.append((c, a, host))
                    continue
                if M.parse_addr(a) is None:
                    continue  # not a canonical a.b.c.d:p: no plan has it (D13, D20); its Listen is stuck
                if M.port_of(a) == b"0":
                    ok = c.e is not None and c.e.get("err") is None and isinstance(c.e.get("new"), dict)
                    if not ok:
                        continue
                    port = (c.e["new"].get("local") or {}).get("s", "").rsplit(":", 1)[-1].encode()
                    a = a[:-1] + port
                    self.lenient[id(c)] = a
                self._plan_host(plan, a, host, c)
            for c in self.calls:
                if c.op in ("Dial", "DialTimeout") and c.b.get("net") == "tcp":
                    a = c.b.get("addr", "").encode()
                    if M.parse_addr(a) is not None:  # else no plan has it: the Dial is stuck
                        plan.setdefault(a, None)
            for c, a, host in wild:
                p = M.wild_port(a)
                if p == b"0":
                    ok = c.e is not None and c.e.get("err") is None and isinstance(c.e.get("new"), dict)
                    if not ok:
                        continue
                    p = (c.e["new"].get("local") or {}).get("s", "").rsplit(":", 1)[-1].encode()
                cands = [x for x in plan if M.port_of(x) == p]
                if len(cands) == 1:
                    a0 = cands[0]
                elif not cands:
                    a0 = b"127.0.0.1:" + p
                    self.notes.append(f"wildcard Listen {a.decode()} at {c.where()}: no address with its port "
                                      f"in the run; the plan is given {a0.decode()} for it")
                else:
                    continue  # ListenAt has no address: the Listen is out of scope (below)
                if M.wild_port(a) == b"0":
                    self.lenient[id(c)] = a0
                self._plan_host(plan, a0, host, c)
            for a in list(plan):
                if plan[a] is None:
                    plan[a] = b"-"  # dialed, never listened at: any host (none of the run's nodes)
        self.plan = plan
        self.plan_list = sorted(plan.items())
        if not M.plan_well_formed(self.plan_list):
            bad = [a.decode() for a, _ in self.plan_list if not M.addr_ok(a)]
            self.findings.append(Finding("scope", "-", f"the plan is not well formed (D20, Deploy.lean's "
                                         f"PlanWellFormed): {', '.join(bad[:6])}{' ...' if len(bad) > 6 else ''}"
                                         " (port 0, ephemeral ports or not canonical); checked under it all the same"))
        if self.lenient:
            self.findings.append(Finding("scope", "-", f"{len(self.lenient)} Listen(s) of port 0 (D12: not "
                                         "modeled); each checked as a Listen of the address the kernel gave it"))
        self.stats["plan addresses"] = len(plan)

    def _plan_host(self, plan, a, host, c):
        h = plan.get(a)
        if h is not None and h != host:
            self.find("scope", c, f"{a.decode()} is listened at by nodes {h.decode()!r} and {host.decode()!r}: "
                      "a plan gives an address one host (ListenAt)")
            return
        plan[a] = host

    def resolve_listeners(self):
        self.lis_addr = {}   # listener socket -> a0
        self.listen_a0 = {}  # id(Listen call) -> a0
        for c in self.calls:
            if c.op != "Listen" or c.b.get("net") != "tcp" or c.e is None or id(c) not in self.mapped:
                continue
            ch = self.chain_of[c.proc.pid][0]
            a = self.lenient.get(id(c), c.b.get("addr", "").encode())
            a0 = M.listen_resolve(self.plan, ch.host, a)
            if a0 is None:
                self.find("scope", c, f"ListenAt has no plan address for {a.decode()} at host "
                          f"{ch.host.decode()!r}: the model's Listen is stuck")
                new = c.new()
                if isinstance(new, dict) and new.get("id"):
                    self.out_sockets.add((c.proc.pid, new["id"]))
                continue
            self.listen_a0[id(c)] = a0
            m = self.mapped[id(c)]
            if m.res and m.res[0] == "ok":
                self.lis_addr[(c.proc.pid, m.res[1]["id"])] = a0
        self.out_dials = set()  # ids of Dial calls out of scope: their connections are projected out
        for c in self.calls:
            if c.op == "Dial" or c.op == "DialTimeout":
                if c.b.get("net") == "tcp" and self.plan.get(c.b.get("addr", "").encode()) is None:
                    self.find("scope", c, f"Dial of {c.b.get('addr')}, not a plan address (DialStep is stuck)")
                    self.out_dials.add(id(c))

    # -----------------------------------------------------------------------------------------
    def pair(self):
        """The two ends of each connection, by 4-tuple: a Dial's (local, remote) is an Accept's
        (remote, local). A 4-tuple may name several connections in turn (an ephemeral port
        reused): each Accept, in the order they returned, takes the latest Dial of its 4-tuple
        called before it returned and not taken yet."""
        self.end_conn = {}    # end socket -> (conn key, side)
        self.out_conns = set()  # connections an out-of-scope Dial made
        self.accept_conn = {}  # id(Accept call) -> conn key (None: no Dial returned it)
        dials = collections.defaultdict(list)
        for c in self.calls:
            if c.op in ("Dial", "DialTimeout") and id(c) in self.mapped:
                m = self.mapped[id(c)]
                if m.res and m.res[0] == "ok":
                    new = m.res[1]
                    ck = ("D", c.proc.pid, new["id"])
                    self.end_conn[(c.proc.pid, new["id"])] = (ck, 0)
                    if id(c) in self.out_dials:
                        self.out_conns.add(ck)
                    key = ((new.get("local") or {}).get("s"), (new.get("remote") or {}).get("s"))
                    dials[key].append(c)
        accs = []
        for c in self.calls:
            if c.op == "Accept" and id(c) in self.mapped and c.sock() in self.lis_addr:
                m = self.mapped[id(c)]
                if m.res and m.res[0] == "ok":
                    accs.append(c)
        accs.sort(key=lambda c: c.ret)
        used = set()
        reused = 0
        for a in accs:
            new = self.mapped[id(a)].res[1]
            key = ((new.get("remote") or {}).get("s"), (new.get("local") or {}).get("s"))
            ds = dials.get(key, [])
            if len(ds) > 1:
                reused += 1
            cands = [d for d in ds if id(d) not in used and d.call < a.ret]
            end = (a.proc.pid, new["id"])
            if cands:
                d = max(cands, key=lambda d: d.call)
                used.add(id(d))
                ck = ("D", d.proc.pid, self.mapped[id(d)].res[1]["id"])
                self.stats["connections paired"] += 1
            else:
                late = [d for d in ds if id(d) not in used]
                if late:
                    self.notes.append(f"{a.where()}: the Dials of its 4-tuple began after it returned: "
                                      f"taken as a connection no Dial returned")
                ck = ("A", a.proc.pid, new["id"])
                self.stats["connections accepted that no Dial returned"] += 1
            self.end_conn[end] = (ck, 1)
            self.accept_conn[id(a)] = ck if ck[0] == "D" else None
        self.stats["connections dialed, never accepted"] = sum(1 for ds in dials.values() for d in ds if id(d) not in used)
        if reused:
            self.stats["Accepts whose 4-tuple several Dials had"] = reused

    # -----------------------------------------------------------------------------------------
    def build_components(self):
        self.comps = []
        conn = {}
        addr = {}

        def comp_c(ck):
            if ck not in conn:
                cp = Comp("conn", ck, Z.CONN_ABANDONED if ck[0] == "A" else Z.CONN_FRESH)
                conn[ck] = cp
                self.comps.append(cp)
            return conn[ck]

        def comp_a(a0):
            if a0 not in addr:
                cp = Comp("addr", a0, Z.ADDR0)
                addr[a0] = cp
                self.comps.append(cp)
            return addr[a0]

        for (pid, sid), why in self.taint.items():
            if (pid, sid) in self.end_conn:
                comp_c(self.end_conn[(pid, sid)][0]).tainted.extend(why)
            if (pid, sid) in self.lis_addr:
                comp_a(self.lis_addr[(pid, sid)]).tainted.extend(why)

        for c in self.calls:
            if id(c) not in self.mapped and c.e is not None:
                continue
            if c.op in G.CONN_OPS:
                if c.sock() not in self.end_conn:
                    if c.sock() not in self.out_sockets:
                        self.find("scope", c, f"{c.op} on a socket no in-scope Dial or Accept returned")
                    else:
                        self.find("scope", c, f"{c.op} on a socket an out-of-scope call made")
                    continue
                ck, side = self.end_conn[c.sock()]
                if ck in self.out_conns:
                    self.find("scope", c, f"{c.op} on a connection an out-of-scope Dial made")
                    continue
                self.add_conn_op(comp_c(ck), c, side)
            elif c.op in ("Accept", "ListenerClose"):
                if c.sock() not in self.lis_addr:
                    if c.sock() not in self.out_sockets:
                        self.find("scope", c, f"{c.op} on a listener no in-scope Listen returned")
                    elif c.op == "Accept":
                        self.find("scope", c, "Accept on a listener whose Listen is out of scope")
                    new = c.new()
                    if isinstance(new, dict) and new.get("id"):
                        self.out_sockets.add((c.proc.pid, new["id"]))
                    continue
                if c.op == "Accept" and self.accept_conn.get(id(c)) in self.out_conns:
                    self.find("scope", c, "Accept of a connection an out-of-scope Dial made (left out: "
                              "it changes nothing the in-scope operations see)")
                    continue
                self.add_addr_op(comp_a(self.lis_addr[c.sock()]), c)
            elif c.op == "Listen":
                if id(c) in self.listen_a0:
                    self.add_addr_op(comp_a(self.listen_a0[id(c)]), c)
            elif c.op in ("Dial", "DialTimeout"):
                a = c.b.get("addr", "").encode()
                if c.b.get("net") == "tcp" and self.plan.get(a) is not None:
                    self.add_addr_op(comp_a(a), c)
        # crashes, in the address components of their node's host
        for cp in list(addr.values()):
            host = self.plan.get(cp.key)
            for ch in self.chains:
                if ch.host != host:
                    continue
                for i in range(len(ch.procs) - 1):
                    p, q = ch.procs[i], ch.procs[i + 1]
                    mine = [j for j, x in enumerate(cp.calls) if x is not None and x.proc is p]
                    later = [j for j, x in enumerate(cp.calls) if x is not None and x.proc.pid in
                             {r.pid for r in ch.procs[i + 1:]}]
                    if not mine and not later:
                        continue
                    # the crash: after every operation of p (preds), before every operation of
                    # the node's later processes (each gets the crash as a pred); its interval,
                    # from p's death to q's start, for real time with the other nodes
                    call = self.death[p.pid] + 1
                    ret = max(call, q.header["t0"])
                    preds = 0
                    for j in mine:
                        preds |= 1 << j
                    node = ch.name
                    desc = f"crash of node {node} (between {p.tag} and {q.tag}) [{call}, {ret}]"
                    k = len(cp.ops)
                    cp.ops.append(lincheck.Op(call, ret, lambda st, dn, node=node: Z.crash(st, node), desc,
                                              preds=preds))
                    cp.calls.append(None)
                    cp.items.append({"kind": "crash", "chain": ch, "index": i})
                    for j in later:
                        cp.ops[j].preds |= 1 << k
        self.stats["components: addresses"] = len(addr)
        self.stats["components: connections"] = len(conn)

    def _deadline(self, c):
        return self.death.get(c.proc.pid)

    def _bad_step(self, c):
        m = self.mapped[id(c)]
        why = "; ".join(m.problems) or "no extension result gives this Go value"
        return lambda st, dn: ([], f"net.lean cannot return this value: {why}")

    def add_conn_op(self, cp, c, side):
        j = len(cp.ops)
        pending = c.e is None
        b = c.b
        item = {"kind": "conn", "op": c.op, "side": side}
        if not pending and self.mapped[id(c)].bad:
            step = self._bad_step(c)
        elif c.op == "Read":
            n = b.get("n", 0)
            if pending:
                step = self._pending_read(cp, c, side, n)
            else:
                r = self.mapped[id(c)].res
                step = lambda st, dn, s=side, n=n, r=r, W=cp.W: Z.read(st, s, n, r, W)
        elif c.op == "Write":
            data = bytes.fromhex(b.get("data", ""))
            w = len(cp.W)
            cp.W.append(data)
            item["w"] = w
            if pending:
                step = lambda st, dn, s=side, j=j, w=w, L=len(data): Z.write_pending(st, s, j, w, L, dn)
            else:
                k, res = self.mapped[id(c)].res
                step = (lambda st, dn, s=side, j=j, w=w, L=len(data), k=k, res=res:
                        Z.write(st, s, j, w, L, k, res, dn))
        elif c.op == "Close":
            if pending:
                step = lambda st, dn, s=side: Z.close_pending(st, s)
            else:
                res = self.mapped[id(c)].res
                step = lambda st, dn, s=side, res=res: Z.close(st, s, res)
        elif c.op == "CloseWrite":
            if pending:
                step = lambda st, dn, s=side: Z.close_write_pending(st, s)
            else:
                res = self.mapped[id(c)].res
                step = lambda st, dn, s=side, res=res: Z.close_write(st, s, res)
        else:  # SetDeadline
            kind = KIND_OF_WHICH.get(b.get("which"), 0)
            set_ = bool(b.get("set"))
            item["dkind"], item["set"] = kind, set_
            if pending:
                step = lambda st, dn, s=side, k=kind, z=set_: Z.deadline_pending(st, s, k, z)
            else:
                res = self.mapped[id(c)].res
                step = lambda st, dn, s=side, k=kind, z=set_, res=res: Z.deadline(st, s, k, z, res)
        ret = c.ret if not pending else self._deadline(c)
        cp.ops.append(lincheck.Op(c.call, ret, step, describe(c), ref=c, optional=pending))
        cp.calls.append(c)
        cp.items.append(item)

    def _same_end_ops(self, cp, c, op):
        """The indices (filled lazily, when the component is complete) of the other operations
        `op` of c's end in cp."""
        box = {}

        def get():
            if "v" not in box:
                box["v"] = [j for j, x in enumerate(cp.calls)
                            if x is not None and x is not c and x.op == op and x.sock() == c.sock()]
            return box["v"]
        return get

    def _pending_read(self, cp, c, side, n):
        others = self._same_end_ops(cp, c, "Read")
        return lambda st, dn, s=side, n=n: Z.read_pending(st, s, n, any(not dn(j) for j in others()))

    def add_addr_op(self, cp, c):
        pending = c.e is None
        node = self.chain_of[c.proc.pid][0].name
        item = {"kind": "addr", "op": c.op, "node": node}
        if pending:
            if c.op in ("Dial", "DialTimeout"):
                step = lambda st, dn: Z.dial_pending(st)
                opt = True
            elif c.op == "ListenerClose":
                lid = c.id
                step = lambda st, dn, node=node, lid=(c.proc.pid, lid): Z.lis_close(st, node, lid, None)
                opt = True
            else:
                return  # a Listen or an Accept that never returned: leaving it out dominates
            cp.ops.append(lincheck.Op(c.call, self._deadline(c), step, describe(c), ref=c, optional=opt))
            cp.calls.append(c)
            cp.items.append(item)
            return
        m = self.mapped[id(c)]
        if m.bad:
            step = self._bad_step(c)
        elif c.op == "Listen":
            ok = m.res[0] == "ok"
            if not ok and m.res[1] != M.SYS:
                step = lambda st, dn, k=m.res[1]: ([], f"a Listen failure of kind {k} (ListenStep: only sys)")
            else:
                lid = (c.proc.pid, m.res[1]["id"]) if ok else None
                step = lambda st, dn, node=node, lid=lid, ok=ok: Z.listen(st, node, lid, ok)
        elif c.op == "Accept":
            lid = (c.proc.pid, c.id)
            if m.res[0] == "ok":
                ck = self.accept_conn.get(id(c))
                step = lambda st, dn, node=node, lid=lid, ck=ck: Z.accept(st, node, lid, None, ck)
            else:
                step = lambda st, dn, node=node, lid=lid, k=m.res[1]: Z.accept(st, node, lid, k, None)
        elif c.op == "ListenerClose":
            lid = (c.proc.pid, c.id)
            step = lambda st, dn, node=node, lid=lid, res=m.res: Z.lis_close(st, node, lid, res)
        else:  # Dial, DialTimeout
            if m.res[0] == "ok":
                ck = ("D", c.proc.pid, m.res[1]["id"])
                step = lambda st, dn, ck=ck: Z.dial_ok(st, ck)
            else:
                step = lambda st, dn, k=m.res[1]: Z.dial_fail(st, k)
        cp.ops.append(lincheck.Op(c.call, c.ret, step, describe(c), ref=c))
        cp.calls.append(c)
        cp.items.append(item)

    # -----------------------------------------------------------------------------------------
    def search_all(self):
        steps = 0
        for cp in self.comps:
            r = lincheck.search(cp.ops, cp.init, self.limit)
            cp.result = r
            steps = max(steps, r.steps)
            if r.ok:
                continue
            self.report_fail(cp, r)
        self.stats["max search steps (one component)"] = steps

    def report_fail(self, cp, r):
        name = (f"address {cp.key.decode()}" if cp.kind == "addr" else
                f"connection {self.conn_name(cp.key)}")
        f = r.fail
        if f.get("op") is None:
            kind = "inconclusive" if r.limit or cp.tainted else "not-admitted"
            self.findings.append(Finding(kind, name, f"{name}: {f['why']}"))
            return
        bad = cp.ops[f["op"]]
        ctx = []
        if f["prefix"]:
            ctx.append(f"the linearization up to there (last 8 of {len(f['prefix'])}):")
            ctx += ["  " + cp.ops[i].desc + _choice(ch) for i, ch in f["prefix"][-8:]]
        st = f["state"]
        ctx.append("the state there: " + (show_conn_state(st, cp.W) if cp.kind == "conn" else show_addr_state(st)))
        ctx.append("the operation no linearization admits: " + bad.desc)
        ctx.append("  why: " + f["why"])
        others = [(i, why) for i, why in f["tried"] if i != f["op"]]
        if others:
            ctx.append("the other candidates there:")
            ctx += ["  " + cp.ops[i].desc + "\n      why not: " + why for i, why in others[:6]]
        kind = "not-admitted"
        what = f"{name}: no linearization admits {bad.ref.where() if bad.ref else bad.desc} {bad.ref.op if bad.ref else ''}: {f['why']}"
        if cp.tainted:
            kind = "inconclusive"
            what += f" (the component has operations out of the model's scope: {'; '.join(cp.tainted[:3])})"
        t = (bad.ref.ret or bad.ref.call) if bad.ref else bad.call
        self.findings.append(Finding(kind, bad.ref.where() if bad.ref else name, what, ctx, t, bad.ref))

    def conn_name(self, ck):
        if ck[0] == "D":
            return f"{ck[1]}/{ck[2]} (dialed)"
        return f"{ck[1]}/{ck[2]} (accepted, no Dial returned it)"


def _choice(ch):
    if ch is None:
        return ""
    return f"   <- {ch}"


def check_run(run, plan=None, limit=5_000_000, replay=True):
    return Checker(run, plan=plan, limit=limit, replay=replay).check()


def report(res, max_findings=5, verbose=False):
    lines = [f"{res['run']}: {res['verdict']} ({res['seconds']:.2f} s)"]
    hard = [f for f in res["findings"] if f.kind in HARD]
    scope = [f for f in res["findings"] if f.kind in ("scope", "inconclusive")]
    warn = [f for f in res["findings"] if f.kind == "warning"]
    if verbose:
        for k in sorted(res["stats"]):
            lines.append(f"  {k}: {res['stats'][k]}")
        for n in res["notes"]:
            lines.append(f"  note: {n}")
    if hard:
        lines.append(f"  {len(hard)} finding(s); the first {min(len(hard), max_findings)}:")
        for f in sorted(hard, key=lambda f: f.t)[:max_findings]:
            lines.append(f"  - [{f.kind}] {f.where}: {f.what}")
            lines += ["      " + x for x in f.context]
    if scope:
        by = collections.Counter(f.what if f.kind == "scope" and f.where == "-" else
                                 (f.kind + ": " + f.what.split(":")[0]) for f in scope)
        lines.append(f"  out of scope: {len(scope)} event(s):")
        for k, v in by.most_common(8):
            lines.append(f"    {v} x {k}")
        if verbose:
            for f in [f for f in scope if f.kind == "inconclusive"][:3]:
                lines.append(f"  - [{f.kind}] {f.where}: {f.what}")
                lines += ["      " + x for x in f.context]
    if warn and verbose:
        lines.append(f"  warnings: {len(warn)}; the first: {warn[0].what}")
    return "\n".join(lines)
