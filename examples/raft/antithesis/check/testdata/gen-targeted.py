#!/usr/bin/env python3
"""Hand-built report streams, each ending at a step that one guard of the binding refuses (or a
property it flags), with TLC's verdict on each, for the differential test (diff_test.go). They
exercise the guards that no recorded, simulated or randomly perturbed stream reaches
(notes/antithesis-check-design.md §7: the surviving self-mutants).

    EFR=/path/to/etcd-raft-formalized python3 -I testdata/gen-targeted.py [--no-tlc]

Writes testdata/targeted/<name>.ndjson.gz and testdata/verdicts-targeted.txt (source `targeted`).
All streams use EtcdBindingEmpty.cfg (three voters, empty logs) unless named otherwise.
"""
import gzip
import json
import os
import subprocess
import sys
import tempfile

here = os.path.dirname(os.path.abspath(__file__))
N = ["raft1", "raft2", "raft3"]


class S:
    """A stream being built, with each node's state as the reports leave it."""

    def __init__(self):
        self.ev = []
        self.st = {n: dict(term=0, vote="", commit=0, log=[], role="follower") for n in N}

    def add(self, e):
        self.ev.append(e)
        return self

    def boot_all(self):
        for n in N:
            self.add({"e": "boot", "node": n, "term": 0, "vote": "", "commit": 0, "lastIndex": 0, "lastTerm": 0,
                      "applied": 0, "voters": N, "outgoing": []})
        return self

    def ready(self, n, by, role, term, vote, commit, first=0, entries=()):
        entries = list(entries)
        s = self.st[n]
        s.update(term=term, vote=vote, commit=commit, role=role)
        if entries:
            s["log"] = s["log"][:first - 1] + entries
        return self.add({"e": "ready", "node": n, "by": by, "role": role, "term": term, "vote": vote,
                         "commit": commit, "first": first, "entries": entries})

    def msg(self, ty, frm, to, term, index=0, logTerm=0, entries=(), commit=0, reject=False):
        return {"type": ty, "from": frm, "to": to, "term": term, "index": index, "logTerm": logTerm,
                "entries": list(entries), "commit": commit, "reject": reject, "hint": 0}

    def send(self, n, by, m, **extra):
        e = {"e": "send", "node": n, "by": by, "msg": m}
        e.update(extra)
        return self.add(e)

    def recv(self, n, m):
        return self.add({"e": "recv", "node": n, "msg": m})

    def deliver(self, by, m, **extra):
        """send by m's sender, recv by its receiver."""
        self.send(m["from"], by, m, **extra)
        return self.recv(m["to"], m)

    def campaign(self, c, term):
        """c campaigns for term (and, from an earlier term, for each term up to it first)."""
        s = self.st[c]
        for t in range(s["term"] + 1, term + 1):
            self.ready(c, "campaign", "candidate", t, c, s["commit"])
        return self

    def vote_req(self, c, v, term):
        s = self.st[c]
        lt = s["log"][-1]["term"] if s["log"] else 0
        return self.msg("vote", c, v, term, index=len(s["log"]), logTerm=lt)

    def win(self, c, v, term):
        """c, a candidate in term, asks v, which votes; c leads and appends its empty entry."""
        self.deliver("campaign", self.vote_req(c, v, term))
        sv = self.st[v]
        self.ready(v, "recv", "follower", term, c, sv["commit"])
        self.deliver("recv", self.msg("voteresp", v, c, term))
        s = self.st[c]
        return self.ready(c, "recv", "leader", term, c, s["commit"], len(s["log"]) + 1, [noop(term)])


def noop(t):
    return {"term": t, "type": "noop", "value": ""}


def cmd(t, v):
    return {"term": t, "type": "command", "value": v}


# ---------------------------------------------------------------------------------------------
# One stream per guard.

def up_to_date():
    """A node votes for a candidate whose log is behind its own (R 237-239 UpToDate, in OnDisk's
    vote guard, B 370-372): raft2 holds raft1's entry of term 1; raft3, with an empty log, asks it
    for its vote in term 2, and it votes."""
    s = S().boot_all()
    s.campaign("raft1", 1).win("raft1", "raft2", 1)
    s.deliver("recv", s.msg("app", "raft1", "raft2", 1, entries=[noop(1)]))
    s.ready("raft2", "recv", "follower", 1, "raft1", 0, 1, [noop(1)])
    s.campaign("raft3", 2)
    s.deliver("campaign", s.vote_req("raft3", "raft2", 2))
    return s.ready("raft2", "recv", "follower", 2, "raft3", 0)


def has_first():
    """A follower stores entries from the k-th of a request on although its log does not hold the
    first k-1 (OnDisk's HasFirst(n, f, k - 1), B 385): raft1 holds its own entry of term 1; raft2,
    leader of term 2, sends it [noop(2), x(2)] after index 0, and raft1 reports storing x at index 2."""
    s = S().boot_all()
    s.campaign("raft1", 1).win("raft1", "raft2", 1)
    s.campaign("raft2", 2).win("raft2", "raft3", 2)
    s.ready("raft2", "propose", "leader", 2, "raft2", 0, 2, [cmd(2, "x")])
    m = s.msg("app", "raft2", "raft1", 2, entries=[noop(2), cmd(2, "x")])
    s.deliver("propose", m)
    return s.ready("raft1", "recv", "follower", 2, "", 0, 2, [cmd(2, "x")])


def apply_beyond_commit():
    """A follower applies an entry committed by its leader before its own commit index covers it
    (ApplyBeyondCommit, B 606-607): VIOLATED."""
    s = S().boot_all()
    s.campaign("raft1", 1).win("raft1", "raft2", 1)
    s.deliver("recv", s.msg("app", "raft1", "raft2", 1, entries=[noop(1)]))
    s.ready("raft2", "recv", "follower", 1, "raft1", 0, 1, [noop(1)])
    s.deliver("recv", s.msg("appresp", "raft2", "raft1", 1, index=1))
    s.ready("raft1", "recv", "leader", 1, "raft1", 1)
    return s.add({"e": "apply", "node": "raft2", "by": "tick", "first": 1, "entries": [noop(1)]})


def boot_undo_made():
    """A node restarts without the write it said was on disk (Boot's ~u.made, B 174): a batching
    node's campaign write, flushed, announced (`net`) and made, then `boot` with the state before
    it."""
    s = S().boot_all()
    s.add({"e": "mem", "node": "raft1", "by": "campaign", "role": "candidate", "term": 1, "vote": "raft1",
           "commit": 0, "w": 1})
    s.add({"e": "flush", "node": "raft1", "more": 0})
    s.add({"e": "net", "node": "raft1", "term": 1, "vote": "raft1", "commit": 0, "first": 0, "entries": []})
    s.add({"e": "made", "node": "raft1"})
    return s.add({"e": "boot", "node": "raft1", "term": 0, "vote": "", "commit": 0, "lastIndex": 0, "lastTerm": 0,
                  "applied": 0, "voters": N, "outgoing": []})


def net_low():
    """A batching leader's write said (`net`) to hold no entries although a flushed report stored
    one (Net's u.low = 0, B 487)."""
    s = S().boot_all()
    s.campaign("raft1", 1)
    s.deliver("campaign", s.vote_req("raft1", "raft2", 1))
    s.ready("raft2", "recv", "follower", 1, "raft1", 0)
    s.deliver("recv", s.msg("voteresp", "raft2", "raft1", 1))
    s.add({"e": "mem", "node": "raft1", "by": "recv", "role": "leader", "term": 1, "vote": "raft1", "commit": 0,
           "w": 1, "entries": [noop(1)]})
    s.add({"e": "flush", "node": "raft1", "more": 0})
    return s.add({"e": "net", "node": "raft1", "term": 1, "vote": "raft1", "commit": 0, "first": 0, "entries": []})


def leader_new_term_write():
    """A queued write of a later term made while the node leads (OnDisk's T1 # T0 => ro[n] #
    Leader, B 365): with AsyncStorageWrites, raft1 queues a campaign for term 2, then wins term 1
    with the grant that arrives, then writes the term-2 campaign as leader."""
    s = S().boot_all()

    def mem(n, by, role, term, vote, commit, first=0, entries=()):
        return s.add({"e": "mem", "node": n, "by": by, "role": role, "term": term, "vote": vote, "commit": commit,
                      "w": 1, "first": first, "entries": list(entries)})

    mem("raft1", "campaign", "candidate", 1, "raft1", 0)
    s.add({"e": "write", "node": "raft1", "term": 1, "vote": "raft1", "commit": 0, "first": 0, "entries": []})
    s.add({"e": "wrote", "node": "raft1"})
    s.deliver("campaign", s.vote_req("raft1", "raft2", 1), cause=[])
    s.ready("raft2", "recv", "follower", 1, "raft1", 0)
    s.deliver("recv", s.msg("voteresp", "raft2", "raft1", 1))
    s.ev.pop()  # its receipt comes after the timeout below
    mem("raft1", "tick", "candidate", 2, "raft1", 0)
    s.recv("raft1", s.msg("voteresp", "raft2", "raft1", 1))
    mem("raft1", "recv", "leader", 1, "raft1", 0, 1, [noop(1)])
    return s.add({"e": "write", "node": "raft1", "term": 2, "vote": "raft1", "commit": 0, "first": 0, "entries": []})


def gc_stale_leader():
    """A batched request of a term every node has left, sent after the binding forgot that term's
    leader (GC, B 709-721; StaleLed makes GC due at once): raft1 led term 1; all three move to term
    2 (raft1 refusing raft3's vote); raft1 then sends a heartbeat of term 1 in a batched Ready."""
    s = S().boot_all()
    s.campaign("raft1", 1).win("raft1", "raft2", 1)
    s.campaign("raft3", 2)
    s.deliver("campaign", s.vote_req("raft3", "raft2", 2))
    s.ready("raft2", "recv", "follower", 2, "raft3", 0)
    s.send("raft2", "recv", s.msg("voteresp", "raft2", "raft3", 2))
    s.deliver("campaign", s.vote_req("raft3", "raft1", 2))
    s.ready("raft1", "recv", "follower", 2, "", 0)
    # (each node's last write now known made: a send after it, B 527, so every EffTerm is 2)
    s.send("raft1", "recv", s.msg("voteresp", "raft1", "raft3", 2, reject=True))
    return s.send("raft1", "batch", s.msg("hb", "raft1", "raft2", 1), b=1)


def old_grant(rounds, probe_term):
    """Leadership alternates between raft1 and raft2 for `rounds` terms while raft3 stays at term 0
    (so no term is ever over and only the count of garbage makes GC due, B 711); each leader's
    follower acks its empty entry. Then raft2 sends a grant for an earlier term it voted in: accepted
    unless GC dropped that vote (OldVotes, B 708). Which round makes the difference depends on how
    many acks count as garbage (B 699-701)."""
    s = S().boot_all()
    for t in range(1, rounds + 1):
        c, v = ("raft1", "raft2") if t % 2 else ("raft2", "raft1")
        s.campaign(c, t).win(c, v, t)
        st = s.st[c]
        last = len(st["log"])
        prev = last - 1
        m = s.msg("app", c, v, t, index=prev, logTerm=st["log"][prev - 1]["term"] if prev else 0,
                  entries=[noop(t)])
        s.deliver("recv", m)
        s.ready(v, "recv", "follower", t, c, s.st[v]["commit"], last, [noop(t)])
        s.deliver("recv", s.msg("appresp", v, c, t, index=last))
    # raft2 voted for raft1 in the odd terms.
    return s.send("raft2", "recv", s.msg("voteresp", "raft2", "raft1", probe_term))


TARGETS = {
    "up-to-date": up_to_date,
    "has-first": has_first,
    "apply-beyond-commit": apply_beyond_commit,
    "boot-undo-made": boot_undo_made,
    "net-low": net_low,
    "leader-new-term-write": leader_new_term_write,
    "gc-stale-leader": gc_stale_leader,
}
# The GC-count streams, at round counts around where GC first becomes due by count (10) and where
# counting the acks of the term just left decides it (21-22), with every earlier odd term as probe.
for r in (9, 10, 21, 22):
    for p in range(1, r, 2):
        TARGETS["old-grant-%d-%d" % (r, p)] = (lambda r=r, p=p: old_grant(r, p))


def verdict(lines, efr, tmp):
    fm = os.path.join(efr, "antithesis-fm")
    sf = os.path.join(tmp, "s.ndjson")
    for f in os.listdir(tmp):
        os.remove(os.path.join(tmp, f))
    with open(sf, "w") as f:
        f.writelines(lines)
    open(sf + ".eof", "w").close()
    out = subprocess.run([sys.executable, "-I", os.path.join(fm, "tracekit/check/streamcheck.py"),
                          os.path.join(fm, "spec", "manifest-empty.json"), sf], capture_output=True, text=True).stdout
    return out.splitlines()[0][:300] if out else "ERROR no output"


def main():
    only = [a for a in sys.argv[1:] if not a.startswith("--")]
    os.makedirs(os.path.join(here, "targeted"), exist_ok=True)
    out = None if "--no-tlc" in sys.argv else open(os.path.join(here, "verdicts-targeted.txt"), "w")
    with tempfile.TemporaryDirectory() as tmp:
        for name, f in TARGETS.items():
            if only and name not in only:
                continue
            lines = [json.dumps(e, separators=(",", ":")) + "\n" for e in f().ev]
            rel = "targeted/%s.ndjson.gz" % name
            with gzip.open(os.path.join(here, rel), "wt") as g:
                g.writelines(lines)
            if out:
                v = verdict(lines, os.environ["EFR"], tmp)
                out.write("targeted %s EtcdBindingEmpty.cfg %d %s\n" % (rel, len(lines), v))
                out.flush()
                print(name, v[:100], flush=True)


main()
