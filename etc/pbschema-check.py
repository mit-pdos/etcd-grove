#!/usr/bin/env python3
"""The descriptor check of the trusted protobuf schemas (per-type message models, stage A,
`[v6a]` 1 and 6).

Each `pbModelOf` registration's wire content is read against the schemas of `pbSchemaOf`
(`Proof/google_golang_org/protobuf/proto/PbSchema.lean`), which are trusted: an over-declared
schema makes the decoder trust (`proto.UnmarshalPbC`'s D1) false, an under-declared one its round
trip (D2). This check:

1. runs `etc/PbSchemaDump.lean` on the modules declaring the registrations (found in the sources:
   an `axiom` whose statement is `pbModelOf … = some …`), which prints `pbSchemaOf`'s table, the
   registered roots, and the schema constants each registered instance reaches;
2. checks that every schema constant an instance reaches is one of `pbSchemaOf`'s;
3. runs the Go test `examples/pbschema` on the dump: every message type reachable from a root has
   a schema equal to its `protoreflect` descriptor (number -> the wire types the decoder takes),
   and no reachable type has a proto2 unpacked repeated int32 or enum field, nor another unpacked
   repeated scalar numbered 16 or more (D1's 2x size bound);
4. negative tests: the Go test must fail on the dump with a field added to a schema
   (over-declared: `(5,[0])` in `raftpb.Entry`'s), and with a wire type removed
   (under-declared: `ConfState`'s packed `2`);
5. runs the tests of `examples/pbschema` that need no dump: `TestD1PostMessage`/`TestD1PostEntry`
   (the decoder's post D1 of `UnmarshalPb.lean` at raftpb.Message/Entry, with the instances'
   size, levels and decOk of `PerTypeMessage.lean`/raft's `PbEntryType.lean`),
   `TestD2P2EntryEncoder`/`TestD2P2MessageEncoder` (the round trip D2 and the encoder axioms
   `entryEncC_ok`/`msgEncC_ok`), `TestSizeBoundCondition` (step 3's size bound condition), and
   (out_size B2) `TestB2CCDecoderUf`/`TestB2MustUnmarshalCC` (the conf-change decoders' unknown fields
   at their schemas) and `TestA3CCLen`/`TestA3CC2Len` (`proto.MarshalConfChange[V2]`'s `ccLenMax`).

    etc/pbschema-check.py        prints one line, exits 1 on a failure

Never builds: the `.olean`s must be up to date (`lake build`). `$LAKE_OPTS` is passed to lake.
Needs go (`GOTOOLCHAIN`, `GOWORK=off` are set).
"""
import os
import re
import subprocess
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
REG = re.compile(r"^axiom\s+(\S+)[^\n]*(?:\n(?!axiom|theorem|def|/--)[^\n]*)*?pbModelOf\s+GF\s+\S+\s*=\s*some", re.M)


def reg_modules():
    mods = []
    for d in ("Proof", "Spec"):
        for dp, _, fs in os.walk(os.path.join(ROOT, d)):
            for f in fs:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(dp, f)
                s = open(p, encoding="utf-8").read()
                if "pbModelOf GF" in s and REG.search(s):
                    mods.append(os.path.relpath(p, ROOT)[:-5].replace(os.sep, "."))
    return sorted(mods)


def lake(*args):
    return ["lake", *os.environ.get("LAKE_OPTS", "").split(), *args]


# the tests of examples/pbschema that need no dump (d1post_test.go, descriptor_test.go)
POST_TESTS = "^(TestD1PostMessage|TestD1PostEntry|TestD2P2EntryEncoder|TestD2P2MessageEncoder|TestSizeBoundCondition|TestB2CCDecoderUf|TestB2MustUnmarshalCC|TestA3CCLen|TestA3CC2Len)$"


def go_test(dump, run="^TestSchemas$"):
    env = dict(os.environ, GOWORK="off", GOTOOLCHAIN=os.environ.get("GOTOOLCHAIN", "go1.27.1"),
               PATH="/usr/local/go/bin:" + os.path.expanduser("~/go/bin") + ":" + os.environ["PATH"])
    if dump is not None:
        env["PBSCHEMA_DUMP"] = dump
    else:
        env.pop("PBSCHEMA_DUMP", None)
    r = subprocess.run(["go", "test", "-count=1", "-v", "-run", run, "./pbschema/"],
                       cwd=os.path.join(ROOT, "examples"), env=env, capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def main():
    mods = reg_modules()
    if not mods:
        sys.exit("pbschema: FAILED: no pbModelOf registration found in the sources")
    env = dict(os.environ)
    env["PATH"] = os.path.expanduser("~/.elan/bin") + os.pathsep + env.get("PATH", "")
    r = subprocess.run(lake("env", "lean", "--run", "etc/PbSchemaDump.lean", *mods), cwd=ROOT,
                       env=env, capture_output=True, text=True)
    if r.returncode != 0:
        print(r.stdout + r.stderr)
        sys.exit("pbschema: FAILED: etc/PbSchemaDump.lean failed")
    dump = r.stdout
    table = {}
    roots = []
    uses = []
    for line in dump.splitlines():
        w = line.split()
        if not w:
            continue
        if w[0] == "schema":
            table[w[2]] = w[1]
        elif w[0] == "root":
            roots.append(w[1])
        elif w[0] == "uses":
            uses.append((w[1], w[2]))
    fail = []
    for reg, c in uses:
        if c not in table:
            fail.append(f"{reg} reaches the schema {c}, which is not one of pbSchemaOf's")
    # the dumps are kept (no deletion): in $PBSCHEMA_SCRATCH, default .lake/pbschema (untracked)
    td = os.environ.get("PBSCHEMA_SCRATCH", os.path.join(ROOT, ".lake", "pbschema"))
    os.makedirs(td, exist_ok=True)
    if True:
        p = os.path.join(td, "dump")
        open(p, "w").write(dump)
        rc, out = go_test(p)
        if rc != 0:
            fail.append("the Go descriptor test failed:\n" + "\n".join(
                l for l in out.splitlines() if "descriptor_test.go" in l or "FAIL" in l))
        # negative tests: an over-declared and an under-declared schema must be refused
        over = re.sub(r"^(schema raftpb\.Entry \S+) ", r"\1 5:0 ", dump, flags=re.M)
        under = re.sub(r"^(schema raftpb\.ConfState \S+ 1:)0,2", r"\g<1>0", dump, flags=re.M)
        for name, d in (("over-declared", over), ("under-declared", under)):
            if d == dump:
                fail.append(f"negative test {name}: the mutation did not apply")
                continue
            pm = os.path.join(td, f"dump-{name}")
            open(pm, "w").write(d)
            rc, _ = go_test(pm)
            if rc == 0:
                fail.append(f"negative test {name}: the Go test passed on a wrong schema")
        # the decoder's post D1, the round trip D2, the encoder axioms (P2), the size bound condition
        rc, out = go_test(None, POST_TESTS)
        if rc != 0:
            fail.append("the Go D1/D2/P2 tests failed:\n" + "\n".join(
                l for l in out.splitlines() if ("_test.go" in l and ("FAIL" in l or "Error" in l))
                or l.startswith("--- FAIL") or l.startswith("FAIL")))
        elif out.count("--- PASS") != 9:
            fail.append(f"the Go D1/D2/P2 and ConfChange tests: {out.count('--- PASS')} passed, want 9 ({POST_TESTS})")
    if fail:
        print("pbschema: FAILED")
        for f in fail:
            print("  " + f)
        sys.exit(1)
    print(f"pbschema: ok ({len(table)} schemas, roots {', '.join(sorted(roots))}; "
          f"2 negative tests refused; Go tests D1 post (Message, Entry), D2/P2 encoders (Entry, "
          f"Message), the size bound condition, and the ConfChange decoders and length bound passed)")


if __name__ == "__main__":
    main()
