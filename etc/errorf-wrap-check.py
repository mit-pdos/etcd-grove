#!/usr/bin/env python3
"""Check that no proof learns of Go's `fmt.Errorf` a fact true only of Perennial's model.

Perennial's model of `fmt.Errorf` is `errors.New(format)`: it does not model `%w` (Go returns a
`*fmt.wrapError`) nor call the arguments' formatting methods (`Error`, `String`, `Format`,
`GoString`), which Go calls (notes/decisions.md, "`fmt.Errorf` with `%w`: no fact from the model",
and its H0 supersession). A proof that steps into the model proves a statement true of Go only when
the statement says nothing the model and Go disagree on (a post of `True`, or one true of both) and
its premise excludes what the model leaves out. The modules below hold the proofs that step into
it, each reviewed; a new one fails this check until it is reviewed and added.

The check reads proof TERMS, not the text (2026-11-18, replacing a search of the sources for
`@! fmt.Errorf` next to `wp_start`): `etc/tcb-report.lean` marks every constant whose term uses the
model's unfolding (the instance field `fmt.Assumptions.Errorf_unfold`, the model's body
`fmt.Errorf.impl`, the class's recursors or a raw projection of the field; Perennial's own
`fmt.Errorf.wp_proof`, true of Go, is sanctioned there) and lists, per root, those its proof
depends on. This script reads `.lake/tcb.json` (which `etc/tcb-report.py` writes; it needs an
up-to-date `lake build`) and fails on a step that some root reaches outside REVIEWED.

usage: etc/errorf-wrap-check.py [--reuse] [--json PATH] [-v]
  --reuse   read the existing .lake/tcb.json (as etc/tcb-report.py --reuse); else recompute it
  -v        list every step reached, reviewed or not
(exit 1 on an unreviewed step)
"""
import argparse
import os
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402

# module: why its model step is true of Go
REVIEWED = {
    'Proof.k8s_io.client_go.listers.apps.v1.ErrorfLabels': 'post True',
    'Proof.k8s_io.client_go.tools.cache.ErrorfSet': 'post True',
    'Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Errorf': 'premise (W8 37) not in format: no verb, '
        'no argument formatted',
    # premise-fixes-4: `wp_Errorf_errStrOk` (post: some `Error()` string, no `Format` method)
    'Proof.go_etcd_io.etcd.cache.v3.Base': 'premise ArgsWf: no argument is an error or has '
        'methods, so Go wraps nothing, calls no method, and returns errors.New(s)',
    # H0 (2026-11-18): the post's left disjunct is the model's error, the right Go's *wrapError;
    # the description conjunct is conditional on Go's `Unwrap` (vacuous of the model's error)
    'Proof.fmt.ErrorfWrap': 'post: the model\'s error or Go\'s *fmt.wrapError; prefix of errDesc '
        'only given an Unwrap method',
    # fmt soundness (2026-11-18): nil, basic, FileMode (String() writes only its own buffer) and
    # []string (read under the fraction given back) arguments: Go calls no method with an effect
    'Proof.fmt.ErrorfStrs': 'post errOk only; arguments basic, []string or FileMode (String() '
        'local), no error arguments',
    # NOT reviewed (fmt soundness item 3, refuted 2026-11-18: their premises admit arguments whose
    # Format/String/Error Go calls with effects or nested panics): Proof.fmt.ErrorfErrs,
    # Proof.fmt.ErrorfAny
}


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--reuse", action="store_true")
    ap.add_argument("--json", default=os.path.join(ROOT, ".lake", "tcb.json"))
    ap.add_argument("-v", action="store_true")
    args = ap.parse_args()
    objs = proof_roots.load(args.json, "errorf-wrap-check", args.reuse)
    steps, reach = {}, {}
    for o in objs:
        if o["t"] == "root":
            if "errorf" not in o:
                sys.exit("errorf-wrap-check: " + args.json + " is of an older etc/tcb-report.lean "
                         "(no `errorf` field); rerun etc/tcb-report.py without --reuse")
            for c in o["errorf"]:
                reach.setdefault(c, []).append(o["name"])
        elif o["t"] == "errorf":
            steps[o["name"]] = o
    bad = 0
    for c in sorted(reach):
        s = steps.get(c, {"user": c, "module": "?", "line": 0})
        ok = s["module"] in REVIEWED
        bad += not ok
        if args.v or not ok:
            rs = reach[c]
            print(f"errorf-wrap: {'reviewed' if ok else 'UNREVIEWED'} {s['user']} ({s['module']}, "
                  f"line {s['line']}) steps into the `fmt.Errorf` model; reached by {len(rs)} "
                  f"roots, e.g. {', '.join(rs[:3])}", file=sys.stderr if not ok else sys.stdout)
    if bad:
        print("errorf-wrap: review the steps above (is the statement true of Go's Errorf, which "
              "wraps %w and calls the arguments' formatting methods?) and add their modules to "
              "REVIEWED", file=sys.stderr)
        return 1
    print(f"errorf-wrap: ok ({len(reach)} model steps reached, all in the {len(REVIEWED)} "
          "reviewed modules)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
