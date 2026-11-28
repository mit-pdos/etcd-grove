#!/usr/bin/env python3
"""Check that no proof learns of Go's `fmt.Errorf` a fact true only of Perennial's model.

Until fmtmodel (2026-11-20, Perennial `79517dbdf`) Perennial's model of `fmt.Errorf` was
`errors.New(format)`: it did not model `%w` (Go returns a `*fmt.wrapError`) nor call the arguments'
formatting methods (`Error`, `String`, `Format`, `GoString`), which Go calls (notes/decisions.md,
"`fmt.Errorf` with `%w`: no fact from the model", and its H0 supersession). The model now does both
and is stuck where it cannot follow Go, so the proofs use its spec, `fmt.wp_Errorf`; this check keeps
any new step into the model's unfolding under review. A proof that steps into the model proves a statement true of Go only when
the statement says nothing the model and Go disagree on (a post of `True`, or one true of both) and
its premise excludes what the model leaves out. The declarations below are the proofs that step
into it, each reviewed; a new one fails this check until it is reviewed and added.

Reviewing a step: its post must never give `deepRep (.errString _)` (or any other fact of the
model's `*errorString` representation, which `reflect.DeepEqual`'s specs read) of the model's error
outside the disjunction with Go's error: Go returns a `*fmt.wrapError` for `%w`, which no such fact
describes (k8s 7g joint attack, m4; decided by etcd-grove-03, 2026-11-19).

The check reads proof TERMS, not the text (2026-11-18, replacing a search of the sources for
`@! fmt.Errorf` next to `wp_start`): `etc/tcb-report.lean` marks every constant whose term uses the
model's unfolding (the instance field `fmt.Assumptions.Errorf_unfold`, the model's body
`fmt.Errorf.impl`, the class's recursors or a raw projection of the field; Perennial's own
`fmt.Errorf.wp_proof`, true of Go, is sanctioned there) and lists, per root, those its proof
depends on. This script reads `.lake/tcb.json` (which `etc/tcb-report.py` writes; it needs an
up-to-date `lake build`) and fails on a step that some root reaches outside REVIEWED.

A generated package initialization proof (`etc/gen-init.py`: `Proof/<pkg>/Init.lean` or
`InitLinked.lean`, and a part's `<root>/Proof/...`) steps into the model without naming it: the
`fmt.Errorf` call is in the translation's `initialize'`, not in the proof. So a second check
(2026-11-19, prove-errinits; kept beside the term check by merge-origin9, 2026-11-20) reads the
translations: for every package whose `initialize'` calls `fmt.Errorf`, each call's format must
be a literal without `%` (no verb, so no `%w`: Go returns `errors.New(format)`, as the model), unless
no init proof of the package steps into a function (`wp_func_call`) or uses Perennial's model lemmas
(`Perennial.fmt.wp_`); and an init proof that does must be in REVIEWED_INIT (keyed by file: the
step is in the translation, not in a declaration of the proof). (`gen-init.py`'s `newvar_steps`
asserts the same of the formats it is given; this check does not trust its callers.)

usage: etc/errorf-wrap-check.py [--reuse] [--json PATH] [-v]
  --reuse   read the existing .lake/tcb.json (as etc/tcb-report.py --reuse); else recompute it
  -v        list every step reached, reviewed or not
(exit 1 on an unreviewed step, or an unreviewed or unsafe init proof)
"""
import argparse
import os
import pathlib
import re
import sys

ROOT = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.join(ROOT, "etc"))
import proof_roots  # noqa: E402

ROOT_P = pathlib.Path(ROOT)

# declaration (the user-facing constant a step belongs to; auxiliary `_proof_n`/`match_n`
# constants count as their declaration's): why its model step is true of Go. Keyed by constant, so
# a new step elsewhere in the same module is not covered (2026-11-18).
REVIEWED = {
    # (fmtmodel, 2026-11-20) Perennial's model of `fmt.Errorf` formats, calls the arguments' methods
    # as Go does and returns Go's error (`errors.New(s)`, `*wrapError`, `*wrapErrors`), stuck where it
    # cannot follow Go; the proofs that stepped into the previous model (`errors.New(format)`) now go
    # through `fmt.wp_Errorf` (ErrorfWrap, ErrorfErrs, ErrorfLeaf, `wp_Errorf_errStrOk`,
    # `wp_Errorf_errorfIs`, the generated initializers) or are axioms (ErrorfStrs,
    # `wp_Errorf_setArgs`, `wp_Errorf_labelArgs`; ErrorfSlice until 2026-11-24), so none is listed. A new step into the model's
    # unfolding is still refused until reviewed here.
}

# generated init proof (file): why its steps into its package initializer's `fmt.Errorf` calls are
# true of Go (`init_errors`)
REVIEWED_INIT = {
    # (prove-errinits, 2026-11-19) generated initializers of `var X = fmt.Errorf("...")` (`etc/gen-init.py`,
    # `newvar_steps`, which asserts the format has no `%`); the call is in the translation,
    # listed for the review (and `init_errors` checks their formats in the translation)
    # (fmtmodel, 2026-11-20) through `EtcdGrove.fmt.wp_Errorf_noPct` (Perennial's `fmt.wp_Errorf`)
    'Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/InitLinked.lean': 'formats without %: Go returns errors.New(format); fmt.wp_Errorf',
    'Proof/go_etcd_io/etcd/pkg/v3/ioutil/Init.lean': 'formats without %: Go returns errors.New(format); fmt.wp_Errorf',
    # (prove-rpctypes, 2026-11-20) found by `init_errors`: `ErrNotReady = fmt.Errorf("cache: store not
    # ready")` goes through `EtcdGrove.fmt.wp_Errorf` (since fmtmodel a theorem over Perennial's), its steps are other functions'
    'Proof/go_etcd_io/etcd/cache/v3/InitLinked.lean': 'format without %; its Errorf step is EtcdGrove.fmt.wp_Errorf',
    # (#23, 2026-11-22) api/meta's `errNotList`/`errNotObject` (`fmt.Errorf` of constants without `%`)
    # (prove-metav1, 2026-11-27: its `wp_initialize'` moved to `InitLinked.lean`, as metav1's)
    'Proof/k8s_io/apimachinery/pkg/api/meta/InitLinked.lean': 'formats without %: Go returns errors.New(format); fmt.wp_Errorf',
    # (dsv-rabia, 2026-11-23) gogo-generated `ErrInvalidLengthMessage`/`ErrIntOverflowMessage`/
    # `ErrUnexpectedEndOfGroupMessage = fmt.Errorf("proto: ...")` (constants without `%`); its
    # `var _ = fmt.Errorf` is a function value, not a call
    'Dsverify/Proof/rabia/internal/message/Init.lean': 'formats without %: Go returns errors.New(format); fmt.wp_Errorf',
}


# a call: `(App (App (App (Val (GoInstruction (FuncResolve ... fmt.Errorf []))) ...` (format, args);
# not the bare function value `(App (Val (GoInstruction (FuncResolve ... fmt.Errorf []))) (Val #()))`,
# which `var _ = fmt.Errorf` (gogo-generated code) translates to and which calls nothing (2026-11-23)
INIT_CALL = re.compile(r'\(App \(App \(App \(Val \(GoInstruction \(FuncResolve _root_\.Perennial\.fmt\.Errorf\b')
# `(Let "$a0" (Val #(go!"<format>")) (Let "$a1" ...) (App ... (FuncResolve ... fmt.Errorf [])))`
INIT_FMT = re.compile(r'\(Let "\$a0" \(Val #\(go!"((?:[^"\\]|\\.)*)"\)\)\s*\(Let "\$a1" [^\n]*\n\s*'
                      r'\(App \(App \(App \(Val \(GoInstruction \(FuncResolve _root_\.Perennial\.fmt\.Errorf\b')
INIT_STEP = re.compile(r'\bwp_func_call\b|Perennial\.fmt\.wp_')


def init_errors():
    """The init proofs that step into the model of a package whose `initialize'` calls `fmt.Errorf`
    with a format that is not a literal without `%`, or that are not reviewed."""
    bad = []
    for code in sorted(ROOT_P.glob('**/Code/**/*.lean')):
        rel = code.relative_to(ROOT_P)
        if rel.parts[0] in ('.lake', 'old') or 'Code' not in rel.parts[:2]:
            continue
        s = code.read_text()
        i = s.find("noncomputable def initialize'")
        if i < 0:
            continue
        body = s[i:s.find('\n\n', i)]
        calls = len(INIT_CALL.findall(body))
        if not calls:
            continue
        fmts = INIT_FMT.findall(body)
        unsafe = len(fmts) != calls or any('%' in f for f in fmts)
        k = rel.parts.index('Code')
        pdir = ROOT_P.joinpath(*rel.parts[:k], 'Proof', *rel.parts[k + 1:]).with_suffix('')
        for pf in (pdir / 'Init.lean', pdir / 'InitLinked.lean'):
            if not pf.exists() or not INIT_STEP.search(pf.read_text()):
                continue
            prel = str(pf.relative_to(ROOT_P))
            if unsafe:
                bad.append(f'{prel} steps into functions while {rel}\'s initializer calls `fmt.Errorf` '
                           f'with a format that is not a literal without `%`')
            elif prel not in REVIEWED_INIT:
                bad.append(f'{prel} steps into {rel}\'s initializer\'s `fmt.Errorf` calls; review it '
                           f'and add it to REVIEWED_INIT')
    return bad


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
        ok = s["user"] in REVIEWED
        bad += not ok
        if args.v or not ok:
            rs = reach[c]
            print(f"errorf-wrap: {'reviewed' if ok else 'UNREVIEWED'} {s['user']} ({s['module']}, "
                  f"line {s['line']}) steps into the `fmt.Errorf` model; reached by {len(rs)} "
                  f"roots, e.g. {', '.join(rs[:3])}", file=sys.stderr if not ok else sys.stdout)
    init_bad = init_errors()
    for m in init_bad:
        print(f'errorf-wrap: {m}', file=sys.stderr)
    if bad:
        print("errorf-wrap: review the steps above (is the statement true of Go's Errorf, which "
              "wraps %w and calls the arguments' formatting methods?) and add their declarations to "
              "REVIEWED", file=sys.stderr)
    if bad or init_bad:
        return 1
    print(f"errorf-wrap: ok ({len(reach)} model steps reached, all in the {len(REVIEWED)} "
          "reviewed declarations; init proofs: "
          f"{len(REVIEWED_INIT)} reviewed)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
