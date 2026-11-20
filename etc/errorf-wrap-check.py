#!/usr/bin/env python3
"""Check that no proof learns a `fmt.Errorf` error's facts from Perennial's model.

Perennial's model of `fmt.Errorf` is `errors.New(format)`, which does not model `%w` (Go returns a
`*fmt.wrapError`; notes/decisions.md, "`fmt.Errorf` with `%w`: no fact from the model"). A fact
learned by stepping into the model is true of Go only when the lemma's statement says nothing
the model and Go disagree on (a post of `True`) or its premise excludes `%w`. The proofs that step
into it are the files below, each reviewed; a new one fails this check until it is reviewed and
added. The other specs of `fmt.Errorf` are axioms true of Go (`Spec/fmt/{Errorf,ErrorfPlain,
ErrorfWrap}.lean`). A cheap check, not a proof: it reads names, not terms.

A generated package initialization proof (`etc/gen-init.py`: `Proof/<pkg>/Init.lean` or
`InitLinked.lean`, and a part's `<root>/Proof/...`) steps into the model without naming it: the
`fmt.Errorf` call is in the translation's `initialize'`, not in the proof. So the second check reads
the translations: for every package whose `initialize'` calls `fmt.Errorf`, each call's format must
be a literal without `%` (no verb, so no `%w`: Go returns `errors.New(format)`, as the model), unless
no init proof of the package steps into a function (`wp_func_call`) or uses Perennial's model lemmas
(`Perennial.fmt.wp_`); and an init proof that does must be in REVIEWED. (`gen-init.py`'s
`newvar_steps` asserts the same of the formats it is given; this check does not trust its callers.)

usage: etc/errorf-wrap-check.py   (exit 1 on an unreviewed file)
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# file: why its model step is true of Go
REVIEWED = {
    'Proof/k8s_io/client_go/listers/apps/v1/ErrorfLabels.lean': 'post True',
    'Proof/k8s_io/client_go/tools/cache/ErrorfSet.lean': 'post True',
    'Proof/go_etcd_io/etcd/server/v3/storage/mvcc/Errorf.lean': 'premise (W8 37) ∉ format',
    # premise-fixes-4: `wp_Errorf_errStrOk` (post: some `Error()` string, no `Format` method)
    'Proof/go_etcd_io/etcd/cache/v3/Base.lean': 'premise ArgsWf: no argument is an error, so Go wraps nothing and returns errors.New(s)',
    # (prove-errinits, 2026-11-19) generated initializers of `var X = fmt.Errorf("...")` (`etc/gen-init.py`,
    # `newvar_steps`, which asserts the format has no `%`); not matched by MODEL (the call is in the
    # translation), listed for the review (and `init_errors` checks their formats in the translation)
    'Proof/go_etcd_io/etcd/server/v3/etcdserver/api/rafthttp/InitLinked.lean': 'formats without %: Go returns errors.New(format), the model',
    'Proof/go_etcd_io/etcd/pkg/v3/ioutil/Init.lean': 'formats without %: Go returns errors.New(format), the model',
    # (prove-rpctypes, 2026-11-20) found by `init_errors`: `ErrNotReady = fmt.Errorf("cache: store not
    # ready")` goes through `EtcdGrove.fmt.wp_Errorf` (an axiom true of Go), its steps are other functions'
    'Proof/go_etcd_io/etcd/cache/v3/InitLinked.lean': 'format without %; its Errorf step is the axiom EtcdGrove.fmt.wp_Errorf',
}

MODEL = re.compile(r'@! (_root_\.)?Perennial\.fmt\.Errorf\b')
STEP = re.compile(r'\bwp_start\b|\bwp_func_call\b')


INIT_CALL = re.compile(r'FuncResolve _root_\.Perennial\.fmt\.Errorf\b')
# `(Let "$a0" (Val #(go!"<format>")) (Let "$a1" ...) (App ... (FuncResolve ... fmt.Errorf [])))`
INIT_FMT = re.compile(r'\(Let "\$a0" \(Val #\(go!"((?:[^"\\]|\\.)*)"\)\)\s*\(Let "\$a1" [^\n]*\n\s*'
                      r'\(App \(App \(App \(Val \(GoInstruction \(FuncResolve _root_\.Perennial\.fmt\.Errorf\b')
INIT_STEP = re.compile(r'\bwp_func_call\b|Perennial\.fmt\.wp_')


def init_errors():
    """The init proofs that step into the model of a package whose `initialize'` calls `fmt.Errorf`
    with a format that is not a literal without `%`, or that are not reviewed."""
    bad = []
    for code in sorted(ROOT.glob('**/Code/**/*.lean')):
        rel = code.relative_to(ROOT)
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
        pdir = ROOT.joinpath(*rel.parts[:k], 'Proof', *rel.parts[k + 1:]).with_suffix('')
        for pf in (pdir / 'Init.lean', pdir / 'InitLinked.lean'):
            if not pf.exists() or not INIT_STEP.search(pf.read_text()):
                continue
            prel = str(pf.relative_to(ROOT))
            if unsafe:
                bad.append(f'{prel} steps into functions while {rel}\'s initializer calls `fmt.Errorf` '
                           f'with a format that is not a literal without `%`')
            elif prel not in REVIEWED:
                bad.append(f'{prel} steps into {rel}\'s initializer\'s `fmt.Errorf` calls; review it '
                           f'and add it to REVIEWED')
    return bad


def main():
    bad = []
    for f in sorted(ROOT.glob('**/*.lean')):
        rel = f.relative_to(ROOT)
        # SpecPlan/: the spec plan, specs only (no proof steps into any model)
        if rel.parts[0] in ('.lake', 'old', 'Code', 'GeneratedProof', 'SpecPlan') or 'Code' in rel.parts[:2]:
            continue
        s = f.read_text()
        if MODEL.search(s) and STEP.search(s) and str(rel) not in REVIEWED:
            bad.append(rel)
    for rel in bad:
        print(f'errorf-wrap: {rel} steps into the `fmt.Errorf` model; review it '
              f'(a `%w` format?) and add it to REVIEWED', file=sys.stderr)
    init_bad = init_errors()
    for m in init_bad:
        print(f'errorf-wrap: {m}', file=sys.stderr)
    if bad or init_bad:
        return 1
    print(f'errorf-wrap: ok ({len(REVIEWED)} reviewed model steps)')
    return 0


if __name__ == '__main__':
    sys.exit(main())
