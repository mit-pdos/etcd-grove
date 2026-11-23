#!/usr/bin/env python3
"""The gryff kit's replica boots (notes/dsv-gryff.md, "Package initializers"): for each replica
command (`cmd/server{2,3,4}`), `Dsverify/Proof/gryff/examples/gryffnet/cmd/<cmd>/Boot.lean`, its
initialization from a fresh process keeping `gryff`'s owned variables and trace prophecy
(`Dsverify/Proof/gryff/Boot/Defs.lean`). Generated from etc/gen-init.py's output: the program's
`PkgTable.lean` (its table and the package-by-package facts, here twice: for the table `g` and for
`gNo g`) and the `wp_initialize'_lb` bodies of `gryff`, `gryffnet` and the command (their import
steps). Run after etc/gen-init.py; `--check` exits 1 if a file differs. (A file starting with `_`:
not a kit file, etc/dsv/README.md.)"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
P = 'Dsverify/Proof/gryff'
REPLICAS = ['server2', 'server3', 'server4']
NO = {'gryff.src.gryff', 'gryff.examples.gryffnet'}


def wfname(pkg):
    return pkg.replace('«', '').replace('»', '').replace('.', '_')


def chains(table):
    """The table's facts as top-level theorems, for `g` (`wf_`) and for `gNo g` (`wfNo_`)."""
    blocks = re.findall(r'  have (h\d+) : GetIsPkgInitProp pkg_id\.(\S+) \(getIsPkgInit \(GF := GF\)\) := by\n'
                        r'    refine And\.intro \?_ \?_\n    · rfl\n    exact (.*)\n', table)
    names = {h: q for h, q, _ in blocks}
    out = []
    for kind in ['wf', 'wfNo']:
        for h, q, ex in blocks:
            if kind == 'wfNo' and (q in NO or q.startswith('gryff.examples.gryffnet.cmd.')):
                continue
            g = 'getIsPkgInit (GF := GF)' if kind == 'wf' else 'gNo (getIsPkgInit (GF := GF))'
            ex = re.sub(r'\bh\d+\b', lambda m: f'{kind}_{wfname(names[m.group(0)])}', ex)
            head = '· rfl' if kind == 'wf' else '· rw [gNo_ne _ _ (by decide)]; rfl'
            out.append(f'theorem {kind}_{wfname(q)} : GetIsPkgInitProp pkg_id.{q} ({g}) := by\n'
                       f'  refine And.intro ?_ ?_\n  {head}\n  exact {ex}\n')
    return '\n'.join(out)


def imports(init_txt):
    """The import steps of a generated `wp_initialize'_lb`: (package, hypothesis index)."""
    body = init_txt[init_txt.index("theorem wp_initialize'_lb"):]
    body = body[:body.index('/-- Perennial')]
    steps = []
    for m in re.finditer(r"wp_apply \((?:_root_\.Perennial\.(\S+)\.wp_initialize'_lb _ \S+\)"
                         r"|EtcdGrove\.(?:Dsv\.)?initLb_of_spec pkg_id\.\S+ _root_\.Perennial\.(\S+)\.initialize'"
                         r"[^$]*?\)) _ \$\$ Hown as ⟨Hown, #Hd(\d+)⟩", body):
        steps.append((m.group(1) or m.group(2), m.group(3)))
    return steps


def step(pkg, n, kind):
    return (f"  wp_apply (_root_.Perennial.{pkg}.wp_initialize' _ {kind}_{wfname(pkg)}) $$ Hown\n"
            f"    as ⟨Hown, #Hd{n}⟩")


GRYFF_ALLOCS = '''  wp_apply wp_GlobalAlloc (V := github_com.goose_lang.primitive.ProphId) _root_.Perennial.gryff.src.gryff.traceProph _ as Htp
  wp_apply wp_GlobalAlloc (V := GoMap) _root_.Perennial.gryff.src.gryff.deferMap _ as Hdm
  wp_apply wp_GlobalAlloc (V := gryff.src.gryffproto.AcceptOKReply) _root_.Perennial.gryff.src.gryff.aokr _ as Haokr
  wp_apply wp_GlobalAlloc (V := gryff.src.gryffproto.PreAcceptOKReply) _root_.Perennial.gryff.src.gryff.paokr _ as Hpaokr
  wp_apply wp_GlobalAlloc (V := gryff.src.epaxosproto.CommitShort) _root_.Perennial.gryff.src.gryff.ecs _ as Hecs
  wp_apply wp_GlobalAlloc (V := gryff.src.gryffproto.ECommit) _root_.Perennial.gryff.src.gryff.ec _ as Hec
  wp_apply wp_GlobalAlloc (V := gryff.src.gryffproto.EAccept) _root_.Perennial.gryff.src.gryff.ea _ as Hea
  wp_apply wp_GlobalAlloc (V := gryff.src.gryffproto.TryPreAccept) _root_.Perennial.gryff.src.gryff.tpa _ as Htpa
  wp_apply wp_GlobalAlloc (V := gryff.src.gryffproto.PreAccept) _root_.Perennial.gryff.src.gryff.pa _ as Hpa
  wp_apply wp_GlobalAlloc (V := w64) _root_.Perennial.gryff.src.gryff.happy _ as Hhappy
  wp_apply wp_GlobalAlloc (V := w64) _root_.Perennial.gryff.src.gryff.slow _ as Hslow
  wp_apply wp_GlobalAlloc (V := w64) _root_.Perennial.gryff.src.gryff.weird _ as Hweird
  wp_apply wp_GlobalAlloc (V := w64) _root_.Perennial.gryff.src.gryff.conflicted _ as Hconf
  wp_apply wp_GlobalAlloc (V := w64) _root_.Perennial.gryff.src.gryff.cpcounter _ as Hcpc
  wp_apply wp_GlobalAlloc (V := GoSlice) _root_.Perennial.gryff.src.gryff.cpMarker _ as Hcpm
  wp_apply wp_GlobalAlloc (V := w32) _root_.Perennial.gryff.src.gryff.bf_PT _ as Hbf
  wp_apply wp_GlobalAlloc (V := GoSlice) _root_.Perennial.gryff.src.gryff.stack _ as Hstk'''

GRYFF_END = '''  try wp_auto
  wp_apply (wp_slice_make3 (V := Loc) (W64 0) (W64 100) (by decide)) as %stk ⟨Hsl, Hcap, %Hcapv⟩
  try wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := w64) go.uint64 go.uint64) as %dm -
  try wp_auto
  wp_func_call
  wp_call
  try wp_auto
  wp_apply github_com.goose_lang.primitive.wp_NewProph as %pvs %p Hp
  try wp_auto
  ihave Hown := ownInitializing_weaken _ _ (gNo_le _) $$ Hown
  iframe Hown
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  isplitr
  · is_pkg_init_finish
  isplitl [Haokr Hpaokr Hecs Hec Hea Htpa Hpa Hhappy Hslow Hweird Hconf Hcpm Hbf Hsl Hcap Hstk Hcpc Hdm]
  · unfold gryffGlobals
    isplitl [Hsl Hcap Hstk]
    · iexists stk
      iframe
      ipureintro
      rw [Hcapv]; decide
    iframe
  unfold bootProph
  iexists p, pvs
  iframe'''


def boot(cmd):
    tbl_path = f'{P}/examples/gryffnet/cmd/{cmd}/PkgTable.lean'
    table = open(os.path.join(ROOT, tbl_path)).read()
    gi = imports(open(os.path.join(ROOT, f'{P}/src/gryff/Init.lean')).read())
    ni = imports(open(os.path.join(ROOT, f'{P}/examples/gryffnet/Init.lean')).read())
    ci = imports(open(os.path.join(ROOT, f'{P}/examples/gryffnet/cmd/{cmd}/Init.lean')).read())
    assert ci == [('gryff.examples.gryffnet', '1')], ci
    assert any(q == 'gryff.src.gryff' for q, _ in ni), ni
    ns = f'gryff.examples.gryffnet.cmd.{cmd}'
    gsteps = '\n'.join(step(q, n, 'wfNo') for q, n in gi)
    nsteps, seen = [], False
    for q, n in ni:
        if q == 'gryff.src.gryff':
            nsteps.append(f'  wp_apply wp_gryff_own $$ Hown as ⟨Hown, #Hd{n}, HR⟩')
            seen = True
        else:
            nsteps.append(step(q, n, 'wf' if seen else 'wfNo'))
    nsteps = '\n'.join(nsteps)
    ind = lambda t: '\n'.join('  ' + l for l in t.splitlines())
    gsteps, nsteps = ind(gsteps), ind(nsteps)
    hyps = '\n'.join(l for l in table.splitlines() if l.startswith('variable [_root_') or l.startswith('variable [package_sem'))
    return f'''/-
A replica node's boot (`cmd/{cmd}`): its program's initialization from a fresh process, keeping
`gryff`'s owned variables and trace prophecy (`Dsverify/Proof/gryff/Boot/Defs.lean`;
notes/dsv-gryff.md, "Package initializers"). Generated by `etc/dsv/_gryff_boot.py` from the program's
`PkgTable.lean` and the generated initializers; do not edit.
-/
module

public import Dsverify.Proof.gryff.examples.gryffnet.cmd.{cmd}.PkgTable
public import Dsverify.Proof.gryff.Boot.Defs

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial
namespace {ns}

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode gryff.boot

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
{hyps}

/-! The program table's facts, for `getIsPkgInit` and for `gNo getIsPkgInit`. -/

{chains(table)}
/-- `gryff`'s initialization, not yet initialized (`ownInitializing (gNo g)`): its fact, its
package variables (`gryffGlobals`) and the trace prophecy its `init()` creates. -/
theorem wp_gryff_own :
    {{{{ ownInitializing (gNo (getIsPkgInit (GF := GF))) }}}}
      (App (Val _root_.Perennial.gryff.src.gryff.initialize') (Val #()))
    {{{{ RET #(); ownInitializing (getIsPkgInit (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff ∗ gryffGlobals ∗ bootProph }}}} := by
  wp_start as Hown
  iapply wp_package_init_gen _ _ _ _ (gNo getIsPkgInit) getIsPkgInit
    (isPkgInit (PROP := IProp GF) pkg_id.gryff.src.gryff)
    iprop(gryffGlobals ∗ bootProph) _ rfl (gNo_no _ _ (by decide)) $$ [Hown]
  · iframe Hown
    iintro Hown
    wp_auto
{ind(GRYFF_ALLOCS)}
{gsteps}
{ind(GRYFF_END)}
  · iintro ⟨Hown, Hpk, HR⟩
    iapply HΦ
    iframe

/-- `gryffnet`'s initialization, not yet initialized, keeping `gryff`'s variables and prophecy. -/
theorem wp_gryffnet_own :
    {{{{ ownInitializing (gNo (getIsPkgInit (GF := GF))) }}}}
      (App (Val _root_.Perennial.gryff.examples.gryffnet.initialize') (Val #()))
    {{{{ RET #(); ownInitializing (getIsPkgInit (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ gryffGlobals ∗ bootProph }}}} := by
  wp_start as Hown
  iapply wp_package_init_gen _ _ _ _ (gNo getIsPkgInit) getIsPkgInit
    (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet)
    iprop(gryffGlobals ∗ bootProph) _ rfl (gNo_no _ _ (by decide)) $$ [Hown]
  · iframe Hown
    iintro Hown
    wp_auto
{nsteps}
    iframe Hown HR
    is_pkg_init_finish
  · iintro ⟨Hown, Hpk, HR⟩
    iapply HΦ
    iframe

/-- **The replica node's boot**: its program's initialization from a fresh process, keeping
`gryff`'s variables and trace prophecy. -/
theorem wp_initialize'_own :
    {{{{ ownGoState ∅ }}}}
      (App (Val initialize') (Val #()))
    {{{{ RET #(); ownInitializing (getIsPkgInit (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.{ns} ∗ gryffGlobals ∗ bootProph }}}} := by
  wp_start as Hgs
  ihave Hown := ownInitializing_empty (gNo (getIsPkgInit (GF := GF))) $$ Hgs
  iapply wp_package_init_gen _ _ _ _ (gNo getIsPkgInit) getIsPkgInit
    (isPkgInit (PROP := IProp GF) pkg_id.{ns})
    iprop(gryffGlobals ∗ bootProph) _ rfl (gNo_no _ _ (by decide)) $$ [Hown]
  · iframe Hown
    iintro Hown
    wp_auto
    wp_apply wp_gryffnet_own $$ Hown as ⟨Hown, #Hd1, HR⟩
    iframe Hown HR
    is_pkg_init_finish
  · iintro ⟨Hown, Hpk, HR⟩
    iapply HΦ
    iframe

end boot

end {ns}
end Perennial
'''


def main(argv):
    check = '--check' in argv
    bad = []
    for cmd in REPLICAS:
        path = os.path.join(ROOT, f'{P}/examples/gryffnet/cmd/{cmd}/Boot.lean')
        txt = boot(cmd)
        old = open(path).read() if os.path.exists(path) else None
        if old == txt:
            continue
        if check:
            bad.append(path)
        else:
            open(path, 'w').write(txt)
            print('wrote', path)
    for b in bad:
        print('_gryff_boot: differs from the generated:', b)
    if bad:
        sys.exit(1)


if __name__ == '__main__':
    main(sys.argv[1:])
