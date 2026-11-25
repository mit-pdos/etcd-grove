#!/usr/bin/env python3
"""The gryff kit's server boots (notes/dsv-gryff.md, "Package initializers"): for each server
command (`cmd/server{1,2,3,4}`), `Dsverify/Proof/gryff/examples/gryffnet/cmd/<cmd>/Boot.lean`, its
initialization from a fresh process keeping `gryff`'s owned variables and trace prophecy and what
net/http's and net/rpc's first initializations leave on the machine (`Boot/Defs.lean`'s
`wp_http_own`, `wp_rpc_own`, over Net's `wp_init_first`: `serverBoot`), owned, through `serverlib`'s initialization, the first to import them
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
REPLICAS = ['server1', 'server2', 'server3', 'server4']
NO = {'gryff.src.gryff', 'gryff.examples.gryffnet'}
# the excluded sets: `gNo` (NO and the commands), `gEx noPkgsS2` (+ serverlib), `S1` (+ net/rpc),
# `S0` (+ net/http)
SETS = {
    'wfNo': ('gNo (getIsPkgInit (GF := GF))', '· rw [gNo_ne _ _ (by decide)]; rfl', set()),
    'wfS2': ('gEx noPkgsS2 (getIsPkgInit (GF := GF))', '· rw [gEx_ne _ _ _ (by decide)]; rfl',
             {'gryff.src.serverlib'}),
    'wfS1': ('gEx noPkgsS1 (getIsPkgInit (GF := GF))', '· rw [gEx_ne _ _ _ (by decide)]; rfl',
             {'gryff.src.serverlib', 'net.rpc'}),
    'wfS0': ('gEx noPkgsS0 (getIsPkgInit (GF := GF))', '· rw [gEx_ne _ _ _ (by decide)]; rfl',
             {'gryff.src.serverlib', 'net.rpc', 'net.http'}),
}


def wfname(pkg):
    return pkg.replace('«', '').replace('»', '').replace('.', '_')


def chains(table):
    """The table's facts as top-level theorems, for `g` (`wf_`) and for each excluded set's
    table (`wfNo_`, `wfS2_`, `wfS1_`, `wfS0_`): a package is skipped if it is excluded or one of
    its facts' imports is skipped."""
    blocks = re.findall(r'  have (h\d+) : GetIsPkgInitProp pkg_id\.(\S+) \(getIsPkgInit \(GF := GF\)\) := by\n'
                        r'    refine And\.intro \?_ \?_\n    · rfl\n    exact (.*)\n', table)
    names = {h: q for h, q, _ in blocks}
    out = []
    kinds = [('wf', 'getIsPkgInit (GF := GF)', '· rfl', None)] + \
        [(k, g, hd, ex) for k, (g, hd, ex) in SETS.items()]
    for kind, g, head, extra in kinds:
        skipped = set()
        for h, q, ex in blocks:
            if extra is not None:
                deps = set(re.findall(r'\bh\d+\b', ex))
                if (q in NO or q in extra or q.startswith('gryff.examples.gryffnet.cmd.')
                        or deps & skipped):
                    skipped.add(h)
                    continue
            ex = re.sub(r'\bh\d+\b', lambda m: f'{kind}_{wfname(names[m.group(0)])}', ex)
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
    si = imports(open(os.path.join(ROOT, f'{P}/src/serverlib/Init.lean')).read())
    ni = imports(open(os.path.join(ROOT, f'{P}/examples/gryffnet/Init.lean')).read())
    ci = imports(open(os.path.join(ROOT, f'{P}/examples/gryffnet/cmd/{cmd}/Init.lean')).read())
    assert ci == [('gryff.examples.gryffnet', '1')], ci
    order = [q for q, _ in ni]
    assert 'gryff.src.serverlib' in order and 'gryff.src.gryff' in order, ni
    assert order.index('gryff.src.serverlib') < order.index('gryff.src.gryff'), ni
    # nothing before serverlib in gryffnet's chain initializes net/http or net/rpc
    assert not {'net.http', 'net.rpc'} & set(order[:order.index('gryff.src.serverlib')]), ni
    sq = [q for q, _ in si]
    assert sq.index('net.http') < sq.index('net.rpc'), si
    ns = f'gryff.examples.gryffnet.cmd.{cmd}'
    gsteps = '\n'.join(step(q, n, 'wfNo') for q, n in gi)
    ssteps, kind = [], 'wfS0'
    for q, n in si:
        if q == 'net.http':
            ssteps.append(f'  wp_apply (wp_http_own hT noPkgsS0 noPkgsS1 rfl _ wfS1_net_http) $$ Hown\n'
                          f'    as ⟨Hown, #Hd{n}, HH⟩')
            kind = 'wfS1'
        elif q == 'net.rpc':
            ssteps.append(f'  wp_apply (wp_rpc_own wp_NewServer noPkgsS1 noPkgsS2 rfl _ wfS2_net_rpc) $$ Hown\n'
                          f'    as ⟨Hown, #Hd{n}, HRp⟩')
            kind = 'wfS2'
        else:
            ssteps.append(step(q, n, kind))
    ssteps = '\n'.join(ssteps)
    nsteps, kind = [], 'wfS0'
    for q, n in ni:
        if q == 'gryff.src.serverlib':
            nsteps.append(f'  wp_apply (wp_serverlib_own hT wp_NewServer) $$ Hown as ⟨Hown, #Hd{n}, HB⟩')
            kind = 'wfNo'
        elif q == 'gryff.src.gryff':
            nsteps.append(f'  wp_apply wp_gryff_own $$ Hown as ⟨Hown, #Hd{n}, HG, HPr⟩')
            kind = 'wf'
        else:
            nsteps.append(step(q, n, kind))
    nsteps = '\n'.join(nsteps)
    ind = lambda t: '\n'.join('  ' + l for l in t.splitlines())
    gsteps, nsteps, ssteps = ind(gsteps), ind(nsteps), ind(ssteps)
    hyps = '\n'.join(l for l in table.splitlines() if l.startswith('variable [_root_') or l.startswith('variable [package_sem'))
    return TEMPLATE.format(cmd=cmd, ns=ns, hyps=hyps, chains=chains(table),
                           allocs=ind(GRYFF_ALLOCS), gsteps=gsteps, gend=ind(GRYFF_END),
                           ssteps=ssteps, nsteps=nsteps)


TEMPLATE = '''/-
Server machine `{cmd}`'s boot (`cmd/{cmd}`): its program's initialization from a fresh process,
keeping `gryff`'s owned variables and trace prophecy and what net/http's and net/rpc's
first initializations leave on the machine (`serverBoot`, Net's `wp_init_first`), owned, through
`serverlib`'s initialization (`Dsverify/Proof/gryff/Boot/Defs.lean`; notes/dsv-gryff.md, "Package
initializers"). Generated by `etc/dsv/_gryff_boot.py` from the program's `PkgTable.lean` and the
generated initializers; do not edit.
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

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net gryff.boot Perennial.gryff

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {{GF : BundledGFunctors}} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
{hyps}
variable [net.rpc.Assumptions] [net.http.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable (hT : threadBound GF ≤ 2 ^ 30)
variable (wp_NewServer : net.rpc.NewServer.spec_owned (GF := GF) (hG := hG))

/-! The program table's facts, for `getIsPkgInit` and for the excluded sets' tables. -/

{chains}
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
{allocs}
{gsteps}
{gend}
  · iintro ⟨Hown, Hpk, HR⟩
    iapply HΦ
    iframe

include hT wp_NewServer in
/-- `serverlib`'s initialization, with neither it nor net/http nor net/rpc initialized
(`gEx noPkgsS0`): net/http's and net/rpc's initializations are the first (Net's
`wp_init_first`, on a machine of at most `2 ^ 30` threads), and leave the machine's `serverBoot`. -/
theorem wp_serverlib_own :
    {{{{ ownInitializing (gEx noPkgsS0 (getIsPkgInit (GF := GF))) }}}}
      (App (Val _root_.Perennial.gryff.src.serverlib.initialize') (Val #()))
    {{{{ RET #(); ownInitializing (gNo (getIsPkgInit (GF := GF))) ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.src.serverlib ∗ serverBoot (GF := GF) }}}} := by
  wp_start as Hown
  iapply wp_package_init_gen _ _ _ _ (gEx noPkgsS0 getIsPkgInit) (gNo getIsPkgInit)
    (isPkgInit (PROP := IProp GF) pkg_id.gryff.src.serverlib)
    (serverBoot (GF := GF)) _ (by rw [gNo_ne _ _ (by decide)]; rfl)
    (gEx_no _ _ _ (by decide)) $$ [Hown]
  · iframe Hown
    iintro Hown
    wp_auto
{ssteps}
    ihave Hown := ownInitializing_weaken _ _ (gEx_S2_le _) $$ Hown
    unfold serverBoot
    iframe Hown HH HRp
    is_pkg_init_finish
  · iintro ⟨Hown, Hpk, HR⟩
    iapply HΦ
    iframe

include hT wp_NewServer in
/-- `gryffnet`'s initialization, not yet initialized, keeping `gryff`'s variables and prophecy
and the machine's `serverBoot`. -/
theorem wp_gryffnet_own :
    {{{{ ownInitializing (gEx noPkgsS0 (getIsPkgInit (GF := GF))) }}}}
      (App (Val _root_.Perennial.gryff.examples.gryffnet.initialize') (Val #()))
    {{{{ RET #(); ownInitializing (getIsPkgInit (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet ∗ gryffGlobals ∗ bootProph ∗
        serverBoot (GF := GF) }}}} := by
  wp_start as Hown
  iapply wp_package_init_gen _ _ _ _ (gEx noPkgsS0 getIsPkgInit) getIsPkgInit
    (isPkgInit (PROP := IProp GF) pkg_id.gryff.examples.gryffnet)
    iprop(gryffGlobals ∗ bootProph ∗ serverBoot (GF := GF)) _ rfl (gEx_no _ _ _ (by decide)) $$ [Hown]
  · iframe Hown
    iintro Hown
    wp_auto
{nsteps}
    iframe Hown HG HPr HB
    is_pkg_init_finish
  · iintro ⟨Hown, Hpk, HR⟩
    iapply HΦ
    iframe

include hT wp_NewServer in
/-- **The server machine's boot**: its program's initialization from a fresh process, keeping
`gryff`'s variables and trace prophecy and the machine's `serverBoot`. -/
theorem wp_initialize'_own :
    {{{{ ownGoState ∅ }}}}
      (App (Val initialize') (Val #()))
    {{{{ RET #(); ownInitializing (getIsPkgInit (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.{ns} ∗ gryffGlobals ∗ bootProph ∗
        serverBoot (GF := GF) }}}} := by
  wp_start as Hgs
  ihave Hown := ownInitializing_empty (gEx noPkgsS0 (getIsPkgInit (GF := GF))) $$ Hgs
  iapply wp_package_init_gen _ _ _ _ (gEx noPkgsS0 getIsPkgInit) getIsPkgInit
    (isPkgInit (PROP := IProp GF) pkg_id.{ns})
    iprop(gryffGlobals ∗ bootProph ∗ serverBoot (GF := GF)) _ rfl (gEx_no _ _ _ (by decide)) $$ [Hown]
  · iframe Hown
    iintro Hown
    wp_auto
    wp_apply (wp_gryffnet_own hT wp_NewServer) $$ Hown as ⟨Hown, #Hd1, HR⟩
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
