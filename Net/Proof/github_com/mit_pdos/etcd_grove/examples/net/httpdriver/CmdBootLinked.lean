/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the commands' boots

Each command's initialization from the machine's empty package state, its first, through
`httpdriver`'s (`BootLinked.lean`, `boot_httpdriver`), at the command's table (`getIsPkgInit`, its
`PkgTable.lean`; `kitG`): it returns the machine's boot resources (`bootRes`). As the dsverify kits'
`BootCmdsLinked.lean` (`etc/dsv/kitgen.py`'s template). A linking module.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.BootLinked
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server.PkgTable
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client.PkgTable

@[expose] public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : Assumptions] [net.FieldAssumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem kitG : github_com.mit_pdos.etcd_grove.examples.net.httpdriver.KitG (getIsPkgInit (GF := GF)) := by
  constructor <;> rfl

set_option maxHeartbeats 4000000 in
/-- **Command `server`'s boot** (see the file header). -/
theorem wp_boot (HEnv : net.http.GodebugHttpmuxgo121Not1) :
    {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing (getIsPkgInit (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server ∗ github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes }} := by
  wp_start as Hgs
  ihave Hown := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server :: github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownedPkgs) (getIsPkgInit (GF := GF))) $$ Hgs
  iapply EtcdGrove.wp_package_init_first (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server)
    (P := isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server) (Q := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes)
    (gA := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server :: github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownedPkgs) (getIsPkgInit (GF := GF)))
    (gB := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownedPkgs (getIsPkgInit (GF := GF))) (gC := getIsPkgInit (GF := GF))
    (hA := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff_off _ _ _ (by decide)) (hAB := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff_sub _ _ _ (by decide)) (heq := rfl)
    $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.net.httpdriver.boot_httpdriver kitG HEnv $$ Hown as ⟨Hown, #Hd, HR⟩
  try wp_auto
  iframe Hown HR
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

end boot

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.server

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : Assumptions] [net.FieldAssumptions]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem kitG : github_com.mit_pdos.etcd_grove.examples.net.httpdriver.KitG (getIsPkgInit (GF := GF)) := by
  constructor <;> rfl

set_option maxHeartbeats 4000000 in
/-- **Command `client`'s boot** (see the file header). -/
theorem wp_boot (HEnv : net.http.GodebugHttpmuxgo121Not1) :
    {{ ownGoState (hG := hG.goose_localGS.goose_go_stateGS) ∅ }}
      (App (Val initialize') (Val #()))
    {{ RET #(); ownInitializing (getIsPkgInit (GF := GF)) ∗
        isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client ∗ github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes }} := by
  wp_start as Hgs
  ihave Hown := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownInitializing_of_empty
    (github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client :: github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownedPkgs) (getIsPkgInit (GF := GF))) $$ Hgs
  iapply EtcdGrove.wp_package_init_first (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client)
    (P := isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client) (Q := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.bootRes)
    (gA := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff (pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client :: github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownedPkgs) (getIsPkgInit (GF := GF)))
    (gB := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ownedPkgs (getIsPkgInit (GF := GF))) (gC := getIsPkgInit (GF := GF))
    (hA := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff_off _ _ _ (by decide)) (hAB := github_com.mit_pdos.etcd_grove.examples.net.httpdriver.gOff_sub _ _ _ (by decide)) (heq := rfl)
    $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  try wp_auto
  wp_apply github_com.mit_pdos.etcd_grove.examples.net.httpdriver.boot_httpdriver kitG HEnv $$ Hown as ⟨Hown, #Hd, HR⟩
  try wp_auto
  iframe Hown HR
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  is_pkg_init_finish

end boot

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver.cmd.client

end Perennial
