/-
`Main`'s callees linked (`notes/etcd-unified-scope.md` §3.3), by hand as `k8s_all`'s `MainLinked.lean`:
`etcd_all.Main.wp_proof` applied to the restart part's proof, itself over `spawn`'s proof (over
`holdToken`'s) and the two drivers' linked `Main` results (`etcd_restartN.wp_Main`,
`etcd_restart1.wp_Main`); and `MainChecked`'s (the program's entry point since the pure-premises
plan's P4, 2026-11-24) over `Main`'s and `ParamsOk`'s. `Results.lean` restates them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.ParamsOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Restart
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.spawn
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.holdToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restartN.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.MainLinked

@[expose] public section

set_option pp.fullNames true

set_option linter.unusedSectionVars false

set_option synthInstance.maxSize 4096

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial

namespace EtcdGrove

open Iris Iris.BI

section results
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]
variable [NaInvG GF]

/-- **`spawn`** (`spawn.lean`), over `holdToken`'s proof. -/
theorem etcd_all.wp_spawn : etcd_all.spawn.spec (GF := GF) (hG := hG) :=
  etcd_all.spawn.wp_proof etcd_all.holdToken.wp_proof

/-- **The Restart part** (`Restart.lean`), over its two drivers' linked results. -/
theorem etcd_all.wp_Restart
    : etcd_all.Restart.spec (GF := GF) (hG := hG) :=
  etcd_all.Restart.wp_proof etcd_all.wp_spawn etcd_restartN.wp_Main etcd_restart1.wp_Main

/-- **The single-process theorem's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/Main.lean`), under the semantic premises of the
two drivers' linked results. -/
theorem etcd_all.wp_Main :
    etcd_all.Main.spec (GF := GF) (hG := hG) :=
  etcd_all.Main.wp_proof etcd_all.wp_Restart

/-- **`ParamsOk`** (`ParamsOk.lean`). -/
theorem etcd_all.wp_ParamsOk : etcd_all.ParamsOk.spec (GF := GF) (hG := hG) :=
  etcd_all.ParamsOk.wp_proof

/-- **The program's entry point does not panic** (`MainChecked.lean`): `Main`'s linked triple behind
`ParamsOk`. -/
theorem etcd_all.wp_MainChecked :
    etcd_all.MainChecked.spec (GF := GF) (hG := hG) :=
  etcd_all.MainChecked.wp_proof etcd_all.wp_ParamsOk etcd_all.wp_Main

end results

end EtcdGrove
end Perennial
