/-
`Main`'s callees linked (`notes/etcd-unified-scope.md` §3.3), by hand as `k8s_all`'s `MainLinked.lean`:
`etcd_all.Main.wp_proof` applied to `spawn`'s proof (over `holdToken`'s), the four parts' proofs and,
under them, the eleven drivers' linked `Main` results (`etcd_txnlinfaultsN.wp_Main`,
`etcd_partition.wp_MainWatch`, `etcd_compactwatch.wp_Main`, `etcd_compacted.wp_Main`,
`etcd_cache.wp_Main`, `etcd_authN.wp_Main`, `etcd_authlease.wp_Main`, `etcd_leaseN.wp_Main`,
`etcd_leasecatchup.wp_Main`, `etcd_restartN.wp_Main`, `etcd_restart1.wp_Main`); and `MainChecked`'s
(the program's entry point since the pure-premises plan's P4, 2026-11-24) over `Main`'s, `ParamsOk`'s
(over `mulBelow`'s) and `cluster3`'s `RandomSchedule`. `Results.lean` restates them.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.MainChecked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.ParamsOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.mulBelow
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.KV
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Auth
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Lease
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.Restart
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.spawn
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.all.holdToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.compacted.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authN.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.authlease.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup.MainLinked
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

/-- **The KV part** (`KV.lean`), over its five drivers' linked results. -/
theorem etcd_all.wp_KV [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_all.KV.spec (GF := GF) (hG := hG) :=
  etcd_all.KV.wp_proof etcd_all.wp_spawn etcd_txnlinfaultsN.wp_Main etcd_partition.wp_MainWatch
    etcd_compactwatch.wp_Main etcd_compacted.wp_Main etcd_cache.wp_Main

/-- **The Auth part** (`Auth.lean`), over its two drivers' linked results. -/
theorem etcd_all.wp_Auth [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_all.Auth.spec (GF := GF) (hG := hG) :=
  etcd_all.Auth.wp_proof etcd_all.wp_spawn etcd_authN.wp_Main etcd_authlease.wp_Main

/-- **The Lease part** (`Lease.lean`), over its two drivers' linked results. -/
theorem etcd_all.wp_Lease [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_all.Lease.spec (GF := GF) (hG := hG) :=
  etcd_all.Lease.wp_proof etcd_all.wp_spawn etcd_leaseN.wp_Main etcd_leasecatchup.wp_Main

/-- **The Restart part** (`Restart.lean`), over its two drivers' linked results. -/
theorem etcd_all.wp_Restart [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] : etcd_all.Restart.spec (GF := GF) (hG := hG) :=
  etcd_all.Restart.wp_proof etcd_all.wp_spawn etcd_restartN.wp_Main etcd_restart1.wp_Main

/-- **The one closed etcd theorem's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/Main.lean`), under the semantic premises of the
eleven drivers' linked results. -/
theorem etcd_all.wp_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_all.Main.spec (GF := GF) (hG := hG) :=
  etcd_all.Main.wp_proof etcd_all.wp_spawn etcd_all.wp_KV etcd_all.wp_Auth etcd_all.wp_Lease
    etcd_all.wp_Restart

/-- **`mulBelow`** (`mulBelow.lean`). -/
theorem etcd_all.wp_mulBelow : etcd_all.mulBelow.spec (GF := GF) (hG := hG) :=
  etcd_all.mulBelow.wp_proof

/-- **`ParamsOk`** (`ParamsOk.lean`), over `mulBelow`'s proof. -/
theorem etcd_all.wp_ParamsOk : etcd_all.ParamsOk.spec (GF := GF) (hG := hG) :=
  etcd_all.ParamsOk.wp_proof etcd_all.wp_mulBelow

/-- **The program's entry point does not panic** (`MainChecked.lean`): `Main`'s linked triple behind
`ParamsOk`, with the schedules `cluster3.RandomSchedule` draws. -/
theorem etcd_all.wp_MainChecked [_root_.Perennial.net.FieldAssumptions]
    [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    etcd_all.MainChecked.spec (GF := GF) (hG := hG) :=
  etcd_all.MainChecked.wp_proof etcd_all.wp_ParamsOk cluster3.wp_RandomSchedule etcd_all.wp_Main

end results

end EtcdGrove
end Perennial
