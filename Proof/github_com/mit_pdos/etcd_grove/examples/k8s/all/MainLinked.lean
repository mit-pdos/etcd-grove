/-
`Main`'s callees linked (`notes/k8s-unified-scope.md`), by hand as the compactor's `MainLinked.lean`:
`k8s_all.Main.wp_proof` applied to `holdToken`'s proof and to the two drivers' linked `MainPartition`
results (`k8s_etcd3.wp_MainPartition`, `k8s_compactor.wp_MainPartition`, the latter under the named
hypothesis of `clock.RealClock.After`). `Results.lean` restates it.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.Main
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.MainChecked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.ParamsOk
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.mulBelow
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Link
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.all.holdToken
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainLinked
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainLinked

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
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]
variable [NaInvG GF]
variable [ctxDescs : EtcdGrove.ContextReadErrs (GF := GF) (hG := hG)]
variable (h_After : EtcdGrove.clock.RealClock.After.spec (GF := GF) (hG := hG))

include h_After in
/-- **The one closed Kubernetes theorem's `Main` does not panic** (see the file header;
`Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/Main.lean`), under the semantic premises of the
two drivers' linked `MainPartition` results and the named hypothesis of `clock.RealClock.After`. -/
theorem k8s_all.wp_Main [_root_.Perennial.net.FieldAssumptions]
    [os.file.FieldAssumptions] [os.fileStat.FieldAssumptions] [go_etcd_io.etcd.cache.v3.Assumptions]
    [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    k8s_all.Main.spec (GF := GF) (hG := hG) :=
  k8s_all.Main.wp_proof k8s_all.holdToken.wp_proof k8s_etcd3.wp_MainPartition
    (k8s_compactor.wp_MainPartition h_After)

/-- **`mulBelow`** (`mulBelow.lean`). -/
theorem k8s_all.wp_mulBelow : k8s_all.mulBelow.spec (GF := GF) (hG := hG) :=
  k8s_all.mulBelow.wp_proof

/-- **`ParamsOk`** (`ParamsOk.lean`), over `mulBelow`'s proof. -/
theorem k8s_all.wp_ParamsOk : k8s_all.ParamsOk.spec (GF := GF) (hG := hG) :=
  k8s_all.ParamsOk.wp_proof k8s_all.wp_mulBelow

include h_After in
/-- **The program's entry point does not panic** (`MainChecked.lean`; the pure-premises plan's P5,
2026-11-24): `Main`'s linked triple behind `ParamsOk`, with the schedules `cluster3.RandomSchedule`
draws. -/
theorem k8s_all.wp_MainChecked [_root_.Perennial.net.FieldAssumptions]
    [go_etcd_io.etcd.cache.v3.Assumptions] [go_etcd_io.etcd.client.v3.DialWithBalancerBody] :
    k8s_all.MainChecked.spec (GF := GF) (hG := hG) :=
  k8s_all.MainChecked.wp_proof k8s_all.wp_ParamsOk cluster3.wp_RandomSchedule
    (k8s_all.wp_Main h_After)

end results

end EtcdGrove
end Perennial
