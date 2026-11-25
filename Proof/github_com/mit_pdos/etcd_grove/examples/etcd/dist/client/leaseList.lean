/-
Proof of `leaseList.spec`: the request timeout's context, `cli.Lease.Leases` at the member at another
machine (the draft `etcd_dist.Client_LeaseLeases_dist`), the cancel.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseList
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.ClientLeaseLeasesDist
public import Perennial.Spec.context.Background
public import Spec.context.WithTimeoutBackground
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [client_sem : go_etcd_io.etcd.client.v3.Assumptions]
variable [esrv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

set_option maxHeartbeats 800000 in
theorem leaseList.wp_proof
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Leases_dist : etcd_dist.Client_LeaseLeases_dist.spec (GF := GF) (hG := hG)) :
    leaseList.spec (GF := GF) (hG := hG) := by
  intro π cl ep V γE mid hAs
  wp_start as ⟨#Hnc, #Hnp, #Haddr⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Hnc' := Hnc
  iunfold isNewClient at Hnc'
  icases Hnc' with ⟨-, -, -, -, ⟨%lp, #Hlf, -⟩, -⟩
  (try wp_auto)
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
  (try wp_auto)
  wp_apply (wp_Leases_dist cl lp ep V γE mid ctx cd) $$ [] as %resp %err Hres
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  iapply HΦ
  iexact Hres

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
