/-
Proofs of `leaseList.spec`/`specLive`/`specGranted`: the request timeout's context, `cli.Lease.Leases` at
the member at another machine (the drafts `etcd_dist.view.Client_LeaseLeases_dist`, `Lease_LeasesLive_dist`,
`Lease_LeasesGranted_dist`), the cancel.
Lean-first (no Rocq counterpart); #50 N9b (`notes/etcd-dist-n9b.md`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.leaseList
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
open etcd_dist etcd_dist.view

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
    (wp_Leases_dist : Client_LeaseLeases_dist.spec (GF := GF) (hG := hG)) :
    leaseList.spec (GF := GF) (hG := hG) := by
  intro π cl ep V Γ mid hAs
  wp_start as ⟨Hlt, #Hmc⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  icases leaseClientV_of_memberCli cl ep V Γ mid $$ Hmc with ⟨%lp, #Hlc⟩
  ihave #Hlc' := Hlc
  iunfold leaseClientAt at Hlc'
  icases Hlc' with ⟨-, -, #Hlf, -⟩
  (try wp_auto)
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
  (try wp_auto)
  wp_apply (wp_Leases_dist cl lp ep V Γ mid ctx cd) $$ [$Hlt] as %resp %err ⟨Hlt, Hres⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  iapply HΦ
  iframe Hlt
  iexact Hres

set_option maxHeartbeats 800000 in
theorem leaseList.wp_proofLive
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Leases_dist : Lease_LeasesLive_dist.spec (GF := GF) (hG := hG)) :
    leaseList.specLive (GF := GF) (hG := hG) := by
  intro π cl ep V Γ mid n hAs hlm hinj
  wp_start as ⟨Hlt, #Hmc, #HG⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  icases leaseClientV_of_memberCli cl ep V Γ mid $$ Hmc with ⟨%lp, #Hlc⟩
  ihave #Hlc' := Hlc
  iunfold leaseClientAt at Hlc'
  icases Hlc' with ⟨-, -, #Hlf, -⟩
  (try wp_auto)
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
  (try wp_auto)
  wp_apply (wp_Leases_dist cl lp ep V Γ mid ctx cd n hlm hinj) $$ [$Hlt] as %resp %err ⟨Hlt, Hres⟩
  · iframe #
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  iapply HΦ
  iframe Hlt
  iexact Hres

set_option maxHeartbeats 800000 in
theorem leaseList.wp_proofGranted
    (wp_Background : context.Background.spec (GF := GF) (hG := hG))
    (hWT : context.WithTimeoutBackground.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Leases_dist : Lease_LeasesGranted_dist.spec (GF := GF) (hG := hG)) :
    leaseList.specGranted (GF := GF) (hG := hG) := by
  intro π cl ep V Γ mid G hAs hlm hinj
  wp_start as ⟨Hlt, #Hmc, HG⟩
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  icases leaseClientV_of_memberCli cl ep V Γ mid $$ Hmc with ⟨%lp, #Hlc⟩
  ihave #Hlc' := Hlc
  iunfold leaseClientAt at Hlc'
  icases Hlc' with ⟨-, -, #Hlf, -⟩
  (try wp_auto)
  wp_apply wp_Background
  (try wp_auto)
  wp_apply (client.wp_WithTimeout_bg hWT wp_ErrAny hAs _) $$ []
    as %ctx %cd %cancel ⟨#Hcancel, #Hctx, #Hce, -⟩
  (try wp_auto)
  wp_apply (wp_Leases_dist cl lp ep V Γ mid ctx cd G hlm hinj) $$ [$Hlt HG] as %resp %err ⟨Hlt, Hres⟩
  · iframe #; iexact HG
  (try wp_auto)
  wp_apply Hcancel
  (try wp_auto)
  iapply HΦ
  iframe Hlt
  iexact Hres

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
