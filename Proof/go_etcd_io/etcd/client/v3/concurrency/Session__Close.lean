/-
Proof of `Spec/go_etcd_io/etcd/client/v3/concurrency/Session__Close.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Close
public import Spec.go_etcd_io.etcd.client.v3.concurrency.Session__Orphan

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace concurrency

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.concurrency

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.concurrency.Assumptions]

theorem Session.Close.wp_proof (hO : Session.Orphan.spec (GF := GF) (hG := hG)) :
    Session.Close.spec (GF := GF) (hG := hG) := by
  intro s γ client id
  wp_start as #Hs
  ihave #Hs' := Hs
  iunfold isSession at Hs'
  icases Hs' with ⟨%ops, %o, %octx, %ocs, %ctx, %cs, %cancel, %donec, #HC, #HO, #HI, #Hx, #Hcn,
    #HD, #Hops, %Ho, #Hoctx, #Hctx, #Hcancel, #Hdone, #Hlease⟩
  (try wp_auto)
  wp_apply hO s γ client id $$ [$Hs] as #Hsd
  (try wp_auto)
  obtain ⟨hoc, -⟩ := Ho
  unfold SessionOpts.val
  rw [hoc]
  iStructNamed Hops
  (try wp_auto)
  wp_apply context.wp_WithTimeout $$ [$Hoctx] as %tctx %tγ %tcancel %d ⟨#Htc, #Htctx⟩
  (try wp_auto)
  unfold isEtcdLeaseClient
  icases Hlease with ⟨%l, #Hlf, #Hl⟩
  unfold isEtcdLease
  icases Hl with ⟨-, -, #HRev⟩
  (try wp_auto)
  wp_apply HRev $$ [$Htctx] as %resp %err -
  (try wp_auto)
  wp_apply Htc
  (try wp_auto)
  iapply HΦ
  iexact Hsd

end proof

end concurrency
end EtcdGrove
end Perennial
