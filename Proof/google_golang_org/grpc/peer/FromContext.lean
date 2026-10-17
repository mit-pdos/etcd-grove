/-
Proof of `Spec/google_golang_org/grpc/peer/FromContext.lean` (PR etcd#22259). Lean-first (no Rocq
counterpart).
-/
module

public import Spec.google_golang_org.grpc.peer.FromContext

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [peer_sem : google_golang_org.grpc.peer.Assumptions]

theorem peer.FromContext.wp_proof : peer.FromContext.spec (GF := GF) (hG := hG) := by
  intro ci o
  wp_start as #Hpeer
  wp_auto
  wp_bind (App (Val #(methods ci.ty go!"Value" ci.v)) _)
  iunfold grpcRunPeerIs at Hpeer
  iapply Hpeer
  inext
  iintro %v Hv
  cases o with
  | none =>
    icases Hv with %Hv
    subst Hv
    wp_auto
    iapply HΦ
    ipureintro; rfl
  | some s =>
    icases Hv with ⟨%p, ⟨%Hv, %Hpn⟩, #Hpi⟩
    subst Hv
    wp_auto
    iapply HΦ
    dsimp only
    iframe Hpi
    ipureintro; exact ⟨rfl, Hpn⟩

end proof

end EtcdGrove
end Perennial
