module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__EstimatedWritePageSize
public import Proof.go_etcd_io.bbolt.internal.freelist.Lemmas
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Count

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt.internal.freelist

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.internal.freelist.Assumptions]

theorem shared.EstimatedWritePageSize.wp_proof (hCount : shared.Count.spec (GF := GF) (hG := hG)) :
    shared.EstimatedWritePageSize.spec (GF := GF) (hG := hG) := by
  intro I s σ hFC
  wp_start as ⟨Hsh, Hown⟩
  icases ownShared_wf _ _ _ $$ Hsh with ⟨Hsh, %Hwf⟩
  have Hlen : σ.allIds.length < 2 ^ 63 := Hwf.2.2.2.1
  wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"Count" #s)) (Val #()))
  iapply (hCount I s σ hFC) $$ [Hsh Hown]
  · iframe; iexact Hpkg
  inext
  iintro ⟨Hsh, Hown⟩
  have Hc : (σ.free.length + σ.pendingCount : Nat) = σ.allIds.length := by
    unfold FLState.allIds FLState.pendingCount; rw [List.length_append]
  rw [Hc]
  try wp_auto
  wp_if_destruct
  · try wp_auto
    rw [if_pos (by word)]
    rw [show W64 16 + W64 8 * (W64 (σ.allIds.length : Int) + W64 1) =
      W64 (16 + 8 * ((σ.allIds.length + 1 : Nat) : Int)) by word]
    iapply HΦ; iframe
  · try wp_auto
    rw [if_neg (by word)]
    rw [show W64 16 + W64 8 * W64 (σ.allIds.length : Int) =
      W64 (16 + 8 * ((σ.allIds.length : Nat) : Int)) by word]
    iapply HΦ; iframe

end proof

end bbolt
end EtcdGrove
end Perennial
