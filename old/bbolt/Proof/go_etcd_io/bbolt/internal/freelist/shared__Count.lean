module
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__Count
public import Spec.go_etcd_io.bbolt.internal.freelist.shared__PendingCount

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

theorem shared.Count.wp_proof (hPC : shared.PendingCount.spec (GF := GF) (hG := hG)) :
    shared.Count.spec (GF := GF) (hG := hG) := by
  intro I s σ hFC
  wp_start as ⟨Hs, Hown⟩
  unfold ownShared ownSharedC
  icases Hs with ⟨%sv, %c, Hs, %Hok⟩
  iNamed Hs
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  rw [Hiface]
  unfold FLImpl.iface
  wp_auto
  wp_bind (App (Val #(methods I.ity go!"FreeCount" I.iv)) (Val #()))
  iapply (hFC s σ.free) $$ Hown
  inext
  iintro Hown
  ihave Hsh : ownShared s (interface.mkOk I.ity I.iv) σ $$
      [Hs Hro Hro_cap Hallocs Hcache Hpending Hpds]
  · unfold ownShared ownSharedC
    iexists sv, c
    iframe
    ipureintro; exact ⟨Hiface, Hok⟩
  wp_auto
  wp_bind (App (Val #(methods (go.GoType.PointerType shared.ty) go!"PendingCount" #s)) (Val #()))
  iapply (hPC s _ σ) $$ [Hsh]
  · iframe Hsh; iexact Hpkg
  inext
  iintro Hsh
  try wp_auto
  rw [show (W64 (σ.free.length : Int) + W64 (σ.pendingCount : Int) : w64) =
    W64 ((σ.free.length + σ.pendingCount : Nat) : Int) by word]
  unfold ownShared ownSharedC
  iapply HΦ
  iframe

end proof

end bbolt
end EtcdGrove
end Perennial
