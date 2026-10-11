/-
Proof of `Spec/newReady.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newReady.wp_proof : newReady.spec (GF := GF) (hG := hG) := by
  wp_start
  wp_apply chan.wp_make1 (V := Unit) as %ch %γch ⟨#Hch, %_, Hoc⟩
  imod mono_nat_own_alloc (GF := GF) 0 with ⟨%γe, Hauth, #Hlb⟩
  imod alloc_broadcast_chan (E := ⊤) (readyEpochLb (GF := GF) ⟨γe⟩ (0 + 1)) γch ch $$ Hch Hoc
    with Hbc
  wp_alloc r as Hr
  iStructNamed Hr
  imod sync.init_Mutex (readyLockInv (GF := GF) r ⟨γe⟩) ⊤ (readyMuAddr r) $$ mu
    [isReady stateCh Hbc Hauth] with #Hmu
  · inext
    unfold readyLockInv
    iexists false, ch, γch, 0
    simp only [named]
    iframe
    ipureintro; rfl
  wp_auto
  iapply HΦ $$ %r %(ReadyNames.mk γe)
  unfold isReady readyEpochLb
  iframe #

end proof

end EtcdGrove
end Perennial
