/-
Proof of `Spec/newWatcher.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.newWatcher

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem newWatcher.wp_proof : newWatcher.spec (GF := GF) (hG := hG) := by
  intro bufSize f pred
  wp_start as ⟨%Hbuf, #Hpred⟩
  wp_auto
  wp_apply chan.wp_make2 (V := go_etcd_io.etcd.client.v3.WatchResponse) bufSize as
    %ch %γch ⟨#Hch, %Hcap, Hoc⟩
  · ipureintro; exact Hbuf
  wp_alloc w as Hw
  iStructNamed Hw
  ipersist respCh
  ipersist keyPred
  imod ghostVar_alloc (GF := GF) ([] : List RespModel) with ⟨%γs, Hs⟩
  icases ghostVar_split γs ([] : List RespModel) (1 : Qp).half (1 : Qp).half $$ [Hs] with ⟨Hs1, Hs2⟩
  · rw [Qp.half_add_half]; iexact Hs
  imod ghostVar_alloc (GF := GF) ([] : List RespModel) with ⟨%γr, Hr⟩
  icases ghostVar_split γr ([] : List RespModel) (1 : Qp).half (1 : Qp).half $$ [Hr] with ⟨Hr1, Hr2⟩
  · rw [Qp.half_add_half]; iexact Hr
  imod dghostVar_alloc (GF := GF) (none : Option (List RespModel × Option w64)) with ⟨%γc, Hc⟩
  icases dghostVar_split γc (none : Option (List RespModel × Option w64)) (.own (1 : Qp).half)
    (.own (1 : Qp).half) $$ [Hc] with ⟨Hc1, Hc2⟩
  · rw [DFrac.op_own, Qp.half_add_half]; iexact Hc
  imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
  imod inv_alloc watcherN ⊤ (watcherInv (hG := hG) w ⟨γch, γs, γr, γc, γt⟩) $$ [Hoc Hs2 Hr2 Hc2] with #Hinv
  · inext
    unfold watcherInv
    iexists (if bufSize = W64 0 then ChanState.Idle else ChanState.Buffered []), [], [], [], none
    simp only [named]
    iframe
    isplitr
    · ipureintro; exact List.prefix_refl _
    isplitr
    · ipureintro; split <;> rfl
    isplitr
    · ipureintro; split <;> rfl
    isplitr
    · simp only [List.length_nil, List.drop_zero]; iapply respsSent_nil
    unfold watcherInvClosed
    iexact Hc2
  imod sync.init_Once (watcherStopOnceAddr w) (watcherOnceP (hG := hG) w ⟨γch, γs, γr, γc, γt⟩)
    iprop(∃ sc c, watcherClosed (GF := GF) ⟨γch, γs, γr, γc, γt⟩ sc c) ⊤ $$ [stopOnce cancelResp Htok]
    with #Honce
  · unfold watcherOnceP; iframe
  wp_auto
  iapply HΦ $$ %w %(WatcherNames.mk γch γs γr γc γt)
  unfold isWatcher watcherOpen watcherConsumer
  iframe
  iexists ch, f
  simp only [named]
  iframe #

end proof

end EtcdGrove
end Perennial
