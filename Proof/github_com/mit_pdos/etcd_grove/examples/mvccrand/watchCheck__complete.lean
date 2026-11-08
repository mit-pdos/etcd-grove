/- Lean-first (no Rocq counterpart). The proof of `watchCheck.complete`: under `c.mu`, the lock's
watchers at the longer of its history's lower bound and the caller's; the loop over the watchers'
map takes each watcher out of the lock's map (`wats_take`), asks `expect`, and puts it back. -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__complete
public import Spec.github_com.mit_pdos.etcd_grove.examples.mvccrand.watchCheck__expect

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.mvccrand mvcc mvcc.api

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]
variable [mvcc_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem watchCheck.complete.wp_proof
    (wp_expect : watchCheck.expect.spec (GF := GF) (hG := hG)) :
    watchCheck.complete.spec (GF := GF) (hG := hG) := by
  intro c γ h wm Hlb upto hu1 hu2
  wp_start as ⟨Hctx, Hrd, #Hlbc⟩
  iunfold wcCtx at Hctx
  icases Hctx with ⟨#Hpkg, #Hmpkg, #HhF, #HwF, #Hmu, #Hinv, #Hhist, -⟩
  wp_auto
  wp_bind (App (Val wrapDefer) _)
  wp_apply wp_with_defer as %defer defer
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HL⟩
  iunfold cmuInv at HL
  icases HL with ⟨%rs, %W, %Hl, Hwm, Hreg, Hrcv0, #Hlb, %Hknown, Hwats⟩
  ihave %Hcmp := mono_list_lb_valid γ.h.l Hl Hlb $$ Hlb Hlbc
  obtain ⟨Hlx, hpx, hpcx, hx⟩ : ∃ Hlx, Hl <+: Hlx ∧ Hlb <+: Hlx ∧ (Hlx = Hlb ∨ Hlx = Hl) := by
    rcases Hcmp with hc | hc
    · exact ⟨Hlb, hc, List.prefix_refl _, Or.inl rfl⟩
    · exact ⟨Hl, List.prefix_refl _, hc, Or.inr rfl⟩
  ihave #Hlbx : monoListLbOwn γ.h.l Hlx $$ []
  · rcases hx with rfl | rfl
    · iexact Hlbc
    · iexact Hlb
  ihave Hwats := wats_frame (GF := GF) hpx W (rs := rs) (rs' := rs) (fun _ => rfl) $$ Hwats
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List w64) (i : Int) => iprop(∃ (wpv : Loc) (b : Bool),
      "w" ∷ w_ptr ↦ wpv ∗ "«$res0»" ∷ «$res0_ptr» ↦ b ∗ "Hrd" ∷ histRd h γ.h ∗
      "c" ∷ c_ptr ↦ c ∗ "upto" ∷ upto_ptr ↦ upto ∗
      "Hlocked" ∷ sync.ownMutex (cF go!"mu" c) ∗ "Hreg" ∷ ghostMapAuth γ.reg (1 : Qp).half W ∗
      "Hrcv0" ∷ ghostVar γ.rcv (1 : Qp).half rs ∗ "defer" ∷ defer ↦ _ ∗ "HΦ" ∷ (∀ b : Bool, histRd h γ.h -∗ Φ #b) ∗
      "Hwats" ∷ ([∗map] id ↦ x ∈ W, watcherOwn Hlx rs id x.1 x.2))) $$ Hwm
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [w «$res0» Hrd c upto Hwats Hlocked Hreg Hrcv0 defer HΦ]
  · iexists _, _
    iframe
  isplitr
  · imodintro
    iintro %i %key %v ⟨%Hkey, %Hv⟩ HP
    iNamed HP
    rw [GMap.lookup_fmap] at Hv
    obtain ⟨⟨wp, ri⟩, hW, rfl⟩ : ∃ x, W !! key = some x ∧ x.1 = v := by
      cases hW : W !! key with
      | none => rw [hW] at Hv; cases Hv
      | some x => rw [hW] at Hv; exact ⟨x, rfl, Option.some.inj Hv⟩
    icases (wats_take (GF := GF) (List.prefix_refl _) W key (wp, ri) hW
      (rs := rs) (rs' := rs) (fun _ _ => rfl)) $$ Hwats with ⟨Hwo, Hback⟩
    iunfold watcherOwn at Hwo
    icases Hwo with ⟨%wv, Hwp, #Hk, #He, %Hwo⟩
    obtain ⟨hen, hkk, hst1, hst2, hpos⟩ := Hwo
    (try wp_auto)
    wp_apply wp_expect c h γ.h Hlx wp wv ri.1 ri.2.1 upto DFrac.discard (DFrac.own 1)
        DFrac.discard DFrac.discard hpos.1 hpos.2.1 (by have := hpcx.length_le; omega) hu2
      $$ [$HhF $Hwp $Hk $He $Hrd $Hlbx] as %ch %rr %ok ⟨-, Hwp, -, -, Hrd, %Hres⟩
    ihave Hwats := Hback $$ [Hwp]
    · iunfold watcherOwn
      iexists wv
      iframe
      iframe #
      ipureintro
      exact ⟨hen, hkk, hst1, hst2, hpos⟩
    (try wp_auto)
    cases ok
    · (try wp_auto)
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      iframe
    · (try wp_auto)
      unfold forMapPostcondition
      iright; iright; iright
      iexists _
      isplitr
      · ipureintro; rfl
      iintro Hwm
      (try wp_auto)
      wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
        $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats]
      · iunfold cmuInv
        iexists rs, W, Hlx
        iframe
        iframe #
        ipureintro; exact Hknown
      (try wp_auto)
      iapply HΦ
      iframe
  iintro HP Hwm
  iNamed HP
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock (cF go!"mu" c) (cmuInv wm γ)
    $$ [$Hmu $Hlocked Hwm Hreg Hrcv0 Hwats]
  · iunfold cmuInv
    iexists rs, W, Hlx
    iframe
    iframe #
    ipureintro; exact Hknown
  (try wp_auto)
  iapply HΦ
  iframe

end proof

end mvccrand
end EtcdGrove
end Perennial
