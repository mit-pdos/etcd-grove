/-
Proof of `Spec/demux__broadcastProgressLocked.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__broadcastProgressLocked
public import Spec.go_etcd_io.etcd.cache.v3.watcher__enqueueResponse

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

theorem demuxBPL_delete_none {V : Type} (m : GMap Loc V) (k : Loc) (h : m !! k = none) :
    GMap.delete k m = m := by
  apply GMap.ext; intro k'
  by_cases hk : k = k'
  · subst hk; rw [GMap.lookup_delete, h]
  · rw [GMap.lookup_delete_ne _ hk]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.broadcastProgressLocked.wp_proof
    (wp_enqueueResponse : watcher.enqueueResponse.spec (GF := GF) (hG := hG)) :
    demux.broadcastProgressLocked.spec (GF := GF) (hG := hG) := by
  intro d γd cap c regs views p
  wp_start as ⟨Hl, % ⟨Hinv, Hp, Hp0⟩⟩
  iunfold demuxLocked at Hl
  iNamed Hl
  wp_auto
  ipersist d
  ipersist progressRev
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range_mut (fun (_ : Nat) (m' : GMap Loc w64) => iprop(∃ (x : w64) (y : Loc)
      (views' : GMap Loc View),
      "nextRev" ∷ nextRev_ptr ↦ x ∗
      "w" ∷ w_ptr ↦ y ∗
      "HactF" ∷ demuxActAddr d ↦ actP ∗
      "Hviews" ∷ ghostMapAuth γd.views 1 views' ∗
      "Hres" ∷ ([∗map] w ↦ ri ∈ regs, regRes γd w ri) ∗
      "Hlag" ∷ lagP ↦$ lagOf views' ∗
      "%Hm" ∷ ⌜m' = actOf views'⌝ ∗
      "%Hok" ∷ ⌜RegsOk c c.stream.length regs views'⌝)) $$ Hact
  iintro %keys ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [nextRev w HactF Hviews Hres Hlag]
  · iexists _, _, views
    simp only [named]
    iframe
    ipureintro; exact ⟨trivial, Hok⟩
  isplitr
  · imodintro
    iintro %i %key %nv %m' ⟨%Hkey, %Hnv, %Hagree⟩ HP Hm
    iNamed HP
    subst Hm
    have Hcur : actOf views' !! key = some nv := by
      rw [Hagree i key (Nat.le_refl _) Hkey]; exact Hnv
    rw [actOf_lookup] at Hcur
    obtain ⟨v, Hvw, Hvact, Hvn⟩ : ∃ v, views' !! key = some v ∧ v.phase = .active ∧ v.n = nv := by
      cases h : views' !! key with
      | none => simp [h] at Hcur
      | some v =>
        simp only [h, Option.bind_some] at Hcur
        split at Hcur
        · exact ⟨v, rfl, by assumption, by simpa using Hcur⟩
        · simp at Hcur
    wp_auto
    wp_if_destruct
    · -- `nextRev >= progressRev`: continue
      unfold forMapPostcondition
      ileft
      isplitr
      · ipureintro; rfl
      iexists actOf views'
      iframe Hm
      isplitl
      · iexists _, _, views'
        simp only [named]
        iframe
        ipureintro; first | exact Hok | exact ⟨trivial, Hok⟩
      ipureintro; intro k _; rfl
    -- send a progress notification at `p`
    ihave %Hhnn := typedPointsto_not_null $$ «$v0»
    iStructNamed «$v0»
    ipersist Revision
    -- the watcher's registration
    obtain ⟨ri, Hri⟩ : ∃ ri, regs !! key = some ri := by
      have := Hok.dom key
      rw [Hvw] at this
      cases h : regs !! key with
      | none => simp [h] at this
      | some ri => exact ⟨ri, rfl⟩
    icases (BigSepM.bigSepM_delete (m := regs) Hri).1 $$ Hres with ⟨Hr, Hres⟩
    iNamed Hr
    ihave %Hv := ghost_map_lookup $$ Hviews Hview
    rw [Hvw] at Hv
    cases Hv
    rw [Hvact]
    simp only [RegPhase.toWatcher, watcherAt]
    ihave #Hresp : respAt (GF := GF)
        ({ Header' := «$v0_ptr», Events' := slice.nil, CompactRevision' := 0, Canceled' := false,
           Created' := false, closeErr' := GoInterface.nil, CancelReason' := [] } :
          go_etcd_io.etcd.client.v3.WatchResponse) (progressResp p) $$ []
    · unfold respAt eventsAt hdrAt
      isplitl
      · iexists []
        isplitl
        · iapply ownSlice_nil
        isplitl
        · ipureintro; rfl
        imodintro
        iintro %j %ev %e %Hev
        simp at Hev
      isplitl
      · iright
        isplitl
        · ipureintro; exact Hhnn
        dsimp only [progressResp]
        iexact Revision
      ipureintro
      exact ⟨rfl, rfl, rfl⟩
    wp_apply wp_enqueueResponse key ri.γ pred sent _ (progressResp p) $$ [Hwat] as %ok ⟨%sent', Hwat, %Henq⟩
    · iframe Hwat Hw Hresp
    -- the facts
    have Hmv := Hok.mapped key v Hvw (by rw [Hvact]; rfl)
    have Hup : ∀ b ∈ v.stream, sint.Z (batchRev b) < sint.Z v.n := by
      intro b hb
      have := Hok.active_up key v Hvw Hvact b
      rw [List.take_length] at this
      exact this (Hmv.1 ▸ hb)
    have Hplt : sint.Z p < 2 ^ 63 - 1 := Hp ▸ Hinv.maxRev_lt
    have Hp1 : sint.Z (p + W64 1) = sint.Z p + 1 := by word
    have HvmaxRev : v.maxRev = p := by rw [Hmv.2, Hp]
    have Henq' : enqueueResult pred (progressResp v.maxRev) sent ok sent' := by
      rw [HvmaxRev]; exact Henq
    obtain ⟨HD1, HD2⟩ := Delivered.enqueue_progress (n' := p + W64 1) Hdel
      (by rw [Hvact]; rfl) Hup (by rw [Hp1, Hvn]; omega) (by rw [Hp1, HvmaxRev]; omega) Henq'
    wp_if_destruct
    · -- not sent
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _, views'
        simp only [named]
        iframe
        isplitl [Hres Hview Hwat]
        · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
          iframe Hres
          iunfold regRes
          iexists sent', v, pred
          simp only [named]
          iframe Hw Hpred Hview
          isplitl
          · simp only [Hvact, RegPhase.toWatcher, watcherAt]; iexact Hwat
          ipureintro; exact HD1
        ipureintro; first | exact Hok | exact ⟨trivial, Hok⟩
      ipureintro; intro k _; rfl
    · -- sent: next revision `progressRev + 1`
      imod ghost_map_update { v with n := p + W64 1 } $$ Hviews Hview with ⟨Hviews, Hview⟩
      wp_apply wp_mapInsert $$ Hm as Hm
      unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _
      iframe Hm
      isplitl
      · iexists _, _, GMap.insert key { v with n := p + W64 1 } views'
        simp only [named]
        iframe
        isplitl [Hres Hview Hwat]
        · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
          iframe Hres
          iunfold regRes
          iexists sent', { v with n := p + W64 1 }, pred
          simp only [named]
          iframe Hw Hpred Hview
          isplitl
          · simp only [Hvact, RegPhase.toWatcher, watcherAt]; iexact Hwat
          ipureintro; exact HD2 rfl
        isplitl
        · rw [lagOf_insert]
          simp only [Hvact, reduceCtorEq, ↓reduceIte]
          rw [demuxBPL_delete_none]
          · iexact Hlag
          rw [lagOf_lookup, Hvw]; simp [Hvact]
        ipureintro
        refine ⟨?_, ?_⟩
        · rw [actOf_insert]; simp [Hvact]
        · apply Hok.insert (by rw [Hri]; rfl)
          · intro _; exact Hmv
          · intro _ b hb
            rw [List.take_length] at hb
            have := Hinv.stream_le b hb
            rw [Hp1]; rw [Hp] at Hp1 ⊢; omega
      ipureintro; intro k hk
      exact GMap.lookup_insert_ne _ _ (Ne.symm hk)
  iintro %m' HP Hm
  iNamed HP
  subst Hm
  wp_auto
  iapply HΦ
  iexists views'
  iunfold demuxLocked
  iexists actP, lagP
  simp only [named]
  iframe
  ipureintro; exact Hok

end proof

end EtcdGrove
end Perennial
