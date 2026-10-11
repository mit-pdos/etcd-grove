/-
Proof of `Spec/demux__Register.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__Register

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- The new registration's start condition (`RegsStart.register`): an active one starts from
now with nothing there yet (`s = 0`) or above `maxRev ≥ base`; a lagging one at its start. -/
theorem register_startOk {cap : Nat} {c : DemuxCore} (hinv : DemuxInv cap c) (startingRev : w64)
    (γ : WatcherNames) (pn : GName) (ph : RegPhase)
    (Hph : ph = (if c.maxRev = W64 0 then
      (if startingRev = W64 0 then RegPhase.active else RegPhase.lagging)
    else (if sint.Z (resolveStart startingRev c.maxRev) ≤ sint.Z c.maxRev then RegPhase.lagging
      else RegPhase.active))) :
    StartOk c (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev)
      (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) := by
  unfold StartOk
  cases ph with
  | lagging => exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  | closed c0 =>
    exfalso; revert Hph; split <;> split <;> simp
  | active =>
    by_cases hM : c.maxRev = W64 0
    · rw [ite_eq_left hM] at Hph
      by_cases hs : startingRev = W64 0
      · left; simp [resolveStart, hs, hM]
      · rw [ite_eq_right hs] at Hph; cases Hph
    · rw [ite_eq_right hM] at Hph
      by_cases hle : sint.Z (resolveStart startingRev c.maxRev) ≤ sint.Z c.maxRev
      · rw [ite_eq_left hle] at Hph; cases Hph
      · right; left
        simp only
        refine ⟨fun h0 => hM (hinv.uninit h0).2, ?_⟩
        have := hinv.base_maxRev hM
        omega

theorem resolveStart_sr (startingRev M : w64) :
    startingRev = W64 0 ∨ resolveStart startingRev M = startingRev := by
  by_cases h : startingRev = W64 0
  · exact Or.inl h
  · right; rw [resolveStart, ite_eq_right h]

theorem demux.Register.wp_proof : demux.Register.spec (GF := GF) (hG := hG) := by
  intro d γd cap C w γ predT startingRev
  wp_start as ⟨#Hd, Hh, #Hw, Hopen, Huniq⟩
  wp_apply wp_with_defer as %defer defer
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  unfold demuxHandle
  wp_apply (lc := 3) sync.RWMutex.wp_Lock $$ [$Hh] as ⟨Hlk, HP⟩
  icombine Hlc1 Hlc2 as Hlc
  imod demux_lock_acquire d γd cap $$ [Hd HP Hlc] with ⟨%c, %regs, %views, Hcore, Hl, %Hinv⟩
  · iframe; iframe #
  iNamed Hl
  -- `w` is not registered yet
  cases Hrw : regs !! w with
  | some ri =>
    icases (BigSepM.bigSepM_delete (m := regs) Hrw).1 $$ Hres with ⟨Hr, -⟩
    iunfold regRes at Hr
    icases Hr with ⟨%sent', %v', %pred', #Hw', #Hpred', Hview', Hwat', Huniq', %Hdel'⟩
    iexfalso
    iapply watcherUnique_excl w γ predT (demuxPub C predT startingRev)
    iframe Hw Huniq Huniq'
  | none =>
  have Hvw : views !! w = none := by
    have := Hok.dom w; rw [Hrw] at this; cases h : views !! w <;> simp_all
  obtain ⟨ph, Hph⟩ : ∃ ph : RegPhase, ph = (if c.maxRev = W64 0 then
      (if startingRev = W64 0 then RegPhase.active else RegPhase.lagging)
    else (if sint.Z (resolveStart startingRev c.maxRev) ≤ sint.Z c.maxRev then RegPhase.lagging
      else RegPhase.active)) := ⟨_, rfl⟩
  have Hmapped : ph.mapped = true := by subst Hph; split <;> split <;> rfl
  have Hup : ph = .active → ∀ b ∈ c.stream.take c.stream.length,
      sint.Z (batchRev b) < sint.Z (resolveStart startingRev c.maxRev) := by
    intro hact b hb
    rw [List.take_length] at hb
    have h1 := Hinv.stream_le b hb
    have h2 := Hinv.stream_ok.pos b hb
    by_cases hM : c.maxRev = W64 0
    · rw [hM] at h1; have : sint.Z (W64 0) = 0 := by word
      omega
    · subst Hph; simp only [hM, ↓reduceIte] at hact
      split at hact
      · cases hact
      · omega
  imod saved_pred_alloc (GF := GF) (fun k : Option GoString => iprop(⌜predCode predT k = true⌝))
    DFrac.discard DFrac.valid_discard with ⟨%pn, #HpredT⟩
  imod ghost_map_insert w (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev) Hrw $$ Hregs
    with ⟨Hregs, Helem⟩
  imod ghost_map_insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) Hvw
    $$ Hviews with ⟨Hviews, Hview⟩
  have Hopw : ph.toWatcher = .opened := by
    revert Hmapped; cases ph <;> simp [RegPhase.mapped, RegPhase.toWatcher]
  ihave Hr : regRes C γd w (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev) $$ [Hopen Hview Huniq]
  · iunfold regRes
    iexists [], View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph, predT
    simp only [named]
    iframe Hview Hw Huniq
    isplitr
    · iunfold predIs; iexact HpredT
    isplitl
    · simp only [Hopw]; unfold watcherAt; iexact Hopen
    ipureintro
    exact Delivered.init predT _ _ Hinv.stream_ok Hinv.stream_le rfl
      (fun m h => by simp only at h; rw [h] at Hmapped; simp [RegPhase.mapped] at Hmapped)
  ihave Hres := (BigSepM.bigSepM_insert (m := regs) (i := w) Hrw).2 $$ [Hr Hres]
  · iframe
  have Hok' := Hok.register w (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev)
    (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) (fun _ => ⟨rfl, rfl⟩) Hup
  have Hstart' := Hstart.register w (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev)
    (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph)
    (fun _ => register_startOk Hinv startingRev γ pn ph Hph) (resolveStart_sr startingRev c.maxRev)
  have Hact_a : ph = .active →
      actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) =
        GMap.insert w (resolveStart startingRev c.maxRev) (actOf views) ∧
      lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) =
        lagOf views := by
    intro h; subst h
    rw [actOf_insert, lagOf_insert]
    simp only [↓reduceIte, reduceCtorEq, true_and]
    exact GMap.delete_notin _ _ (by rw [lagOf_lookup, Hvw]; rfl)
  have Hact_l : ph = .lagging →
      actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) =
        actOf views ∧
      lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) =
        GMap.insert w (resolveStart startingRev c.maxRev) (lagOf views) := by
    intro h; subst h
    rw [actOf_insert, lagOf_insert]
    simp only [↓reduceIte, reduceCtorEq, and_true]
    exact GMap.delete_notin _ _ (by rw [actOf_lookup, Hvw]; rfl)
  wp_auto
  wp_if_destruct
  · -- maxRev = 0
    have Hm0 := Hif
    wp_if_destruct
    · -- startingRev = 0: active from now
      have hph : ph = .active := by rw [Hph, ite_eq_left Hm0, ite_eq_left rfl]
      wp_apply wp_mapInsert $$ Hact as Hact
      have HA : actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views) = GMap.insert w (W64 0) (actOf views) := by rw [(Hact_a hph).1]; simp [resolveStart, Hm0]
      have HL : lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views) = lagOf views := (Hact_a hph).2
      ihave Hl : demuxLocked d γd cap C c c.stream.length
          (GMap.insert w (RegInfo.mk γ (resolveStart (W64 0) c.maxRev) pn (W64 0)) regs)
          (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views)
        $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
      · iunfold demuxLocked
        iexists actP, lagP
        rw [HA, HL]
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hok', Hstart'⟩
      imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
      · iframe; iframe #; ipureintro; exact Hinv
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
      · inext; iexact HP
      iapply HΦ
      iframe
      iexists (resolveStart (W64 0) c.maxRev), c.maxRev
      iunfold demuxRegistered
      isplitl
      · iexists pn, W64 0; iframe; iunfold predIs; iexact HpredT
      ipureintro; rfl
    · -- lagging from startingRev
      have hph : ph = .lagging := by rw [Hph, ite_eq_left Hm0, ite_eq_right Hif]
      wp_apply wp_mapInsert $$ Hlag as Hlag
      have HA : actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) = actOf views := (Hact_l hph).1
      have HL : lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) = GMap.insert w startingRev (lagOf views) := by rw [(Hact_l hph).2, resolveStart, ite_eq_right Hif]
      ihave Hl : demuxLocked d γd cap C c c.stream.length
          (GMap.insert w (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev) regs)
          (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views)
        $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
      · iunfold demuxLocked
        iexists actP, lagP
        rw [HA, HL]
        simp only [named]
        iframe
        iframe #
        ipureintro; exact ⟨Hok', Hstart'⟩
      imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
      · iframe; iframe #; ipureintro; exact Hinv
      wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
      · inext; iexact HP
      iapply HΦ
      iframe
      iexists (resolveStart startingRev c.maxRev), c.maxRev
      iunfold demuxRegistered
      isplitl
      · iexists pn, startingRev; iframe; iunfold predIs; iexact HpredT
      ipureintro; rfl
  · -- maxRev ≠ 0
    have Hm0 := Hif
    wp_if_destruct
    · -- startingRev = 0: from maxRev + 1
      have Hr : resolveStart (W64 0) c.maxRev = c.maxRev + W64 1 := by rw [resolveStart, ite_eq_left rfl, ite_eq_right Hm0]
      wp_if_destruct
      · have hph : ph = .lagging := by rw [Hph, ite_eq_right Hm0, ite_eq_left (by rw [Hr]; exact Hif)]
        wp_apply wp_mapInsert $$ Hlag as Hlag
        have HA : actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views) = actOf views := (Hact_l hph).1
        have HL : lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views) = GMap.insert w (c.maxRev + W64 1) (lagOf views) := by rw [(Hact_l hph).2, Hr]
        ihave Hl : demuxLocked d γd cap C c c.stream.length
            (GMap.insert w (RegInfo.mk γ (resolveStart (W64 0) c.maxRev) pn (W64 0)) regs)
            (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views)
          $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
        · iunfold demuxLocked
          iexists actP, lagP
          rw [HA, HL]
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨Hok', Hstart'⟩
        imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
        · iframe; iframe #; ipureintro; exact Hinv
        wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
        · inext; iexact HP
        iapply HΦ
        iframe
        iexists (resolveStart (W64 0) c.maxRev), c.maxRev
        iunfold demuxRegistered
        isplitl
        · iexists pn, W64 0; iframe; iunfold predIs; iexact HpredT
        ipureintro; rfl

      · have hph : ph = .active := by rw [Hph, ite_eq_right Hm0, ite_eq_right (by rw [Hr]; exact Hif)]
        wp_apply wp_mapInsert $$ Hact as Hact
        have HA : actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views) = GMap.insert w (c.maxRev + W64 1) (actOf views) := by rw [(Hact_a hph).1, Hr]
        have HL : lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views) = lagOf views := (Hact_a hph).2
        ihave Hl : demuxLocked d γd cap C c c.stream.length
            (GMap.insert w (RegInfo.mk γ (resolveStart (W64 0) c.maxRev) pn (W64 0)) regs)
            (GMap.insert w (View.mk c.stream c.maxRev (resolveStart (W64 0) c.maxRev) ph) views)
          $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
        · iunfold demuxLocked
          iexists actP, lagP
          rw [HA, HL]
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨Hok', Hstart'⟩
        imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
        · iframe; iframe #; ipureintro; exact Hinv
        wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
        · inext; iexact HP
        iapply HΦ
        iframe
        iexists (resolveStart (W64 0) c.maxRev), c.maxRev
        iunfold demuxRegistered
        isplitl
        · iexists pn, W64 0; iframe; iunfold predIs; iexact HpredT
        ipureintro; rfl

    · have Hs0 := Hif
      have Hr : resolveStart startingRev c.maxRev = startingRev := by rw [resolveStart, ite_eq_right Hs0]
      wp_if_destruct
      · have hph : ph = .lagging := by rw [Hph, ite_eq_right Hm0, ite_eq_left (by rw [Hr]; exact Hif)]
        wp_apply wp_mapInsert $$ Hlag as Hlag
        have HA : actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) = actOf views := (Hact_l hph).1
        have HL : lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) = GMap.insert w startingRev (lagOf views) := by rw [(Hact_l hph).2, Hr]
        ihave Hl : demuxLocked d γd cap C c c.stream.length
            (GMap.insert w (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev) regs)
            (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views)
          $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
        · iunfold demuxLocked
          iexists actP, lagP
          rw [HA, HL]
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨Hok', Hstart'⟩
        imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
        · iframe; iframe #; ipureintro; exact Hinv
        wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
        · inext; iexact HP
        iapply HΦ
        iframe
        iexists (resolveStart startingRev c.maxRev), c.maxRev
        iunfold demuxRegistered
        isplitl
        · iexists pn, startingRev; iframe; iunfold predIs; iexact HpredT
        ipureintro; rfl

      · have hph : ph = .active := by rw [Hph, ite_eq_right Hm0, ite_eq_right (by rw [Hr]; exact Hif)]
        wp_apply wp_mapInsert $$ Hact as Hact
        have HA : actOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) = GMap.insert w startingRev (actOf views) := by rw [(Hact_a hph).1, Hr]
        have HL : lagOf (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views) = lagOf views := (Hact_a hph).2
        ihave Hl : demuxLocked d γd cap C c c.stream.length
            (GMap.insert w (RegInfo.mk γ (resolveStart startingRev c.maxRev) pn startingRev) regs)
            (GMap.insert w (View.mk c.stream c.maxRev (resolveStart startingRev c.maxRev) ph) views)
          $$ [Hregs Hviews HminRev HmaxRev HactF HlagF Hact Hlag Hhist Hres]
        · iunfold demuxLocked
          iexists actP, lagP
          rw [HA, HL]
          simp only [named]
          iframe
          iframe #
          ipureintro; exact ⟨Hok', Hstart'⟩
        imod demux_lock_release d γd cap c _ _ $$ [Hd Hcore Hl Hlc3] with HP
        · iframe; iframe #; ipureintro; exact Hinv
        wp_apply sync.RWMutex.wp_Unlock $$ [$Hlk HP] as Hh
        · inext; iexact HP
        iapply HΦ
        iframe
        iexists (resolveStart startingRev c.maxRev), c.maxRev
        iunfold demuxRegistered
        isplitl
        · iexists pn, startingRev; iframe; iunfold predIs; iexact HpredT
        ipureintro; rfl



end proof

end EtcdGrove
end Perennial
