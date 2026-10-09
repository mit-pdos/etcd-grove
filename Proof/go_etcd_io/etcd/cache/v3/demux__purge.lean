/-
Proof of `Spec/demux__purge.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.demux__purge
public import Spec.go_etcd_io.etcd.cache.v3.ringBuffer__RebaseHistory
public import Spec.go_etcd_io.etcd.cache.v3.watcher__Stop

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

/-! ## The loops' invariant: the watchers visited so far are closed -/

/-- `vs` is `views` with the watchers `done` closed (cancel `none`). -/
def demuxPurge_closed (views vs : GMap Loc View) (done : List Loc) : Prop :=
  (∀ w, w ∉ done → vs !! w = views !! w) ∧
  (∀ w, w ∈ done → ∃ v, views !! w = some v ∧ vs !! w = some { v with phase := .closed none })

theorem demuxPurge_not_mem_take {l : List Loc} (h : l.Nodup) {i : Nat} {x : Loc}
    (hx : l[i]? = some x) : x ∉ l.take i := by
  intro hm
  have hsplit : l = l.take i ++ l.drop i := (List.take_append_drop i l).symm
  rw [hsplit] at h
  have hdrop : x ∈ l.drop i := by
    apply List.mem_of_getElem? (i := 0)
    rw [List.getElem?_drop]; simpa using hx
  exact (List.nodup_append.1 h).2.2 x hm x hdrop rfl

theorem demuxPurge_closed_nil (views : GMap Loc View) : demuxPurge_closed views views [] :=
  ⟨fun _ _ => rfl, fun _ h => absurd h List.not_mem_nil⟩

theorem demuxPurge_step {views vs : GMap Loc View} {keys : List Loc} {i : Nat} {w : Loc}
    {v : View} (hc : demuxPurge_closed views vs (keys.take i)) (hk : keys[i]? = some w)
    (hnd : keys.Nodup) (hv : views !! w = some v) :
    vs !! w = some v ∧
      demuxPurge_closed views (GMap.insert w { v with phase := .closed none } vs)
        (keys.take (i + 1)) := by
  have hnot := demuxPurge_not_mem_take hnd hk
  have htake : keys.take (i + 1) = keys.take i ++ [w] := by
    rw [List.take_add_one, hk]; rfl
  refine ⟨(hc.1 w hnot).trans hv, ?_, ?_⟩
  · intro x hx
    rw [htake, List.mem_append, List.mem_singleton, not_or] at hx
    rw [GMap.lookup_insert_ne _ _ (Ne.symm hx.2)]
    exact hc.1 x hx.1
  · intro x hx
    rw [htake, List.mem_append, List.mem_singleton] at hx
    by_cases hxw : x = w
    · subst hxw; exact ⟨v, hv, GMap.lookup_insert _ _ _⟩
    · rcases hx with hx | hx
      · rw [GMap.lookup_insert_ne _ _ (Ne.symm hxw)]; exact hc.2 x hx
      · exact absurd hx hxw

/-- After both loops: nothing is mapped, and the domain is unchanged. -/
theorem demuxPurge_final {views vs1 vs2 : GMap Loc View} {k1 k2 : List Loc}
    (h1 : demuxPurge_closed views vs1 k1) (h2 : demuxPurge_closed vs1 vs2 k2)
    (hk1 : ∀ w, w ∈ k1 ↔ (actOf views !! w).isSome)
    (hk2 : ∀ w, w ∈ k2 ↔ (lagOf views !! w).isSome) :
    (∀ w v, vs2 !! w = some v → v.phase.mapped = false) ∧
      (∀ w, (vs2 !! w).isSome = (views !! w).isSome) := by
  have hdom1 : ∀ w, (vs1 !! w).isSome = (views !! w).isSome := by
    intro w
    by_cases hw : w ∈ k1
    · obtain ⟨v, hv, hv'⟩ := h1.2 w hw; rw [hv, hv']; rfl
    · rw [h1.1 w hw]
  constructor
  · intro w v hv
    by_cases hw2 : w ∈ k2
    · obtain ⟨v', -, hv'⟩ := h2.2 w hw2; rw [hv] at hv'; cases hv'; rfl
    rw [h2.1 w hw2] at hv
    by_cases hw1 : w ∈ k1
    · obtain ⟨v', -, hv'⟩ := h1.2 w hw1; rw [hv] at hv'; cases hv'; rfl
    rw [h1.1 w hw1] at hv
    have ha : ¬ (actOf views !! w).isSome = true := fun h => hw1 ((hk1 w).2 h)
    have hl : ¬ (lagOf views !! w).isSome = true := fun h => hw2 ((hk2 w).2 h)
    rw [actOf_lookup, hv] at ha
    rw [lagOf_lookup, hv] at hl
    cases hp : v.phase <;> simp_all [RegPhase.mapped]
  · intro w
    by_cases hw2 : w ∈ k2
    · obtain ⟨v, hv, hv'⟩ := h2.2 w hw2; rw [hv', ← hdom1, hv]; rfl
    · rw [h2.1 w hw2, hdom1]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem demux.purge.wp_proof
    (wp_RebaseHistory : ringBuffer.RebaseHistory.spec (GF := GF) (hG := hG))
    (wp_Stop : watcher.Stop.spec (GF := GF) (hG := hG)) :
    demux.purge.spec (GF := GF) (hG := hG) := by
  intro d γd cap c regs views
  wp_start as ⟨Hl, %Hinv⟩
  iNamed Hl
  wp_auto
  wp_apply wp_RebaseHistory (go.GoType.SliceType (go.GoType.PointerType mvccpb.Event.ty))
    (demuxHistAddr d) cap (batchAt (hG := hG)) batchRev c.history $$ [Hhist] as Hhist
  · iexact Hhist
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (x : Loc) (vs : GMap Loc View),
      "w" ∷ w_ptr ↦ x ∗
      "Hviews" ∷ ghostMapAuth γd.views 1 vs ∗
      "Hres" ∷ ([∗map] w ↦ ri ∈ regs, regRes γd w ri) ∗
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hvs" ∷ ⌜demuxPurge_closed views vs (keys.take i.toNat)⌝)) $$ Hact
  iintro %keys1 ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [w Hviews Hres]
  · iexists _, _
    simp only [named]
    iframe w Hviews Hres
    ipureintro
    refine ⟨Int.le_refl _, ?_⟩
    simpa using demuxPurge_closed_nil views
  isplitr
  · imodintro
    iintro %i %key %n ⟨%Hkey, %Hn⟩ HP
    iNamed HP
    rw [actOf_lookup] at Hn
    obtain ⟨v, hv, hvn⟩ : ∃ v, views !! key = some v ∧ v.phase = .active ∧ v.n = n := by
      cases h : views !! key with
      | none => simp [h] at Hn
      | some v => simp only [h, Option.bind_some] at Hn; split at Hn <;> simp_all
    obtain ⟨hvs, Hvs'⟩ := demuxPurge_step Hvs Hkey Hknodup hv
    obtain ⟨ri, Hri⟩ : ∃ ri, regs !! key = some ri := by
      have h := Hok.dom key
      rw [hv] at h
      exact Option.isSome_iff_exists.1 (by simpa using h)
    icases (BigSepM.bigSepM_delete (m := regs) Hri).1 $$ Hres with ⟨Hr, Hres⟩
    iNamed Hr
    icombine Hviews Hview gives %Hlk
    rw [hvs] at Hlk
    cases Hlk
    wp_auto
    imod ghost_map_update { v with phase := .closed none } $$ Hviews Hview with ⟨Hviews, Hview⟩
    wp_apply wp_Stop key ri.γ pred sent v.phase.toWatcher $$ [Hwat] as Hcl
    · iframe Hw; iexact Hwat
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, _
    simp only [named]
    iframe w Hviews
    isplitl [Hres Hcl Hview]
    · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
      iframe Hres
      unfold regRes
      iexists sent, { v with phase := .closed none }, pred
      simp only [named]
      iframe Hw Hpred Hview
      isplitl [Hcl]
      · iExactEq Hcl
        rw [hvn.1]; rfl
      ipureintro
      exact Hdel.phase _ (fun m h => by cases h)
    ipureintro
    refine ⟨by omega, ?_⟩
    rw [show (i + 1).toNat = i.toNat + 1 by omega]
    exact Hvs'
  iintro HP Hact
  iNamed HP
  have Hc1 : demuxPurge_closed views vs keys1 := by
    rw [show (((actOf views).size : Int)).toNat = keys1.length by omega, List.take_length] at Hvs
    exact Hvs
  clear Hvs Hi
  have Hk1set := Hkset
  generalize vs = vs1 at Hc1 ⊢
  have Hdom1 : ∀ w, (vs1 !! w).isSome = (views !! w).isSome := by
    intro w
    by_cases hw : w ∈ keys1
    · obtain ⟨v, hv, hv'⟩ := Hc1.2 w hw; rw [hv, hv']; rfl
    · rw [Hc1.1 w hw]
  wp_auto
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (keys : List Loc) (i : Int) => iprop(∃ (x : Loc) (vs : GMap Loc View),
      "w" ∷ w_ptr ↦ x ∗
      "Hviews" ∷ ghostMapAuth γd.views 1 vs ∗
      "Hres" ∷ ([∗map] w ↦ ri ∈ regs, regRes γd w ri) ∗
      "%Hi" ∷ ⌜0 ≤ i⌝ ∗
      "%Hvs" ∷ ⌜demuxPurge_closed vs1 vs (keys.take i.toNat)⌝)) $$ Hlag
  iintro %keys2 ⟨%Hkset, %Hklen, %Hknodup⟩
  isplitl [w Hviews Hres]
  · iexists _, _
    simp only [named]
    iframe w Hviews Hres
    ipureintro
    refine ⟨Int.le_refl _, ?_⟩
    simpa using demuxPurge_closed_nil vs1
  isplitr
  · imodintro
    iintro %i %key %n ⟨%Hkey, %Hn⟩ HP
    iNamed HP
    rw [lagOf_lookup] at Hn
    obtain ⟨v, hv0, hvn⟩ : ∃ v, views !! key = some v ∧ v.phase = .lagging ∧ v.n = n := by
      cases h : views !! key with
      | none => simp [h] at Hn
      | some v => simp only [h, Option.bind_some] at Hn; split at Hn <;> simp_all
    have hv : vs1 !! key = some v := by
      have hk1 : key ∉ keys1 := by
        intro hk
        have := (Hk1set key).1 hk
        rw [actOf_lookup, hv0] at this
        simp [hvn.1] at this
      rw [Hc1.1 key hk1, hv0]
    obtain ⟨hvs, Hvs'⟩ := demuxPurge_step Hvs Hkey Hknodup hv
    obtain ⟨ri, Hri⟩ : ∃ ri, regs !! key = some ri := by
      have h := Hok.dom key
      rw [hv0] at h
      exact Option.isSome_iff_exists.1 (by simpa using h)
    icases (BigSepM.bigSepM_delete (m := regs) Hri).1 $$ Hres with ⟨Hr, Hres⟩
    iNamed Hr
    icombine Hviews Hview gives %Hlk
    rw [hvs] at Hlk
    cases Hlk
    wp_auto
    imod ghost_map_update { v with phase := .closed none } $$ Hviews Hview with ⟨Hviews, Hview⟩
    wp_apply wp_Stop key ri.γ pred sent v.phase.toWatcher $$ [Hwat] as Hcl
    · iframe Hw; iexact Hwat
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    iexists key, _
    simp only [named]
    iframe w Hviews
    isplitl [Hres Hcl Hview]
    · iapply (BigSepM.bigSepM_delete (m := regs) Hri).2
      iframe Hres
      unfold regRes
      iexists sent, { v with phase := .closed none }, pred
      simp only [named]
      iframe Hw Hpred Hview
      isplitl [Hcl]
      · iExactEq Hcl
        rw [hvn.1]; rfl
      ipureintro
      exact Hdel.phase _ (fun m h => by cases h)
    ipureintro
    refine ⟨by omega, ?_⟩
    rw [show (i + 1).toNat = i.toNat + 1 by omega]
    exact Hvs'
  iintro HP Hlag
  iNamed HP
  have Hc2 : demuxPurge_closed vs1 vs keys2 := by
    rw [show (((lagOf views).size : Int)).toNat = keys2.length by omega, List.take_length] at Hvs
    exact Hvs
  obtain ⟨Hunm, Hdom⟩ := demuxPurge_final Hc1 Hc2 Hk1set Hkset
  obtain ⟨Ha0, Hl0⟩ := actOf_lagOf_unmapped vs Hunm
  wp_auto
  wp_apply (wp_map_make1 (K := Loc) (V := w64) (go.GoType.PointerType watcher.ty) go.int64)
    as %a Ha
  wp_apply (wp_map_make1 (K := Loc) (V := w64) (go.GoType.PointerType watcher.ty) go.int64)
    as %l Hl
  iapply HΦ
  iexists vs
  unfold demuxLocked
  iexists a, l
  simp only [named]
  rw [Ha0, Hl0]
  iframe
  ipureintro
  refine ⟨fun w => (Hok.dom w).trans (Hdom w).symm, ?_, ?_⟩
  · intro w v hv hm; rw [Hunm w v hv] at hm; cases hm
  · intro w v hv hph; have := Hunm w v hv; rw [hph] at this; cases this

end proof

end EtcdGrove
end Perennial
