/-
`(*Replica).updateCommitted` against the model's `updateCommitted`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

theorem cut_step (c : w32) (fuel : Nat) (Hc1 : -1 ≤ zz c) (Hc2 : zz c + 2 ≤ MAX_INSTANCE)
    (Hfuel1 : (MAX_INSTANCE : Int) ≤ fuel + zz c + 1) (hlt : toN (c + 1) + 2 ≤ MAX_INSTANCE) :
    -1 ≤ zz (c + 1) ∧ zz (c + 1) + 2 ≤ MAX_INSTANCE ∧ ∃ f, fuel = f + 1 ∧
      (MAX_INSTANCE : Int) ≤ f + zz (c + 1) + 1 := by
  unfold MAX_INSTANCE at Hc2 Hfuel1 hlt ⊢
  simp only [zz, toN] at *
  have hc1 : sint.Z (c + 1) = sint.Z c + 1 := by word
  refine ⟨by omega, by omega, fuel - 1, by omega, by omega⟩

/-- `updateCommitted` keeps `CommittedUpTo[q] + 1` in the row. -/
theorem cutBounds_updateCommitted (σ : RState) (q : Nat) (hib : instBounds σ.inst)
    (hcb : cutBounds σ.committedUpTo) : cutBounds (updateCommitted σ q).committedUpTo := by
  have adv : ∀ fuel (c : w32), -1 ≤ zz c → zz c + 2 ≤ MAX_INSTANCE →
      -1 ≤ zz (advanceCommitted σ q fuel c) ∧ zz (advanceCommitted σ q fuel c) + 2 ≤ MAX_INSTANCE := by
    intro fuel
    induction fuel with
    | zero => intro c h1 h2; exact ⟨h1, h2⟩
    | succ f ih =>
      intro c h1 h2
      simp only [advanceCommitted]
      rcases hx : σ.inst ⟨q, toN (c + 1)⟩ with _ | x
      · exact ⟨h1, h2⟩
      · simp only
        split
        · have hsome := hib ⟨q, toN (c + 1)⟩
          rw [hx] at hsome
          have hlt : toN (c + 1) + 2 ≤ MAX_INSTANCE := by
            by_cases hh : toN (c + 1) + 2 ≤ MAX_INSTANCE
            · exact hh
            · exfalso
              have := hsome (Or.inr (show MAX_INSTANCE - 1 ≤ toN (c + 1) by omega)); simp at this
          obtain ⟨hs1, hs2, -⟩ := cut_step c (MAX_INSTANCE) h1 h2 (by omega) hlt
          exact ih (c + 1) hs1 hs2
        · exact ⟨h1, h2⟩
  intro q' hq'
  simp only [updateCommitted, upd]
  split
  · subst_vars; exact adv _ _ (hcb _ hq').1 (hcb _ hq').2
  · exact hcb _ hq'

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

theorem wp_updateCommitted (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (σ : RState) (q : w32) (hq : 0 ≤ zz q ∧ zz q < nR)
    (hib : instBounds σ.inst) (hcb : cutBounds σ.committedUpTo) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ isReplicaFw γ rr i L p Rext ∗
        repInsts γ i r σ.inst ∗ repRowArr r go!"CommittedUpTo" σ.committedUpTo }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"updateCommitted"))
        (Val #q))
    {{ RET #(); repInsts γ i r σ.inst ∗
        repRowArr r go!"CommittedUpTo" (updateCommitted σ (toN q)).committedUpTo }} := by
  wp_start as ⟨#Hrr, #Hfw, Hins, Hcut⟩
  ihave #Hlock := isReplicaFw_lock _ _ _ _ _ _ $$ Hfw
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hlock] as ⟨Hlocked, HR⟩
  have hq' : toN q < nR := by have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have eq : sint.Z (W64 (sint.Z q)) = sint.Z q := by word
  unfold repRowArr
  icases Hcut with ⟨%cut, #Hcutf, Hcutsl⟩
  ihave %Hcutlen := ownSlice_len _ _ _ $$ Hcutsl
  ihave HI : (∃ c : w32,
      "Hcutsl" ∷ cut ↦* ((List.range nR).map (upd σ.committedUpTo (toN q) c)) ∗
      "%Hc" ∷ ⌜-1 ≤ zz c ∧ zz c + 2 ≤ MAX_INSTANCE ∧ ∃ fuel : Nat, (MAX_INSTANCE : Int) ≤ fuel + zz c + 1 ∧
        advanceCommitted σ (toN q) MAX_INSTANCE (σ.committedUpTo (toN q)) =
          advanceCommitted σ (toN q) fuel c⌝ : IProp GF) $$ [Hcutsl]
  · iexists σ.committedUpTo (toN q)
    rw [upd_self _ _ _ rfl]
    iframe Hcutsl
    ipureintro
    exact ⟨(hcb _ hq').1, (hcb _ hq').2, MAX_INSTANCE, by have := (hcb _ hq').1; omega, rfl⟩
  wp_for HI
  obtain ⟨Hc1, Hc2, fuel, Hfuel1, Hfuel⟩ := Hc
  have hn1 : toN (c + 1) < MAX_INSTANCE := by
    simp only [toN, zz] at *; unfold MAX_INSTANCE at *; word
  icases repInsts_acc γ i r σ.inst ⟨toN q, toN (c + 1)⟩ hq' hn1 $$ Hins with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  wp_auto
  have h1 : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z iss.len := by
    have := hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  have h3 : 0 ≤ sint.Z (W64 (sint.Z q)) ∧ sint.Z (W64 (sint.Z q)) < sint.Z cut.len := by
    have := hq.1; have := hq.2; have := Hcutlen.1; simp only [List.length_map, List.length_range] at *
    unfold toN zz nR at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [eq]; exact Hrow
  simp only [h3, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index cut _ _ _ c h3.1 $$ [$Hcutsl] as Hcutsl
  · ipureintro; rw [eq]; simp [upd, hq', show (sint.Z q).toNat = toN q from rfl]
  have eq2 : sint.Z (W64 (sint.Z (c + W32 1))) = sint.Z (c + W32 1) := by word
  have hcn : (sint.Z (c + W32 1)).toNat = toN (c + 1) := rfl
  have h2 : 0 ≤ sint.Z (W64 (sint.Z (c + W32 1))) ∧
      sint.Z (W64 (sint.Z (c + W32 1))) < sint.Z row.len := by
    have := Hptr.2; have := Hplen.1; have := Hplen.2
    simp only [toN, zz] at *; unfold MAX_INSTANCE at *; constructor <;> word
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [eq2, hcn]; exact Hptr.1
  rcases hx : σ.inst ⟨toN q, toN (c + 1)⟩ with _ | w
  · -- no instance: the scan stops
    unfold instAt; icases Hx with %Hnull
    subst Hnull
    wp_auto
    wp_if_destruct
    all_goals try (exact absurd Hif false_neq_true)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $HR]
    have hset : ptrs.set (toN (c + 1)) null = ptrs := by
      have := List.getElem?_eq_some_iff.mp Hptr.1
      rw [← this.2]; exact List.set_getElem_self this.1
    ihave Hins := Hclose $$ %null %none [Hptrs] []
    · rw [hset]; iexact Hptrs
    · ipureintro; rfl
    rw [upd_self _ _ _ hx]
    iapply HΦ
    iframe Hins
    iexists cut; iframe Hcutf
    have hfin : (updateCommitted σ (toN q)).committedUpTo = upd σ.committedUpTo (toN q) c := by
      simp only [updateCommitted, Hfuel]
      have hf1 : 1 ≤ fuel := by
        have := Hc2; unfold MAX_INSTANCE at *; simp only [zz] at *; omega
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hx' : σ.inst ⟨toN q, toN (c + 1#32)⟩ = none := hx
      simp [advanceCommitted, hx']
    rw [hfin]; iexact Hcutsl
  · -- an instance: test its status
    unfold instAt ownInst
    icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
    rw [show decide (ptr = null) = false from decide_eq_false Hnn]
    simp only [Bool.not_false]
    wp_auto
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [eq]; exact Hrow
    simp only [h3, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index cut _ _ _ c h3.1 $$ [$Hcutsl] as Hcutsl
    · ipureintro; rw [eq]; simp [upd, hq', show (sint.Z q).toNat = toN q from rfl]
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
    · ipureintro; rw [eq2, hcn]; exact Hptr.1
    have hcset : ptrs.set (toN (c + 1)) ptr = ptrs := by
      have := List.getElem?_eq_some_iff.mp Hptr.1
      rw [← this.2]; exact List.set_getElem_self this.1
    wp_if_destruct
    · -- COMMITTED
      have hcomm : w.status = stCOMMITTED ∨ w.status = stEXECUTED := Or.inl (by rw [← Hyf.2.2.1]; exact Hif)
      ihave Hins : repInsts γ i r σ.inst $$ [Hclose Hptrs Hy Hycmds Hydeps Hylb]
      · ihave H := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hylb]
        · rw [hcset]; iexact Hptrs
        · iexists y; iframe Hy Hycmds Hydeps Hylb
          isplitr
          · ipureintro; exact Hyf
          iexact Hyid
        rw [upd_self _ _ _ hx]; iexact H
      cleanup_bool_decide
      simp only [h3, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index cut _ _ _ c h3.1 $$ [$Hcutsl] as Hcutsl
      · ipureintro; rw [eq]; simp [upd, hq', show (sint.Z q).toNat = toN q from rfl]
      have h3' : 0 ≤ sint.Z (W64 (sint.Z q)) ∧
          sint.Z (W64 (sint.Z q)) < ((List.range nR).map (upd σ.committedUpTo (toN q) c)).length := by
        simp only [List.length_map, List.length_range]; have := hq.1; have := hq.2
        unfold toN zz nR at *; constructor <;> word
      simp only [h3, _root_.and_self, ↓reduceIte]
      wp_apply wp_store_slice_index $$ [$Hcutsl] as Hcutsl
      · ipureintro; exact h3'
      wp_for_post
      iframe
      iexists c + 1
      rw [eq, show (sint.Z q).toNat = toN q from rfl, ← map_range_upd _ _ _ _ hq', upd_upd,
        show c + W32 1 = c + 1 from rfl]
      iframe Hcutsl
      have hsome := hib ⟨toN q, toN (c + 1)⟩
      rw [hx] at hsome
      have hlt : toN (c + 1) + 2 ≤ MAX_INSTANCE := by
        by_cases hh : toN (c + 1) + 2 ≤ MAX_INSTANCE
        · exact hh
        · exfalso; have := hsome (Or.inr (show MAX_INSTANCE - 1 ≤ toN (c + 1) by omega)); simp at this
      ipureintro
      obtain ⟨hs1, hs2, f, rfl, hs3⟩ := cut_step c fuel Hc1 Hc2 Hfuel1 hlt
      refine ⟨hs1, hs2, f, hs3, ?_⟩
      rw [Hfuel]
      have hx' : σ.inst ⟨toN q, toN (c + 1#32)⟩ = some w := hx
      simp only [advanceCommitted, hx, hx']
      rw [if_pos hcomm]
    · -- not COMMITTED: test EXECUTED
      simp only [h1, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
      · ipureintro; rw [eq]; exact Hrow
      simp only [h3, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index cut _ _ _ c h3.1 $$ [$Hcutsl] as Hcutsl
      · ipureintro; rw [eq]; simp [upd, hq', show (sint.Z q).toNat = toN q from rfl]
      simp only [h2, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
      · ipureintro; rw [eq2, hcn]; exact Hptr.1
      cleanup_bool_decide
      wp_if_destruct
      · have hcomm : w.status = stCOMMITTED ∨ w.status = stEXECUTED := by
          right; rw [← Hyf.2.2.1]; exact Hif
        ihave Hins : repInsts γ i r σ.inst $$ [Hclose Hptrs Hy Hycmds Hydeps Hylb]
        · ihave H := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hylb]
          · rw [hcset]; iexact Hptrs
          · iexists y; iframe Hy Hycmds Hydeps Hylb
            isplitr
            · ipureintro; exact Hyf
            iexact Hyid
          rw [upd_self _ _ _ hx]; iexact H
        cleanup_bool_decide
        try wp_auto
        simp only [h3, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index cut _ _ _ c h3.1 $$ [$Hcutsl] as Hcutsl
        · ipureintro; rw [eq]; simp [upd, hq', show (sint.Z q).toNat = toN q from rfl]
        have h3' : 0 ≤ sint.Z (W64 (sint.Z q)) ∧
            sint.Z (W64 (sint.Z q)) < ((List.range nR).map (upd σ.committedUpTo (toN q) c)).length := by
          simp only [List.length_map, List.length_range]; have := hq.1; have := hq.2
          unfold toN zz nR at *; constructor <;> word
        simp only [h3, _root_.and_self, ↓reduceIte]
        wp_apply wp_store_slice_index $$ [$Hcutsl] as Hcutsl
        · ipureintro; exact h3'
        wp_for_post
        iframe
        iexists c + 1
        rw [eq, show (sint.Z q).toNat = toN q from rfl, ← map_range_upd _ _ _ _ hq', upd_upd,
        show c + W32 1 = c + 1 from rfl]
        iframe Hcutsl
        have hsome := hib ⟨toN q, toN (c + 1)⟩
        rw [hx] at hsome
        have hlt : toN (c + 1) + 2 ≤ MAX_INSTANCE := by
          by_cases hh : toN (c + 1) + 2 ≤ MAX_INSTANCE
          · exact hh
          · exfalso; have := hsome (Or.inr (show MAX_INSTANCE - 1 ≤ toN (c + 1) by omega)); simp at this
        ipureintro
        obtain ⟨hs1, hs2, f, rfl, hs3⟩ := cut_step c fuel Hc1 Hc2 Hfuel1 hlt
        refine ⟨hs1, hs2, f, hs3, ?_⟩
        rw [Hfuel]
        have hx' : σ.inst ⟨toN q, toN (c + 1#32)⟩ = some w := hx
        simp only [advanceCommitted, hx, hx']
        rw [if_pos hcomm]
      · -- neither: the scan stops
        ihave Hins : repInsts γ i r σ.inst $$ [Hclose Hptrs Hy Hycmds Hydeps Hylb]
        · ihave H := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hylb]
          · rw [hcset]; iexact Hptrs
          · iexists y; iframe Hy Hycmds Hydeps Hylb
            isplitr
            · ipureintro; exact Hyf
            iexact Hyid
          rw [upd_self _ _ _ hx]; iexact H
        rename_i Hif4
        have hnc : ¬ (w.status = stCOMMITTED ∨ w.status = stEXECUTED) := by
          rw [← Hyf.2.2.1]; rintro (h | h)
          · exact Hif4 h
          · exact Hif h
        cleanup_bool_decide
        wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $HR]
        iapply HΦ
        iframe Hins
        iexists cut; iframe Hcutf
        have hfin : (updateCommitted σ (toN q)).committedUpTo = upd σ.committedUpTo (toN q) c := by
          simp only [updateCommitted, Hfuel]
          have hf1 : 1 ≤ fuel := by
            have := Hc2; unfold MAX_INSTANCE at *; simp only [zz] at *; omega
          obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
          have hx' : σ.inst ⟨toN q, toN (c + 1#32)⟩ = some w := hx
          simp only [advanceCommitted, hx, hx']
          rw [if_neg hnc]
        rw [hfin]; iexact Hcutsl

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
