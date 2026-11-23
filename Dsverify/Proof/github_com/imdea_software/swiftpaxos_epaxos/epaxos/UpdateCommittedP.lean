/-
`updateCommitted` over the rows with any slot predicate that lets it read `Status`
(`repInstsP`): a caller can keep a slot's pointer known across the call.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.UpdateCommitted
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

theorem updP_self {α : Type} (P : InstId → α) (x : InstId) : updP P x (P x) = P := by
  funext y; unfold updP; split <;> simp_all

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- A slot predicate from which `Status` can be read and given back. -/
def StatusReadable (inst : InstId → Option InstRec) (P : InstId → Loc → IProp GF) : Prop :=
  (∀ x pt, inst x = none → P x pt ⊢ ⌜pt = null⌝ ∗ P x pt) ∧
  (∀ x pt w, inst x = some w → P x pt ⊢
    ∃ y : epaxos.Instance, pt ↦ y ∗ ⌜y.Status' = w.status⌝ ∗ (pt ↦ y -∗ P x pt))

theorem instAtP_status (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) :
    StatusReadable inst (instAtP (GF := GF) γ i inst) := by
  refine ⟨fun x pt h => ?_, fun x pt w h => ?_⟩
  · simp only [instAtP, h, instAt]
    iintro %H; isplitr <;> ipureintro <;> exact H
  · simp only [instAtP, h]
    unfold instAt ownInst
    iintro ⟨%y, Hy, %Hyf, Hrest⟩
    iexists y
    iframe Hy
    isplitr
    · ipureintro; exact Hyf.2.2.1
    iintro Hy
    iexists y
    iframe Hy Hrest
    ipureintro; exact Hyf

theorem wp_updateCommittedP (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (σ : RState) (q : w32) (hq : 0 ≤ zz q ∧ zz q < nR)
    (hib : instBounds σ.inst) (hcb : cutBounds σ.committedUpTo)
    (P : InstId → Loc → IProp GF) (hP : StatusReadable σ.inst P) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ isReplicaFw γ rr i L p Rext ∗
        repInstsP r P ∗ repRowArr r go!"CommittedUpTo" σ.committedUpTo }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"updateCommitted"))
        (Val #q))
    {{ RET #(); repInstsP r P ∗
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
  icases repInstsP_acc r P ⟨toN q, toN (c + 1)⟩ hq' hn1 $$ Hins with
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
    icases hP.1 _ _ hx $$ Hx with ⟨%Hnull, Hx⟩
    subst Hnull
    wp_auto
    wp_if_destruct
    all_goals try (exact absurd Hif false_neq_true)
    wp_apply sync.Mutex.wp_Unlock $$ [$Hlock $Hlocked $HR]
    have hset : ptrs.set (toN (c + 1)) null = ptrs := by
      have := List.getElem?_eq_some_iff.mp Hptr.1
      rw [← this.2]; exact List.set_getElem_self this.1
    ihave Hins := Hclose $$ %null %(P ⟨toN q, toN (c + 1)⟩) [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    rw [updP_self]
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
    icases hP.2 _ _ _ hx $$ Hx with ⟨%y, Hy, %Hys, Hback⟩
    have Hyf : True ∧ True ∧ y.Status' = w.status ∧ True := ⟨trivial, trivial, Hys, trivial⟩
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
      ihave Hins : repInstsP r P $$ [Hclose Hptrs Hy Hback]
      · ihave HP := Hback $$ Hy
        ihave H := Hclose $$ %ptr %(P ⟨toN q, toN (c + 1)⟩) [Hptrs] HP
        · rw [hcset]; iexact Hptrs
        rw [updP_self]; iexact H
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
        ihave Hins : repInstsP r P $$ [Hclose Hptrs Hy Hback]
        · ihave HP := Hback $$ Hy
          ihave H := Hclose $$ %ptr %(P ⟨toN q, toN (c + 1)⟩) [Hptrs] HP
          · rw [hcset]; iexact Hptrs
          rw [updP_self]; iexact H
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
        ihave Hins : repInstsP r P $$ [Hclose Hptrs Hy Hback]
        · ihave HP := Hback $$ Hy
          ihave H := Hclose $$ %ptr %(P ⟨toN q, toN (c + 1)⟩) [Hptrs] HP
          · rw [hcset]; iexact Hptrs
          rw [updP_self]; iexact H
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

theorem ptrSlot_status (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) (x : InstId)
    (ptr : Loc) (w : InstRec) (hx : inst x = some w) :
    StatusReadable inst (updP (instAtP (GF := GF) γ i inst) x (fun pt => iprop(⌜pt = ptr⌝ ∗
      instAt γ i x pt (some w)))) := by
  have hb := instAtP_status (GF := GF) γ i inst
  refine ⟨fun y pt h => ?_, fun y pt w' h => ?_⟩
  · unfold updP
    by_cases hy : y = x
    · subst hy; rw [hx] at h; cases h
    · simp only [hy, if_false]; exact hb.1 y pt h
  · unfold updP
    by_cases hy : y = x
    · subst hy; rw [hx] at h; cases h
      simp only [if_true]
      iintro ⟨%He, Hi⟩
      have := hb.2 y pt _ hx
      simp only [instAtP, hx] at this
      icases this $$ Hi with ⟨%z, Hz, %Hzs, Hback⟩
      iexists z
      iframe Hz
      isplitr
      · ipureintro; exact Hzs
      iintro Hz
      ihave Hi := Hback $$ Hz
      iframe Hi; ipureintro; exact He
    · simp only [hy, if_false]; exact hb.2 y pt w' h

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
