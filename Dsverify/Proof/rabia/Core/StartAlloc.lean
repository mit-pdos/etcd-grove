/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/Rabia/StartAlloc.lean`, run `rabia-r1wake-1`.)

Allocation lemmas for `Start.lean`'s `start` (helpers, internal to the start): ghost maps with
given keys, the facts' invariant `rabiaInv` at the empty record.
-/
module

public import Dsverify.Proof.rabia.Core.Proto
public import Dsverify.Proof.rabia.Core.PkgState

@[expose] public section

noncomputable section

namespace Perennial.rabia

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model

section ghostmaps
variable {GF : BundledGFunctors} [AllG GF]
variable {K V : Type} [DecidableEq K] [Pos.Countable K] [Pos.Countable V]

/-- A ghost map with the keys `ks`, each at `v`: its authority, one half of each element in a
`[∗map]` (an invariant's), the other halves by key. -/
theorem ghost_map_alloc_halves (v : V) : ∀ (ks : List K), ks.Nodup →
    ⊢ |==> ∃ (γ : GName) (m : GMap K V), (ghostMapAuth γ 1 m : IProp GF) ∗
      ([∗map] k ↦ x ∈ m, k ↪[γ]{#(1 : Qp).half} x) ∗
      ([∗list] k ∈ ks, k ↪[γ]{#(1 : Qp).half} v) ∗
      ⌜∀ k x, m.lookup k = some x → x = v ∧ k ∈ ks⌝
  | [], _ => by
    imod ghost_map_alloc_empty (GF := GF) (K := K) (V := V) with ⟨%γ, H⟩
    imodintro
    iexists γ, ∅
    iframe H
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro
    intro k x h; simp at h
  | k0 :: ks, hnd => by
    have hk0 : k0 ∉ ks := (List.nodup_cons.1 hnd).1
    imod ghost_map_alloc_halves v ks (List.nodup_cons.1 hnd).2 with ⟨%γ, %m, Ha, Hm, Hl, %hm⟩
    have hnone : m.lookup k0 = none := by
      cases h : m.lookup k0 with
      | none => rfl
      | some x => exact absurd (hm k0 x h).2 hk0
    imod ghost_map_insert k0 v hnone $$ Ha with ⟨Ha, He⟩
    icases (ghostMapElem_halves γ k0 v).1 $$ He with ⟨He1, He2⟩
    imodintro
    iexists γ, m.insert k0 v
    iframe Ha
    isplitl [Hm He1]
    · iapply (BigSepM.bigSepM_insert (Φ := fun k x => (k ↪[γ]{#(1 : Qp).half} x : IProp GF))
        (m := m) (i := k0) (x := v) hnone).2
      iframe He1 Hm
    isplitl [Hl He2]
    · iapply BigSepL.bigSepL_cons.2
      iframe He2 Hl
    ipureintro
    intro k x h
    by_cases e : k = k0
    · subst e; rw [GMap.lookup_insert] at h; injection h with h; exact ⟨h.symm, by simp⟩
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
      obtain ⟨h1, h2⟩ := hm k x h
      exact ⟨h1, List.mem_cons_of_mem _ h2⟩

/-- A ghost map with the keys `ks`, each at `v`, every element whole. -/
theorem ghost_map_alloc_full (v : V) : ∀ (ks : List K), ks.Nodup →
    ⊢ |==> ∃ (γ : GName) (m : GMap K V), (ghostMapAuth γ 1 m : IProp GF) ∗
      ([∗list] k ∈ ks, k ↪[γ] v) ∗ ⌜∀ k x, m.lookup k = some x → k ∈ ks⌝
  | [], _ => by
    imod ghost_map_alloc_empty (GF := GF) (K := K) (V := V) with ⟨%γ, H⟩
    imodintro
    iexists γ, ∅
    iframe H
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    ipureintro
    intro k x h; simp at h
  | k0 :: ks, hnd => by
    have hk0 : k0 ∉ ks := (List.nodup_cons.1 hnd).1
    imod ghost_map_alloc_full v ks (List.nodup_cons.1 hnd).2 with ⟨%γ, %m, Ha, Hl, %hm⟩
    have hnone : m.lookup k0 = none := by
      cases h : m.lookup k0 with
      | none => rfl
      | some x => exact absurd (hm k0 x h) hk0
    imod ghost_map_insert k0 v hnone $$ Ha with ⟨Ha, He⟩
    imodintro
    iexists γ, m.insert k0 v
    iframe Ha
    isplitl [Hl He]
    · iapply BigSepL.bigSepL_cons.2
      iframe He Hl
    ipureintro
    intro k x h
    by_cases e : k = k0
    · subst e; simp
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm e)] at h
      exact List.mem_cons_of_mem _ (hm k x h)

end ghostmaps

section rabia
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS GooseGlobalGS.gooseAllG

instance isRabia_persistent_start (γ : RabiaNames) : Persistent (isRabia (GF := GF) γ) := by
  unfold isRabia; infer_instance

theorem valid_empty : Valid (fun _ => none) := by
  unfold Valid; intro k; rfl

/-- The writers: the clients, the servers and the orchestrator. -/
def allWriters : List Writer :=
  (List.range nC).map Writer.cli ++ ((List.range maxS).map Writer.srv ++ [Writer.orch])

/-- The facts' invariant at the empty record, with the key-value state's other half and each
writer's (empty) key set. -/
theorem rabia_alloc (E : CoPset) :
    ⊢ |={E}=> ∃ γr : RabiaNames, isRabia (GF := GF) γr ∗ kvHalf γr [] ∗
      ([∗list] c ∈ List.range nC, keysOf γr (.cli c) []) ∗
      ([∗list] k ∈ List.range maxS, keysOf γr (.srv k) []) ∗ keysOf γr .orch [] := by
  imod ghost_map_alloc_empty (GF := GF) (K := FKey) (V := FVal) with ⟨%γf, Hf⟩
  imod ghost_map_alloc_halves (GF := GF) ([] : List FKey) allWriters (by decide)
    with ⟨%γk, %KS, Hk, Hkm, Hkl, %hKS⟩
  imod ghostVar_alloc (GF := GF) ([] : List GoString) with ⟨%γv, Hv⟩
  icases (ghostVar_split_half γv 1 ([] : List GoString)).1 $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := ReqId) (V := GName) with ⟨%γq, Hq⟩
  imod ghost_map_alloc_empty (GF := GF) (K := ReqId) (V := Unit) with ⟨%γc, Hc⟩
  imod inv_alloc rabiaN E (rabiaInv (GF := GF) ⟨γf, γk, γv, γq, γc⟩) $$ [Hf Hk Hkm Hv1 Hq Hc]
    with #Hinv
  · inext
    unfold rabiaInv rabiaInvAt
    iexists (fun _ => none)
    isplitr
    · ipureintro; exact valid_empty
    iexists ∅, KS, 0
    iframe Hf Hk
    isplitr
    · ipureintro; intro k; rfl
    isplitr
    · iapply BigSepM.bigSepM_empty.2; itrivial
    isplitr
    · ipureintro
      intro k
      constructor
      · rintro ⟨W, -, K, hK, hk⟩
        rw [(hKS W K hK).1] at hk; simp at hk
      · rintro ⟨h, -⟩; exact absurd rfl h
    isplitl [Hkm]
    · unfold keysOf; iexact Hkm
    isplitr
    · ipureintro; exact ⟨fun s hs => absurd hs (Nat.not_lt_zero _), rfl⟩
    isplitl [Hv1]
    · unfold kvHalf; rw [cmdsAt_zero]; iexact Hv1
    isplitl [Hq]
    · iexists ∅; iframe Hq; ipureintro; intro r; simp
    isplitl [Hc]
    · iexists ∅; iframe Hc; ipureintro; intro r; simp
    iapply BigSepM.bigSepM_empty.2; itrivial
  imodintro
  iexists ⟨γf, γk, γv, γq, γc⟩
  unfold isRabia
  iframe Hinv
  isplitl [Hv2]
  · unfold kvHalf; iexact Hv2
  unfold allWriters
  icases BigSepL.bigSepL_append.1 $$ Hkl with ⟨Hl1, Hl2⟩
  icases BigSepL.bigSepL_append.1 $$ Hl2 with ⟨Hl2, Hl3⟩
  isplitl [Hl1]
  · iapply (show ([∗list] x ∈ (List.range nC).map Writer.cli, x ↪[γk]{#(1 : Qp).half}
        ([] : List FKey)) ⊢ [∗list] c ∈ List.range nC,
        keysOf (GF := GF) ⟨γf, γk, γv, γq, γc⟩ (.cli c) [] from by
      rw [BigSepL.bigSepL_map]; exact .rfl) $$ Hl1
  isplitl [Hl2]
  · iapply (show ([∗list] k ↦ x ∈ (List.range maxS).map Writer.srv, x ↪[γk]{#(1 : Qp).half}
        ([] : List FKey)) ⊢ [∗list] c ∈ List.range maxS,
        keysOf (GF := GF) ⟨γf, γk, γv, γq, γc⟩ (.srv c) [] from by
      rw [BigSepL.bigSepL_map]; exact .rfl) $$ Hl2
  · icases BigSepL.bigSepL_cons.1 $$ Hl3 with ⟨Ho, -⟩
    unfold keysOf; iexact Ho

/-- A mono-list at `[]`, as two halves of its authority. -/
theorem mono_list_alloc_halves {A : Type} [Pos.Countable A] :
    ⊢ |==> ∃ γ : GName, monoListAuthOwn (GF := GF) γ (1 : Qp).half ([] : List A) ∗
      monoListAuthOwn γ (1 : Qp).half ([] : List A) := by
  imod mono_list_own_alloc (GF := GF) ([] : List A) with ⟨%γ, Ha, -⟩
  imodintro
  iexists γ
  iapply ((monoListAuthOwn_fractional (GF := GF) γ ([] : List A)).fractional
    (1 : Qp).half (1 : Qp).half).1
  have h : ((1 : Qp).half + (1 : Qp).half) = 1 := Qp.half_add_half 1
  rw [h]
  iexact Ha

end rabia

end Perennial.rabia
