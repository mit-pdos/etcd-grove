/-
The remap's cells (U4, `notes/bbolt-proof-plan.md`; design risk R5): `munmap` needs the client
halves of every cell of the mapping, `cellsR base 0 len`, which four owners hold, slot by slot:
the store slots (half, as `bytesPointsto`, from `store_gather`), the two meta slots (two quarters,
`metaCellsQ`), the writer's `W` slots and the partial last slot (`wCells`, as `cellsR`). Here:
`bytesPointsto` at a half as `cellsR` (`bytes_cellsR`), adjacent `cellsR` ranges joined
(`cellsR_join`), whole slots in any order joined into `[0, 4096·k)` (`slots_cellsR`), and the
gather itself (`mapCells_gather`) over a partition of the slots below `len / 4096`.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Inv.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

/-- **The slots below `k` partitioned**: the metas `0`, `1`, the store slots `S` (in `[2, k)`)
and the others `ws` (exactly the rest of `[2, k)`), both without repeats. -/
theorem slots_partition (k : Nat) (S ws : List Nat) (hk : 2 ≤ k) (hSn : S.Nodup)
    (hwn : ws.Nodup) (hS : ∀ s ∈ S, 2 ≤ s ∧ s < k)
    (hw : ∀ s, s ∈ ws ↔ 2 ≤ s ∧ s < k ∧ s ∉ S) :
    (0 :: 1 :: (S ++ ws)).Perm (List.range k) := by
  have hdisj : ∀ a ∈ S, ∀ b ∈ ws, a ≠ b := by
    intro a ha b hb hab; subst hab; exact ((hw a).1 hb).2.2 ha
  have hn : (0 :: 1 :: (S ++ ws)).Nodup := by
    refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, List.nodup_append.2 ⟨hSn, hwn, hdisj⟩⟩⟩
    · intro h
      simp only [List.mem_cons, List.mem_append] at h
      rcases h with h | h | h
      · omega
      · have := (hS 0 h).1; omega
      · have := ((hw 0).1 h).1; omega
    · intro h
      simp only [List.mem_append] at h
      rcases h with h | h
      · have := (hS 1 h).1; omega
      · have := ((hw 1).1 h).1; omega
  refine (List.perm_ext_iff_of_nodup hn List.nodup_range).2 fun a => ?_
  simp only [List.mem_cons, List.mem_append, List.mem_range]
  constructor
  · rintro (h | h | h | h)
    · omega
    · omega
    · exact (hS a h).2
    · exact ((hw a).1 h).2.1
  · intro h
    by_cases h0 : a = 0
    · exact .inl h0
    by_cases h1 : a = 1
    · exact .inr (.inl h1)
    by_cases hs : a ∈ S
    · exact .inr (.inr (.inl hs))
    · exact .inr (.inr (.inr ((hw a).2 ⟨by omega, h, hs⟩)))

section slots
variable [GooseExts]

/-- The store slots of `C`/`fl` (`slotsOf`) without repeats. -/
theorem slotsOf_nodup (C : CommitSt) (fl : FLPg) : (slotsOf C fl).Nodup :=
  nodup_list_dedup _

/-- A slot is a store slot iff it is a tree or pending slot. -/
theorem mem_slotsOf (C : CommitSt) (fl : FLPg) (s : Nat) :
    s ∈ slotsOf C fl ↔ s ∈ treeSlots C ∨ s ∈ pendSlots fl := by
  unfold slotsOf; rw [mem_list_dedup, List.mem_append]

end slots

section cells
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- The values of the cells holding `bs` from `lo` on. -/
def bytesVf (lo : Nat) (bs : List w8) : Nat → val :=
  fun i => LitV (LitByte (bs.getD (i - lo) (W8 0)))

omit hos in
/-- **Bytes at a half are the client halves of their cells.** -/
theorem bytes_cellsR (base : Loc) (bs : List w8) :
    ∀ lo : Nat, bytesPointsto (GF := GF) (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) bs ⊢
      cellsR base lo bs.length (bytesVf lo bs) := by
  induction bs with
  | nil =>
    intro lo
    unfold cellsR
    simp only [List.length_nil, List.range'_zero]
    iintro -
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons b bs ih =>
    intro lo
    simp only [bytesPointsto, List.length_cons]
    rw [show bs.length + 1 = 1 + bs.length by omega]
    refine Entails.trans ?_ (cellsR_append base lo 1 bs.length _).2
    iintro ⟨Hb, Hbs⟩
    isplitl [Hb]
    · unfold cellsR
      rw [List.range'_one]
      iapply BigSepL.bigSepL_singleton.2
      simp only [bytesVf, Nat.sub_self, List.getD_cons_zero]
      iexact Hb
    · have e : base +ₗ ((lo : Nat) : Int) +ₗ 1 = base +ₗ (((lo + 1 : Nat) : Nat) : Int) := by
        rw [loc_add_assoc]; congr 1
      rw [e]
      ihave Hbs := ih (lo + 1) $$ Hbs
      iapply (cellsR_congr base (lo + 1) bs.length _ _ ?_).1 $$ Hbs
      intro i h1 _
      simp only [bytesVf]
      rw [show i - lo = (i - (lo + 1)) + 1 by omega, List.getD_cons_succ]

omit hos in
/-- **Adjacent ranges of cells join**, each with its own values. -/
theorem cellsR_join (base : Loc) (lo n1 n2 : Nat) :
    (∃ vf, cellsR (GF := GF) base lo n1 vf) ∗ (∃ vf, cellsR (GF := GF) base (lo + n1) n2 vf) ⊢
      ∃ vf, cellsR (GF := GF) base lo (n1 + n2) vf := by
  iintro ⟨⟨%vf1, H1⟩, ⟨%vf2, H2⟩⟩
  iexists (fun i => if i < lo + n1 then vf1 i else vf2 i)
  iapply (cellsR_append base lo n1 n2 _).2
  isplitl [H1]
  · iapply (cellsR_congr base lo n1 _ _ ?_).1 $$ H1
    intro i _ h2; simp [h2]
  · iapply (cellsR_congr base (lo + n1) n2 _ _ ?_).1 $$ H2
    intro i h1 _; simp [Nat.not_lt.2 h1]

omit hos in
/-- **Whole slots in any order are the cells of `[0, 4096·k)`**, when they are the slots below
`k`. -/
theorem slots_cellsR (base : Loc) (S : List Nat) (k : Nat) (hS : S.Perm (List.range k)) :
    ([∗list] s ∈ S, ∃ vf, cellsR (GF := GF) base (4096 * s) 4096 vf) ⊢
      ∃ vf, cellsR (GF := GF) base 0 (4096 * k) vf := by
  refine (BigSepL.bigSepL_perm hS).1.trans ?_
  clear hS
  induction k with
  | zero =>
    iintro -
    iexists (fun _ => LitV (LitByte (W8 0)))
    unfold cellsR
    simp only [Nat.mul_zero, List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | succ k ih =>
    rw [List.range_succ]
    refine (BigSepL.bigSepL_append (Φ := fun _ s => iprop(∃ vf, cellsR (GF := GF) base (4096 * s)
      4096 vf))).1.trans ?_
    iintro ⟨Hk, Hl⟩
    ihave Hk := ih $$ Hk
    ihave Hl := (BigSepL.bigSepL_singleton (Φ := fun _ s => iprop(∃ vf, cellsR (GF := GF) base
      (4096 * s) 4096 vf))).1 $$ Hl
    rw [show 4096 * (k + 1) = 4096 * k + 4096 by omega]
    iapply cellsR_join base 0 (4096 * k) 4096
    isplitl [Hk]
    · iexact Hk
    · rw [Nat.zero_add]; iexact Hl

omit hos in
/-- **The cells of a whole mapping** `(base, len)` from its slots' owners: the meta slots' bytes
at a half (`m0`, `m1`, 4096 bytes each: two `metaCellsQ` quarters), the store slots' at a half
(`store_gather`'s, 4096 bytes each), the other slots' cells (`ws`: the writer's `W` slots in the
mapping), and the partial last slot's; the store and `ws` slots with `0`, `1` partition the slots
below `len / 4096`. -/
theorem mapCells_gather (base : Loc) (len : Nat) (m0 m1 : List w8) (S ws : List Nat)
    (bs : Nat → List w8) (hm0 : m0.length = 4096) (hm1 : m1.length = 4096)
    (hbs : ∀ s ∈ S, (bs s).length = 4096)
    (hP : (0 :: 1 :: (S ++ ws)).Perm (List.range (len / 4096))) :
    bytesPointsto (GF := GF) base (DFrac.own (1 : Qp).half) m0 ∗
      bytesPointsto (GF := GF) (base +ₗ (4096 : Int)) (DFrac.own (1 : Qp).half) m1 ∗
      ([∗list] s ∈ S, bytesPointsto (GF := GF) (base +ₗ ((4096 * s : Nat) : Int))
        (DFrac.own (1 : Qp).half) (bs s)) ∗
      ([∗list] s ∈ ws, ∃ vf, cellsR (GF := GF) base (4096 * s) 4096 vf) ∗
      (∃ vf, cellsR (GF := GF) base (4096 * (len / 4096)) (len % 4096) vf) ⊢
    ∃ vf, cellsR (GF := GF) base 0 len vf := by
  iintro ⟨H0, H1, HS, Hws, Hp⟩
  have h0 : bytesPointsto (GF := GF) base (DFrac.own (1 : Qp).half) m0 ⊢
      ∃ vf, cellsR (GF := GF) base (4096 * 0) 4096 vf := by
    have h := bytes_cellsR (GF := GF) base m0 0
    rw [hm0, Int.natCast_zero, loc_add_0] at h
    exact h.trans (exists_intro (Ψ := fun vf => cellsR (GF := GF) base 0 4096 vf) _)
  ihave H0 := h0 $$ H0
  have h1 : bytesPointsto (GF := GF) (base +ₗ (4096 : Int)) (DFrac.own (1 : Qp).half) m1 ⊢
      ∃ vf, cellsR (GF := GF) base (4096 * 1) 4096 vf := by
    have h := bytes_cellsR (GF := GF) base m1 4096
    have e : (((4096 : Nat) : Nat) : Int) = (4096 : Int) := by omega
    rw [hm1, e] at h
    exact h.trans (exists_intro (Ψ := fun vf => cellsR (GF := GF) base 4096 4096 vf) _)
  ihave H1 := h1 $$ H1
  ihave HS : [∗list] s ∈ S, ∃ vf, cellsR (GF := GF) base (4096 * s) 4096 vf $$ [HS]
  · iapply BigSepL.bigSepL_mono ?_ $$ HS
    intro k s hk
    have hl := hbs s (List.mem_of_getElem? hk)
    have h := bytes_cellsR (GF := GF) base (bs s) (4096 * s)
    rw [hl] at h
    exact h.trans (exists_intro (Ψ := fun vf => cellsR (GF := GF) base (4096 * s) 4096 vf) _)
  ihave Hall : [∗list] s ∈ 0 :: 1 :: (S ++ ws), ∃ vf, cellsR (GF := GF) base (4096 * s) 4096 vf
    $$ [H0 H1 HS Hws]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [H0]
    · iexact H0
    iapply BigSepL.bigSepL_cons.2
    isplitl [H1]
    · iexact H1
    iapply (BigSepL.bigSepL_append (Φ := fun _ s => iprop(∃ vf, cellsR (GF := GF) base (4096 * s)
      4096 vf))).2
    iframe
  ihave Hall := slots_cellsR base _ _ hP $$ Hall
  have e : len = 4096 * (len / 4096) + len % 4096 := (Nat.div_add_mod len 4096).symm
  generalize hq : len / 4096 = q at *
  generalize hr : len % 4096 = r at *
  subst e
  iapply cellsR_join base 0 (4096 * q) r
  iframe Hall; rw [Nat.zero_add]; iexact Hp

end cells

end bbolt
end EtcdGrove
end Perennial
