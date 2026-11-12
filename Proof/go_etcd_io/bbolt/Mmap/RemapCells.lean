/-
The new mapping's cells (U4d, `notes/bbolt-proof-plan.md`; `Mmap/Remap`'s plan, step 7): `mmap`'s
cells of `[0, len)` split by slot (`mapCells_scatter`, the inverse of `Mmap/Cells`'
`mapCells_gather`): the two meta slots, the store slots, the writer's slots and the partial last
slot; the meta slots' cells read against the writer's half of their page-cache bytes
(`cellsR_agree_bytes`, as the bboltfs example's `cellsR_agree`, by OsFs's `osCell_agree`), giving
the client halves of the metas' bytes (`cellsR_bytes`, the inverse of `bytes_cellsR`).
-/
module

public import Proof.go_etcd_io.bbolt.Mmap.Cells

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic go_etcd_io.bbolt

section cells
set_option linter.unusedSectionVars false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

omit hos in
/-- **The client halves of cells holding bytes are the bytes at a half** (the inverse of
`bytes_cellsR`). -/
theorem cellsR_bytes (base : Loc) (bs : List w8) :
    ∀ lo : Nat, cellsR (GF := GF) base lo bs.length (bytesVf lo bs) ⊢
      bytesPointsto (GF := GF) (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) bs := by
  induction bs with
  | nil =>
    intro lo
    iintro -
    simp only [bytesPointsto]
    ipureintro; trivial
  | cons b bs ih =>
    intro lo
    simp only [bytesPointsto, List.length_cons]
    rw [show bs.length + 1 = 1 + bs.length by omega]
    refine (cellsR_append base lo 1 bs.length _).1.trans ?_
    iintro ⟨Hb, Hbs⟩
    isplitl [Hb]
    · unfold cellsR
      rw [List.range'_one]
      icases BigSepL.bigSepL_singleton.1 $$ Hb with Hb
      simp only [bytesVf, Nat.sub_self, List.getD_cons_zero]
      iexact Hb
    · have e : base +ₗ ((lo : Nat) : Int) +ₗ 1 = base +ₗ (((lo + 1 : Nat) : Nat) : Int) := by
        rw [loc_add_assoc]; congr 1
      rw [e]
      iapply ih (lo + 1)
      iapply (cellsR_congr base (lo + 1) bs.length _ _ ?_).1 $$ Hbs
      intro i h1 _
      simp only [bytesVf]
      rw [show i - lo = (i - (lo + 1)) + 1 by omega, List.getD_cons_succ]

omit hos in
/-- The cells of `[0, 4096·k)` are the whole slots below `k`, at any values (the inverse of
`slots_cellsR`). -/
theorem cellsR_slots (base : Loc) (vf : Nat → val) :
    ∀ k, cellsR (GF := GF) base 0 (4096 * k) vf ⊢
      [∗list] s ∈ List.range k, cellsR (GF := GF) base (4096 * s) 4096 vf
  | 0 => by
    iintro -
    simp only [List.range_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | k + 1 => by
    rw [List.range_succ, show 4096 * (k + 1) = 4096 * k + 4096 by omega]
    refine (cellsR_append base 0 (4096 * k) 4096 vf).1.trans ?_
    refine Entails.trans ?_ (BigSepL.bigSepL_append (Φ := fun _ s =>
      cellsR (GF := GF) base (4096 * s) 4096 vf)).2
    refine sep_mono (cellsR_slots base vf k) ?_
    rw [Nat.zero_add]
    exact (BigSepL.bigSepL_singleton (Φ := fun _ s => cellsR (GF := GF) base (4096 * s) 4096 vf)).2

omit hos in
/-- **The cells of a new mapping** `(base, len)` by slot: the meta slots `0`, `1`, the store slots
`S` and the others `ws` (a partition of the slots below `len / 4096`), and the partial last slot. -/
theorem mapCells_scatter (base : Loc) (len : Nat) (vf : Nat → val) (S ws : List Nat)
    (hP : (0 :: 1 :: (S ++ ws)).Perm (List.range (len / 4096))) :
    cellsR (GF := GF) base 0 len vf ⊢
      cellsR (GF := GF) base 0 8192 vf ∗
      ([∗list] s ∈ S, ∃ vf, cellsR (GF := GF) base (4096 * s) 4096 vf) ∗
      ([∗list] s ∈ ws, ∃ vf, cellsR (GF := GF) base (4096 * s) 4096 vf) ∗
      (∃ vf, cellsR (GF := GF) base (4096 * (len / 4096)) (len % 4096) vf) := by
  have e : len = 4096 * (len / 4096) + len % 4096 := (Nat.div_add_mod len 4096).symm
  have hsplit := cellsR_append (GF := GF) base 0 (4096 * (len / 4096)) (len % 4096) vf
  rw [← e, Nat.zero_add] at hsplit
  refine hsplit.1.trans ?_
  iintro ⟨Hw, Hp⟩
  ihave Hw := cellsR_slots base vf _ $$ Hw
  ihave Hw := (BigSepL.bigSepL_perm (Φ := fun s => cellsR (GF := GF) base (4096 * s) 4096 vf)
    hP).2 $$ Hw
  icases BigSepL.bigSepL_cons.1 $$ Hw with ⟨H0, Hw⟩
  icases BigSepL.bigSepL_cons.1 $$ Hw with ⟨H1, Hw⟩
  icases (BigSepL.bigSepL_append (Φ := fun _ s => cellsR (GF := GF) base (4096 * s) 4096 vf)).1
    $$ Hw with ⟨HS, Hws⟩
  isplitl [H0 H1]
  · iapply (cellsR_append base 0 4096 4096 vf).2
    iframe H0
    iexact H1
  isplitl [HS]
  · iapply bigSepL_mono_cells $$ HS
  isplitl [Hws]
  · iapply bigSepL_mono_cells $$ Hws
  iexists vf; iexact Hp
where
  bigSepL_mono_cells {L : List Nat} :
      ([∗list] s ∈ L, cellsR (GF := GF) base (4096 * s) 4096 vf) ⊢
        [∗list] s ∈ L, ∃ vf, cellsR (GF := GF) base (4096 * s) 4096 vf :=
    BigSepL.bigSepL_mono fun {_ s} _ =>
      exists_intro (Ψ := fun vf => cellsR (GF := GF) base (4096 * s) 4096 vf) vf

end cells

section agree
set_option linter.unusedSectionVars false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {s : Stuckness} {E : CoPset}

theorem osBytes_cons' (p : GoString) (off : Nat) (dq : DFrac) (x : w8 × Bool)
    (xs : List (w8 × Bool)) :
    osBytes (GF := GF) p off dq (x :: xs) ⊣⊢ osByte (GF := GF) p off dq x ∗ osBytes p (off + 1) dq xs := by
  unfold osBytes osByte; exact bytesG_cons _ _ _ _ _ _

theorem osBytes_nil' (p : GoString) (off : Nat) (dq : DFrac) :
    osBytes (GF := GF) p off dq [] ⊣⊢ emp := by
  unfold osBytes; exact bytesG_nil _ _ _ _

omit hos in
theorem cellsR_cons' (base : Loc) (lo n : Nat) (vf : Nat → val) :
    cellsR (GF := GF) base lo (n + 1) vf ⊣⊢
      heapPointsto (base +ₗ ((lo : Nat) : Int)) (DFrac.own (1 : Qp).half) (vf lo) ∗
        cellsR base (lo + 1) n vf := by
  unfold cellsR
  rw [List.range'_succ]
  exact BigSepL.bigSepL_cons

/-- **Mapped cells `[lo, lo + xs.length)` hold the file's bytes `xs`**, of which the caller holds a
fraction, given the file's `OsMeta` (around any step `e`). -/
theorem cellsR_agree_bytes (e : Expr) (htv : toVal e = none) (p : GoString) (dqm : DFrac)
    (m : OsMeta) (base : Loc) (len : Nat) (hb : m.maps !! base = some len) (dqb : DFrac)
    (hE : ↑osN ⊆ E) (Φ : val → IProp GF) :
    ∀ (xs : List (w8 × Bool)) (lo : Nat) (vf : Nat → val), lo + xs.length ≤ len →
    ⊢ osInv (GF := GF) -∗ osMeta (GF := GF) p dqm (some m) -∗ osBytes (GF := GF) p lo dqb xs -∗
      cellsR (GF := GF) base lo xs.length vf -∗
      (osMeta (GF := GF) p dqm (some m) -∗ osBytes (GF := GF) p lo dqb xs -∗
        cellsR (GF := GF) base lo xs.length (bytesVf lo (xs.map Prod.fst)) -∗
        WP e @ s; E {{ Φ }}) -∗
      WP e @ s; E {{ Φ }}
  | [], lo, vf, _ => by
    iintro #Hinv Hm Hb Hc HΦ
    iapply HΦ $$ Hm Hb
    unfold cellsR; simp only [List.length_nil, List.range'_zero]
    iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: xs, lo, vf, hl => by
    simp only [List.length_cons] at hl
    iintro #Hinv Hm Hb Hc HΦ
    icases (osBytes_cons' _ _ _ _ _).1 $$ Hb with ⟨Hx, Hb⟩
    simp only [List.length_cons]
    icases (cellsR_cons' _ _ _ _).1 $$ Hc with ⟨Hcx, Hc⟩
    iapply osCell_agree e htv p dqm m base len lo hb (by omega) dqb x _ (vf lo) hE Φ
      $$ Hinv Hm Hx Hcx
    iintro %Hv Hm Hx Hcx
    iapply cellsR_agree_bytes e htv p dqm m base len hb dqb hE Φ xs (lo + 1) vf (by omega)
      $$ Hinv Hm Hb Hc
    iintro Hm Hb Hc
    iapply HΦ $$ Hm [Hx Hb] [Hcx Hc]
    · iapply (osBytes_cons' _ _ _ _ _).2; iframe
    · iapply (cellsR_cons' _ _ _ _).2
      simp only [bytesVf, Nat.sub_self, List.map_cons, List.getD_cons_zero]
      rw [← Hv]
      iframe Hcx
      iapply (cellsR_congr base (lo + 1) xs.length _ _ ?_).1 $$ Hc
      intro i h1 _
      simp only [bytesVf]
      rw [show i - lo = (i - (lo + 1)) + 1 by omega, List.getD_cons_succ]

end agree

end bbolt
end EtcdGrove
end Perennial
