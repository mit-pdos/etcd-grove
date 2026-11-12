/-
U7's (`notes/bbolt-proof-plan.md`) facts for `node.read`: a page's bytes through its source
(`srcLoc`), and the inodes `ReadInodeFromPage` returns as the page's entries with their sources
(`wOwn`), when every element's key and value lie inside the page (`pageFits`).
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Ctx
public import Proof.go_etcd_io.bbolt.internal.common.Lemmas.Bytes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

namespace Write

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- Every element's key and value lie inside the page (`leafWF`/`branchWF` give it). -/
def elemsIn (pg : List w8) : Prop := ∀ i < pageCount pg, elemEnd pg i ≤ pg.length

theorem bytesAt_bytesAt (P : List w8) (off n k m : Nat) (h : k + m ≤ n) :
    bytesAt (bytesAt P off n) k m = bytesAt P (off + k) m := by
  unfold bytesAt
  rw [List.drop_take, List.take_take, List.drop_drop, Nat.min_eq_left (by omega)]

theorem bytesAt_length (P : List w8) (off n : Nat) (h : off + n ≤ P.length) :
    (bytesAt P off n).length = n := by
  unfold bytesAt; simp; omega

theorem inViewLoc_sub (v : View) (p : Loc) (pg : List w8) (k m : Nat) (h : inViewLoc v p pg)
    (hk : k + m ≤ pg.length) : inViewLoc v (p +ₗ (k : Int)) (bytesAt pg k m) := by
  obtain ⟨id, P, off, hP, hlen, hbs, rfl⟩ := h
  refine ⟨id, P, off + k, hP, ?_, ?_, ?_⟩
  · rw [bytesAt_length _ _ _ hk]; omega
  · rw [bytesAt_length _ _ _ hk, ← hbs, bytesAt_bytesAt _ _ _ _ _ hk]
  · have e : (((id * 4096 + off : Nat) : Int) + (k : Int)) = ((id * 4096 + (off + k) : Nat) : Int) := by
      omega
    rw [loc_add_assoc, e]

end pure

section bi
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance srcLoc_persistent (v : View) (p : Loc) (src : Src) (bs : List w8) :
    Persistent (srcLoc (GF := GF) v p src bs) := by
  cases src <;> unfold srcLoc <;> infer_instance

/-- **A page's bytes through its source**, and back. -/
theorem srcLoc_acc (q : Qp) (v : View) (p : Loc) (src : Src) (pg : List w8) :
    srcLoc (GF := GF) v p src pg ∗ viewCells q v ⊢ ∃ dq : DFrac, bytesPointsto p dq pg ∗
      (bytesPointsto p dq pg -∗ viewCells q v) := by
  cases src with
  | stale => unfold srcLoc; iintro ⟨%H, -⟩; exact H.elim
  | own dq0 =>
    unfold srcLoc
    iintro ⟨#Hb, Hv⟩
    iexists DFrac.discard
    iframe Hb
    iintro _
    iexact Hv
  | view =>
    unfold srcLoc
    iintro ⟨%Hin, Hv⟩
    iapply (viewCells_loc_acc q v p pg Hin)
    iexact Hv

/-- A sub-slice of a page, from its source. -/
theorem srcLoc_sub (v : View) (p : Loc) (src : Src) (pg : List w8) (k m : Nat)
    (hs : src ≠ Src.stale) (hk : k + m ≤ pg.length) (hm : m < 2 ^ 32) (hp : 0 < p.addr)
    (hpm : p.addr + pg.length ≤ maxAddr) :
    srcLoc (GF := GF) v p src pg ⊢
      srcOwn v (bslice (p +ₗ (k : Int)) m) src (bytesAt pg k m) := by
  have hl := bytesAt_length pg k m hk
  cases src with
  | stale => exact absurd rfl hs
  | view =>
    unfold srcLoc srcOwn
    iintro %Hin
    ipureintro
    refine ⟨?_, by omega, ?_, ?_⟩ <;> simp only [bslice, hl]
    exact inViewLoc_sub v p pg k m Hin hk
  | own dq0 =>
    unfold srcLoc srcOwn
    iintro #Hb
    ihave Hs := internal.common.bytesPointsto_sub p pg (bytesAt pg k m) k (by omega) (by rw [hl]; rfl) $$ Hb
    have hp' : 0 < (p +ₗ (k : Int)).addr := by simp [Loc.add]; omega
    icases (internal.common.bytesPointsto_ownSlice (p +ₗ (k : Int)) DFrac.discard (bytesAt pg k m) hp'
      (by omega)).1 $$ Hs with Hs
    have e : bslice (p +ₗ (k : Int)) m = slice.mk (p +ₗ (k : Int))
        (W64 ((bytesAt pg k m).length : Int)) (W64 ((bytesAt pg k m).length : Int)) := by
      rw [hl]; rfl
    rw [e]
    iexact Hs

/-- A persistent fact gives a pointwise `[∗list]` over two maps of a range. -/
theorem bigSepL2_range_of {A B : Type} (P : IProp GF) [Persistent P] (f : Nat → A) (g : Nat → B)
    (Φ : A → B → IProp GF) :
    ∀ n, (∀ i < n, P ⊢ Φ (f i) (g i)) →
      P ⊢ [∗list] x;y ∈ (List.range n).map f;(List.range n).map g, Φ x y
  | 0, _ => by
    simp only [List.range_zero, List.map_nil]
    iintro _; iapply (BigSepL2.bigSepL2_nil (PROP := IProp GF) (Φ := fun _ x y => Φ x y)).2; iempintro
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.map_append, List.map_singleton,
      List.map_singleton]
    iintro #HP
    iapply (BigSepL2.bigSepL2_snoc (Φ := fun _ x y => Φ x y)).2
    isplitl
    · iapply (bigSepL2_range_of P f g Φ n (fun i hi => h i (by omega)))
      iexact HP
    · iapply (h n (by omega))
      iexact HP

theorem w32_ofNat_toNat (x : w32) : W32 (x.toNat : Int) = x := by
  apply BitVec.eq_of_toNat_eq; simp

theorem w64_ofNat_toNat (x : w64) : W64 (x.toNat : Int) = x := by
  apply BitVec.eq_of_toNat_eq; simp

/-- An entry of page `pg` read with the source `src` (`pageWsAs`). -/
def pwAs (pg : List w8) (src : Src) (w : WEntry) : WEntry :=
  { w with ks := src, vs := if pageFlags pg = leafPageFlag then src else Src.own DFrac.discard }

theorem pageWsAs_eq (pg : List w8) (src : Src) : pageWsAs pg src = (pageWs pg).map (pwAs pg src) :=
  rfl

/-- Inode `i` of a page is its entry `i` with the source. -/
theorem wOwn_pageInode (v : View) (p : Loc) (src : Src) (pg : List w8) (hs : src ≠ Src.stale)
    (hfit : elemsIn pg) (hp : 0 < p.addr) (hpm : p.addr + pg.length ≤ maxAddr) (i : Nat)
    (hi : i < pageCount pg) :
    srcLoc (GF := GF) v p src pg ⊢
      wOwn v true (pageInodeAt p pg i) (pwAs pg src (pageW pg i)) := by
  have he := hfit i hi
  unfold elemEnd at he
  have hk32 : leafKsize pg i < 2 ^ 32 := by unfold leafKsize; exact BitVec.isLt _
  have hv32 : leafVsize pg i < 2 ^ 32 := by unfold leafVsize; exact BitVec.isLt _
  have hb32 : branchKsize pg i < 2 ^ 32 := by unfold branchKsize; exact BitVec.isLt _
  unfold wOwn pageInodeAt pwAs pageW
  by_cases hl : pageFlags pg = leafPageFlag
  · simp only [hl, ↓reduceIte] at he ⊢
    iintro #H
    isplitr
    · ipureintro; simp only [true_and, and_true]; apply BitVec.eq_of_toNat_eq; simp [leafFlags]
    isplitl
    · unfold keySliceAt leafKey; simp only [hl, ↓reduceIte]
      iapply (srcLoc_sub v p src pg _ _ hs (by omega) hk32 hp hpm)
      iexact H
    · unfold valSliceAt leafValue
      iapply (srcLoc_sub v p src pg _ _ hs (by omega) hv32 hp hpm)
      iexact H
  · simp only [hl, ↓reduceIte] at he ⊢
    iintro #H
    isplitr
    · ipureintro; simp only [true_and, and_true]; apply BitVec.eq_of_toNat_eq; simp [branchPgid]
    isplitl
    · unfold keySliceAt branchKey; simp only [hl, ↓reduceIte]
      iapply (srcLoc_sub v p src pg _ _ hs (by omega) hb32 hp hpm)
      iexact H
    · unfold srcOwn
      iapply ownSlice_nil

/-- **The inodes `ReadInodeFromPage` returns are the page's entries** with their source, when
every element lies inside the page. -/
theorem wOwns_pageInodes (v : View) (p : Loc) (src : Src) (pg : List w8) (hs : src ≠ Src.stale)
    (hfit : elemsIn pg) (hp : 0 < p.addr) (hpm : p.addr + pg.length ≤ maxAddr) :
    srcLoc (GF := GF) v p src pg ⊢
      [∗list] it;w ∈ pageInodesAt p pg;pageWsAs pg src, wOwn v true it w := by
  rw [pageWsAs_eq]
  unfold pageInodesAt pageWs
  rw [List.map_map]
  exact bigSepL2_range_of _ _ _ (fun it w => wOwn v true it w) (pageCount pg)
    (fun i hi => wOwn_pageInode v p src pg hs hfit hp hpm i hi)

end bi

end Write

end bbolt
end EtcdGrove
end Perennial
