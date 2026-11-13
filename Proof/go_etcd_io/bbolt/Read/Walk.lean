/-
The reader's page walk (U6, `notes/bbolt-proof-plan.md`; `Tx.forEachPage_r`): `pageWalkF`
unfolded at a page, a branch's children's walks split around one child, and a page's header and
elements read out of `rdTxK` (the reader alone, no bucket).
-/
module

public import Proof.go_etcd_io.bbolt.Read.RCtx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pure
variable [GooseExts]

/-- `pageWalkF` at a page: the page, then (a branch) its children's walks in order. -/
theorem pageWalkF_succ (P : Pages) (n : Nat) (ids : List Nat) (id : Nat) (pg : List w8)
    (hl : ids.getLast? = some id) (hp : P !! id = some pg) :
    pageWalkF P (n + 1) ids = (id, ids) :: (if pageFlags pg = branchPageFlag
      then (List.range (pageCount pg)).flatMap fun j => pageWalkF P n (ids ++ [branchPgid pg j])
      else []) := by
  simp only [pageWalkF, hl, hp]

omit [GooseExts] in
/-- The concatenation over `[0, c)` split around `j`. -/
theorem flatMap_range_split {α : Type} (f : Nat → List α) (c j : Nat) (h : j < c) :
    (List.range c).flatMap f =
      (List.range j).flatMap f ++ f j ++ ((List.range c).drop (j + 1)).flatMap f := by
  conv => lhs; rw [← List.take_append_drop (j + 1) (List.range c)]
  rw [List.take_range, Nat.min_eq_left (by omega), List.range_succ, List.flatMap_append,
    List.flatMap_append]
  simp

end pure

section acc
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

omit package_sem in
/-- The bounds of a page of the reader's view, keeping the reader. -/
theorem rdTxK_page_bounds (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (id : Nat) (pg : List w8) (h : v.pages !! id = some pg) (hne : pg ≠ []) :
    rdTxK (GF := GF) K tx src q T v ⊢ rdTxK K tx src q T v ∗
      ⌜0 < (pageLoc v id).addr ∧ (pageLoc v id).addr + pg.length ≤ maxAddr⌝ := by
  iintro H
  icases rdTxK_page_acc K tx src q T v id pg h $$ H with ⟨%dq, Hb, Hback⟩
  icases Read.bytesPointsto_bounds _ dq pg hne $$ Hb with ⟨Hb, %Hbd⟩
  ihave H := Hback $$ Hb
  iframe
  ipureintro; exact Hbd

/-- **The header of a page of the reader's view, read**, and back. -/
theorem rdTxK_hdr_acc (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (id : Nat) (pg : List w8) (h : v.pages !! id = some pg) (h16 : 16 ≤ pg.length) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dq,
      pageLoc v id ↦{dq} pageHdr pg ∗ (pageLoc v id ↦{dq} pageHdr pg -∗ rdTxK K tx src q T v) := by
  iintro H
  icases rdTxK_page_acc K tx src q T v id pg h $$ H with ⟨%dq, Hb, Hback⟩
  icases Read.bytesPointsto_bounds _ dq pg (by intro e; simp [e] at h16) $$ Hb with ⟨Hb, %Hbd⟩
  icases bytesPointsto_view_read (V := Page) (pageLoc v id) dq pg 0 (pageLoc v id) (by simp) (by omega) Hbd.1 $$ Hb
    with ⟨Hh, Hhb⟩
  iexists dq
  rw [show pageHdr pg = (decode (List.take 16 (List.drop 0 pg)) : Page) from rfl]
  iframe Hh
  iintro Hh
  iapply Hback
  iapply Hhb
  iexact Hh

omit package_sem in
/-- **Element `i` of a page of the reader's view, read** (its 16 bytes as an element view), and
back. -/
theorem rdTxK_elem_acc {V : Type} [ByteEncoding V 16] [TypedPointsto (GF := GF) V]
    [BytesView (GF := GF) V] (K : BC) (tx : Loc) (src : PairSrc) (q : Qp) (T : TxView) (v : View)
    (id : Nat) (pg : List w8) (h : v.pages !! id = some pg) (i : Nat)
    (hi : elemOff i + 16 ≤ pg.length) :
    rdTxK (GF := GF) K tx src q T v ⊢ ∃ dq,
      (pageLoc v id +ₗ ((elemOff i : Nat) : Int)) ↦{dq} (decode (bytesAt pg (elemOff i) 16) : V) ∗
      ((pageLoc v id +ₗ ((elemOff i : Nat) : Int)) ↦{dq} (decode (bytesAt pg (elemOff i) 16) : V) -∗
        rdTxK K tx src q T v) := by
  iintro H
  icases rdTxK_page_acc K tx src q T v id pg h $$ H with ⟨%dq, Hb, Hback⟩
  icases Read.bytesPointsto_bounds _ dq pg (by intro e; simp [e] at hi) $$ Hb with ⟨Hb, %Hbd⟩
  icases bytesPointsto_view_read (V := V) (pageLoc v id) dq pg (elemOff i) _ rfl hi Hbd.1 $$ Hb
    with ⟨Hh, Hhb⟩
  iexists dq
  rw [show bytesAt pg (elemOff i) 16 = List.take 16 (List.drop (elemOff i) pg) from rfl]
  iframe Hh
  iintro Hh
  iapply Hback
  iapply Hhb
  iexact Hh

end acc

end bbolt
end EtcdGrove
end Perennial
