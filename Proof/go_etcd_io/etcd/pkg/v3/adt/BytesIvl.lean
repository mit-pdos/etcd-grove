/-
The interval tree over **bytes-affine** intervals (`BytesAffineComparable`: a byte slice, compared
by `bytes.Compare`, the empty slice the top): a bytes-affine interval as the Go `Interval`
(`bytesIvl`, what `NewBytesAffineInterval(b, e)` returns; 2026-10-14, unit P2), and the tree's
ownership predicate over them (`ownIvtB`; the auth plan's S2, 2026-10-23), the string-affine
`ownIvt` (`Defs.lean`) with each key a read-only slice holding it: the model is the same
(`Model.lean`, entries over the keys' contents, `GoString`), the nodes hold the slices.

**The trust boundary.** The tree's algorithmic proof (`Insert`, `Intersects`, `Visit`; the
fixups, the rotations, the maxima) is done for string-affine keys only; its generalization to a
comparator (the key type, its Go value, its `Compare` and the resource a comparison needs: a
slice's contents for bytes) is the pending stage of `notes/auth-plan.md` ("S2b"). Until then the
three facts the auth store's permission cache needs are **axioms** here, stated exactly as the
string-affine specs are (`Spec/.../adt/intervalTree__{Insert,Intersects}.lean`) and as `Contains`'
pure meaning (`Contains.lean`, `containsRes`: the loop transcribed), over the predicate's concrete
definition: `intervalTree.wp_Insert_bytes`, `wp_Intersects_bytes`, `wp_Contains_bytes`
(`etc/tcb-baseline.txt`; `notes/decisions.md`, "S2 of the auth plan"). What is proved here: the
empty tree is a bytes-affine tree (`ownIvtB_of_empty`: `NewIntervalTree`'s string-affine
postcondition), a built tree can be made read-only (`ownIvtB_persist`, the cache's trees are never
modified), and the entries are in the tree's order (`ownIvtB_sorted`).
-/
module

public import Proof.go_etcd_io.etcd.pkg.v3.adt.NodeLemmas
public import Proof.go_etcd_io.etcd.pkg.v3.adt.Contains

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace adt

open Iris Iris.BI go_etcd_io.etcd.pkg.v3.adt

/-- A slice's length is zero only for the empty contents. -/
theorem slice_len_eq_zero {s : GoSlice} {bs : GoString}
    (h : bs.length = sint.nat s.len ∧ 0 ≤ sint.Z s.len) : s.len = W64 0 ↔ bs = [] := by
  constructor
  · intro h0
    have : bs.length = 0 := by rw [h.1, h0]; rfl
    exact List.eq_nil_of_length_eq_zero this
  · intro hn
    subst hn
    have := h.1
    simp only [List.length_nil] at this
    have := h.2
    word

section defs
variable [ext : FfiSyntax] [GoGlobalContext]

/-- The bytes-affine interval value `[b, e)` (slices `b`, `e`) as the Go `Interval`. -/
def bytesIvl (b e : GoSlice) : Interval :=
  { Begin' := interface.mkOk BytesAffineComparable.ty #b,
    End' := interface.mkOk BytesAffineComparable.ty #e }

@[simp] theorem bytesIvl_Begin (b e : GoSlice) :
    (bytesIvl b e).Begin' = interface.mkOk BytesAffineComparable.ty #b := rfl
@[simp] theorem bytesIvl_End (b e : GoSlice) :
    (bytesIvl b e).End' = interface.mkOk BytesAffineComparable.ty #e := rfl

end defs

section reprs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.adt.Assumptions]

open Iris.ProofMode

/-- A points-to made read-only. -/
theorem tp_persist {V : Type} [TypedPointsto (GF := GF) V] (l : Loc) (v : V) (dq : DFrac) :
    (l ↦{dq} v : IProp GF) ⊢ |==> l ↦□ v :=
  (typedPointsto_dfractional (GF := GF) l v).dfractional_persist dq

/-- The subtree at `n` (child of `p`) holds the model `t`, at `dq`, with the sentinel `s`, over
bytes-affine keys: as `ownNode` (`Defs.lean`), with the entry's begin and end and the subtree's
`max` each a slice (read-only) holding the key. -/
def ownNodeB (s : Loc) (dq : DFrac) : Loc → Loc → RbT Entry → IProp GF
  | _, n, .leaf => iprop(⌜n = s⌝)
  | p, n, .node c l e r => iprop(∃ (lp rp : Loc) (sb se sm : GoSlice), ⌜n ≠ s ∧ n ≠ null⌝ ∗
      n.[intervalNode, go!"iv"] ↦{dq} ({ Ivl' := bytesIvl sb se, Val' := e.2 } : IntervalValue) ∗
      sb ↦*□ e.1.1 ∗ se ↦*□ e.1.2 ∗
      n.[intervalNode, go!"max"] ↦{dq} interface.mkOk BytesAffineComparable.ty #sm ∗
      sm ↦*□ nodeMax l e r ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNodeB s dq n lp l ∗ ownNodeB s dq n rp r)

theorem ownNodeB_leaf (s : Loc) (dq : DFrac) (p n : Loc) :
    ownNodeB (GF := GF) s dq p n .leaf = iprop(⌜n = s⌝) := by rw [ownNodeB]

theorem ownNodeB_node (s : Loc) (dq : DFrac) (p n : Loc) (c : RbColor) (l : RbT Entry) (e : Entry)
    (r : RbT Entry) :
    ownNodeB (GF := GF) s dq p n (.node c l e r) =
      iprop(∃ (lp rp : Loc) (sb se sm : GoSlice), ⌜n ≠ s ∧ n ≠ null⌝ ∗
      n.[intervalNode, go!"iv"] ↦{dq} ({ Ivl' := bytesIvl sb se, Val' := e.2 } : IntervalValue) ∗
      sb ↦*□ e.1.1 ∗ se ↦*□ e.1.2 ∗
      n.[intervalNode, go!"max"] ↦{dq} interface.mkOk BytesAffineComparable.ty #sm ∗
      sm ↦*□ nodeMax l e r ∗
      n.[intervalNode, go!"left"] ↦{dq} lp ∗
      n.[intervalNode, go!"right"] ↦{dq} rp ∗
      n.[intervalNode, go!"parent"] ↦{dq} p ∗
      n.[intervalNode, go!"c"] ↦{dq} colorW c ∗
      ownNodeB s dq n lp l ∗ ownNodeB s dq n rp r) := by rw [ownNodeB]

set_option synthInstance.maxSize 512 in
theorem ownNodeB_persistent (s p n : Loc) :
    ∀ T : RbT Entry, Persistent (ownNodeB (GF := GF) s .discard p n T)
  | .leaf => by rw [ownNodeB_leaf]; infer_instance
  | .node c l e r => by
    rw [ownNodeB_node]
    have hl : ∀ lp, Persistent (ownNodeB (GF := GF) s .discard n lp l) :=
      fun lp => ownNodeB_persistent s n lp l
    have hr : ∀ rp, Persistent (ownNodeB (GF := GF) s .discard n rp r) :=
      fun rp => ownNodeB_persistent s n rp r
    infer_instance

instance ownNodeB_persistent_inst (s p n : Loc) (T : RbT Entry) :
    Persistent (ownNodeB (GF := GF) s .discard p n T) := ownNodeB_persistent s p n T

/-- A subtree made read-only. -/
theorem ownNodeB_persist (s : Loc) : ∀ (T : RbT Entry) (p n : Loc),
    ownNodeB (GF := GF) s (DFrac.own 1) p n T ⊢ |==> ownNodeB s .discard p n T
  | .leaf, p, n => by rw [ownNodeB_leaf, ownNodeB_leaf]; iintro H; imodintro; iexact H
  | .node c l e r, p, n => by
    rw [ownNodeB_node, ownNodeB_node]
    iintro ⟨%lp, %rp, %sb, %se, %sm, %Hn, Hiv, Hsb, Hse, Hmx, Hsm, Hl, Hr, Hp, Hc, HL, HR⟩
    imod tp_persist _ _ _ $$ Hiv with Hiv
    imod tp_persist _ _ _ $$ Hmx with Hmx
    imod tp_persist _ _ _ $$ Hl with Hl
    imod tp_persist _ _ _ $$ Hr with Hr
    imod tp_persist _ _ _ $$ Hp with Hp
    imod tp_persist _ _ _ $$ Hc with Hc
    imod ownNodeB_persist s l n lp $$ HL with HL
    imod ownNodeB_persist s r n rp $$ HR with HR
    imodintro
    iexists lp, rp, sb, se, sm
    iframe
    ipureintro; exact Hn

/-- The sentinel, at `dq` (`ownSentinel` over a `DFrac`). -/
def ownSentinelB (s : Loc) (dq : DFrac) : IProp GF :=
  iprop(∃ v : intervalNode, s ↦{dq} v)

instance ownSentinelB_persistent (s : Loc) : Persistent (ownSentinelB (GF := GF) s .discard) := by
  unfold ownSentinelB; infer_instance

include sem package_sem in
/-- **The tree at `t` holds the entries `L` over bytes-affine keys**, at `dq`: as `ownIvt`
(`Defs.lean`), with `ownNodeB`'s nodes. -/
def ownIvtB (t : Loc) (L : List Entry) (dq : DFrac) : IProp GF :=
  iprop(∃ (tv : intervalTree) (T : RbT Entry),
    t ↦{dq} tv ∗ ownSentinelB tv.sentinel' dq ∗
    ownNodeB tv.sentinel' dq tv.sentinel' tv.root' T ∗
    ⌜T.inorder = L ∧ RbOk T ∧ IvSorted L ∧ tv.count' = W64 L.length ∧ L.length < 2 ^ 63⌝)

instance ownIvtB_persistent (t : Loc) (L : List Entry) :
    Persistent (ownIvtB (GF := GF) t L .discard) := by
  unfold ownIvtB; infer_instance

/-- The entries are in the tree's order. -/
theorem ownIvtB_sorted (t : Loc) (L : List Entry) (dq : DFrac) :
    ownIvtB (GF := GF) t L dq ⊢ ⌜IvSorted L⌝ := by
  unfold ownIvtB
  iintro ⟨%tv, %T, -, -, -, %H⟩
  ipureintro; exact H.2.2.1

/-- A built tree made read-only. -/
theorem ownIvtB_persist (t : Loc) (L : List Entry) :
    ownIvtB (GF := GF) t L (DFrac.own 1) ⊢ |==> ownIvtB t L .discard := by
  unfold ownIvtB ownSentinelB
  iintro ⟨%tv, %T, Ht, ⟨%sv, Hs⟩, Hn, %H⟩
  imod tp_persist _ _ _ $$ Ht with Ht
  imod tp_persist _ _ _ $$ Hs with Hs
  imod ownNodeB_persist _ _ _ _ $$ Hn with Hn
  imodintro
  iexists tv, T
  iframe
  ipureintro; exact H

/-- The empty tree (`NewIntervalTree`'s, `ownIvt t [] 1`) is a bytes-affine tree: only the
sentinel, which holds no key. -/
theorem ownIvtB_of_empty (t : Loc) : ownIvt (GF := GF) t [] 1 ⊢ ownIvtB t [] (DFrac.own 1) := by
  unfold ownIvt ownIvtB ownSentinel ownSentinelB
  iintro ⟨%tv, %T, Ht, Hs, Hn, %H⟩
  obtain ⟨hio, hok, hsorted, hcount, hlen⟩ := H
  cases T with
  | node c l e r => simp at hio
  | leaf =>
    ihave %Hroot := ownNode_leaf_open _ _ _ _ $$ Hn
    iexists tv, .leaf
    rw [ownNodeB_leaf]
    iframe
    ipureintro
    exact ⟨Hroot, rfl, hok, hsorted, hcount, hlen⟩

/-! ## The trust boundary: the tree's facts over bytes-affine keys -/

/-- **`t.Insert(ivl, v)` over bytes-affine keys** (`intervalTree.Insert.spec` with `bytesIvl`:
the slices read-only, the keys their contents). An axiom pending the tree's comparator
generalization (the file header). -/
axiom intervalTree.wp_Insert_bytes (t : Loc) (L : List Entry) (b e : GoSlice) (bs es : GoString)
    (v : GoInterface) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ownIvtB t L (DFrac.own 1) ∗
      b ↦*□ bs ∗ e ↦*□ es ∗ ⌜L.length + 1 < 2 ^ 63⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Insert"))
      (Val #(bytesIvl b e))) (Val #v))
  {{ RET #(); ownIvtB t (ivtInsert ((bs, es), v) L) (DFrac.own 1) }}

/-- **`t.Intersects(ivl)` over bytes-affine keys** (`intervalTree.Intersects.spec` with
`bytesIvl`): whether some entry overlaps the query. An axiom pending the tree's comparator
generalization. -/
axiom intervalTree.wp_Intersects_bytes (t : Loc) (L : List Entry) (b e : GoSlice) (bs es : GoString)
    (db de dq : DFrac) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ownIvtB t L dq ∗
      b ↦*{db} bs ∗ e ↦*{de} es }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Intersects"))
      (Val #(bytesIvl b e)))
  {{ RET #(decide (stab (bs, es) L ≠ [])); ownIvtB t L dq ∗ b ↦*{db} bs ∗ e ↦*{de} es }}

/-- **`t.Contains(ivl)` over bytes-affine keys**: `containsRes` (`Contains.lean`: `Visit` over the
query in tree order, the greedy scan) for a query whose begin is the top `""` or below its end
(`Visit`'s premise, `intervalTree.Visit.spec`); some boolean otherwise. An axiom pending the
tree's comparator generalization (and `Contains`' own proof for string-affine keys: `Visit`'s
spec is for visitors that never stop, `Contains`' stops at a gap). -/
axiom intervalTree.wp_Contains_bytes (t : Loc) (L : List Entry) (b e : GoSlice) (bs es : GoString)
    (db de dq : DFrac) :
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt ∗ ownIvtB t L dq ∗
      b ↦*{db} bs ∗ e ↦*{de} es }}
    (App (Val (t @!! go.GoType.PointerType intervalTree.ty @!! go!"Contains"))
      (Val #(bytesIvl b e)))
  {{ (r : Bool), RET #r; ownIvtB t L dq ∗ b ↦*{db} bs ∗ e ↦*{de} es ∗
      ⌜(bs = go!"" ∨ affLt bs es) → r = containsRes (bs, es) L⌝ }}

end reprs

end adt
end EtcdGrove
end Perennial
