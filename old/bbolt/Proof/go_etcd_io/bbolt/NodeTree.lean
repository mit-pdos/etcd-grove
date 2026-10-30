/-
A node and the subtree of its in-memory children (`node.children`), for `dereference`, which
walks it: `nodeTree P d l` owns the node at `l`, its children slice and, `d` levels down, its
children's subtrees, each node with what `P` says of it.

What `dereference` needs of a node (`derefPre`): its inodes (`inodesOwn`, every key non-empty),
and its key unless it is nil (non-empty unless the node has no page). What it leaves
(`derefPost`): the inodes now point to heap copies, held whole (`freshEntry`), and the old keys
and values (`inodesOwn ins0 es`, the old entries' fractions) and the old key are handed back.
-/
module

public import Proof.go_etcd_io.bbolt.NodeModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

/-- An entry held whole (a heap copy). -/
def freshEntry (e : NodeEntry) : NodeEntry := { e with kq := DFrac.own 1, vq := DFrac.own 1 }

theorem prefix_drop_get {α : Type} (pre l : List α) (j : Nat) (x : α) (hp : pre.length = j)
    (h : l[j]? = some x) : (pre ++ l.drop j)[j]? = some x := by
  rw [List.getElem?_append_right (by omega), hp, Nat.sub_self, drop_cons_of_get _ _ _ h]; rfl

theorem prefix_drop_set {α : Type} (pre l : List α) (j : Nat) (x y : α) (hp : pre.length = j)
    (h : l[j]? = some x) : (pre ++ l.drop j).set j y = (pre ++ [y]) ++ l.drop (j + 1) := by
  rw [List.set_append_right _ _ (by omega), hp, Nat.sub_self, drop_cons_of_get _ _ _ h]
  simp

theorem take_map_succ {α β : Type} (f : α → β) (l : List α) (j : Nat) (x : α) (h : l[j]? = some x) :
    (l.take (j + 1)).map f = (l.take j).map f ++ [f x] := by
  rw [take_succ_of_get _ _ _ h, List.map_append]; rfl

theorem copy_fresh {α : Type} (l : List α) (z : α) (n : Nat) (h : l.length = n) :
    l.take (List.replicate n z).length ++ (List.replicate n z).drop l.length = l := by
  rw [List.length_replicate, ← h, List.take_length, List.drop_replicate, Nat.sub_self,
    List.replicate_zero, List.append_nil]

section tree
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The node at `l` and its children's subtrees, `d` levels deep. -/
def nodeTree (P : node → IProp GF) : Nat → Loc → IProp GF
  | 0, _ => iprop(False)
  | d + 1, l => iprop(∃ (nv : node) (cs : List Loc), l ↦ nv ∗ nv.children' ↦* cs ∗ P nv ∗
      [∗list] c ∈ cs, nodeTree P d c)

theorem nodeTree_zero (P : node → IProp GF) (l : Loc) : nodeTree P 0 l ⊣⊢ False := .rfl

theorem nodeTree_succ (P : node → IProp GF) (d : Nat) (l : Loc) :
    nodeTree P (d + 1) l ⊣⊢ ∃ (nv : node) (cs : List Loc), l ↦ nv ∗ nv.children' ↦* cs ∗ P nv ∗
      [∗list] c ∈ cs, nodeTree P d c := .rfl

/-- The inodes of a node half dereferenced: the first `j` are heap copies (`pre`), the rest
the old ones. -/
theorem inodesOwn_step (pre ins : List internal.common.Inode) (es : List NodeEntry) (j : Nat)
    (it : internal.common.Inode) (e : NodeEntry) (hp : pre.length = j)
    (h1 : ins[j]? = some it) (h2 : es[j]? = some e) :
    inodesOwn (GF := GF) (pre ++ ins.drop j) ((es.take j).map freshEntry ++ es.drop j) ⊢
      inodeIs it e ∗
      (∀ it', inodeIs it' (freshEntry e) -∗
        inodesOwn ((pre ++ [it']) ++ ins.drop (j + 1)) ((es.take (j + 1)).map freshEntry ++ es.drop (j + 1))) := by
  have hj2 := (List.getElem?_eq_some_iff.1 h2).1
  have hl : pre.length = ((es.take j).map freshEntry).length := by simp; omega
  iintro H
  icases (inodesOwn_app _ _ _ _ hl).1 $$ H with ⟨Ha, Hb⟩
  rw [drop_cons_of_get _ _ _ h1, drop_cons_of_get _ _ _ h2]
  icases (inodesOwn_cons _ _ _ _).1 $$ Hb with ⟨Hi, Hb⟩
  iframe Hi
  iintro %it' Hi'
  rw [take_map_succ _ _ _ _ h2]
  iapply (inodesOwn_app _ _ _ _ (by simp only [List.length_append, List.length_singleton]; omega)).2
  iframe Hb
  iapply (inodesOwn_app _ _ _ _ hl).2
  iframe Ha
  iapply (inodesOwn_cons _ _ _ _).2
  iframe Hi'
  iapply inodesOwn_nil

/-- The old inodes handed back, one more. -/
theorem inodesOwn_snoc_take (ins : List internal.common.Inode) (es : List NodeEntry) (j : Nat)
    (it : internal.common.Inode) (e : NodeEntry) (h1 : ins[j]? = some it) (h2 : es[j]? = some e)
    (hl : ins.length = es.length) :
    inodesOwn (GF := GF) (ins.take j) (es.take j) ∗ inodeIs it e ⊢
      inodesOwn (ins.take (j + 1)) (es.take (j + 1)) := by
  have hj1 := (List.getElem?_eq_some_iff.1 h1).1
  rw [take_succ_of_get _ _ _ h1, take_succ_of_get _ _ _ h2]
  iintro ⟨H, Hi⟩
  iapply (inodesOwn_app _ _ _ _ (by simp only [List.length_take]; omega)).2
  iframe H
  iapply (inodesOwn_cons _ _ _ _).2
  iframe Hi
  iapply inodesOwn_nil

/-- What `dereference` needs of a node of the bucket `bl`. -/
abbrev derefPre (bl : Loc) (nv : node) : IProp GF :=
  iprop(⌜nv.bucket' = bl⌝ ∗
    (∃ (ins : List internal.common.Inode) (es : List NodeEntry), nv.inodes' ↦* ins ∗ inodesOwn ins es ∗
      ⌜∀ i < es.length, 0 < (entryKey es i).length⌝) ∗
    (⌜nv.key' = slice.nil⌝ ∨
      ∃ (kb : List w8) (dk : DFrac), nv.key' ↦*{dk} kb ∗ ⌜nv.pgid' = W64 0 ∨ 0 < kb.length⌝))

/-- What `dereference` leaves of a node of the bucket `bl`. -/
abbrev derefPost (bl : Loc) (nv : node) : IProp GF :=
  iprop(⌜nv.bucket' = bl⌝ ∗
    (∃ (ins ins0 : List internal.common.Inode) (es : List NodeEntry), nv.inodes' ↦* ins ∗
      inodesOwn ins (es.map freshEntry) ∗ inodesOwn ins0 es) ∗
    (⌜nv.key' = slice.nil⌝ ∨
      ∃ (kb : List w8) (kold : GoSlice) (dk : DFrac), nv.key' ↦* kb ∗ kold ↦*{dk} kb))

end tree

end bbolt
end EtcdGrove
end Perennial
