module
public import Proof.go_etcd_io.bbolt.NodeTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- What a writer's node holds before `dereference`: its struct, children, inodes, their
entries (bytes and fractions) and its key's bytes and fraction. -/
structure DerefIn where
  nv : node
  cs : List Loc
  ins : List internal.common.Inode
  es : List NodeEntry
  kb : List w8
  dk : DFrac

end defs

section preds
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- A tree of nodes from `l`, `d` levels deep, each node's children those `g` records. -/
def nodeTreeW (P : Loc → node → IProp GF) (g : Loc → DerefIn) : Nat → Loc → IProp GF
  | 0, _ => iprop(False)
  | d + 1, l => iprop(∃ (nv : node), l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ P l nv ∗
      [∗list] c ∈ (g l).cs, nodeTreeW P g d c)

theorem nodeTreeW_zero (P : Loc → node → IProp GF) (g : Loc → DerefIn) (l : Loc) :
    nodeTreeW P g 0 l ⊣⊢ False := .rfl

theorem nodeTreeW_succ (P : Loc → node → IProp GF) (g : Loc → DerefIn) (d : Nat) (l : Loc) :
    nodeTreeW P g (d + 1) l ⊣⊢ ∃ (nv : node), l ↦ nv ∗ nv.children' ↦* (g l).cs ∗ P l nv ∗
      [∗list] c ∈ (g l).cs, nodeTreeW P g d c := .rfl

/-- What `dereference` needs of the node `l` of the bucket `bl` (what `g` records of it). -/
def derefPreW (g : Loc → DerefIn) (bl l : Loc) (nv : node) : IProp GF :=
  iprop(⌜nv = (g l).nv ∧ nv.bucket' = bl ∧ ∀ i < (g l).es.length, 0 < (entryKey (g l).es i).length⌝ ∗
    nv.inodes' ↦* (g l).ins ∗ inodesOwn (g l).ins (g l).es ∗
    (⌜nv.key' = slice.nil⌝ ∨
      (nv.key' ↦*{(g l).dk} (g l).kb ∗ ⌜nv.pgid' = W64 0 ∨ 0 < (g l).kb.length⌝)))

/-- What `dereference` leaves of it: the same node but its key, the inodes' bytes heap copies,
and the old bytes (and key) handed back. -/
def derefPostW (g : Loc → DerefIn) (bl l : Loc) (nv' : node) : IProp GF :=
  iprop(⌜nv' = { (g l).nv with key' := nv'.key' }⌝ ∗
    (∃ (ins : List internal.common.Inode), nv'.inodes' ↦* ins ∗
      inodesOwn ins ((g l).es.map freshEntry)) ∗
    inodesOwn (g l).ins (g l).es ∗
    (⌜(g l).nv.key' = slice.nil ∧ nv'.key' = slice.nil⌝ ∨
      (⌜(g l).nv.key' ≠ slice.nil⌝ ∗ (g l).nv.key' ↦*{(g l).dk} (g l).kb ∗ nv'.key' ↦* (g l).kb)))

end preds

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.dereference()` on a subtree of nodes of the bucket `bl` (as `node.dereference.spec`), what
it hands back related to what it was given (`g`): what a writer needs to give back the view's
bytes it lent. -/
abbrev node.dereference.wspec : Prop :=
  ∀ (g : Loc → DerefIn) (d : Nat) (nl bl : Loc) (bv : Bucket) (dqb : DFrac) (st : TxStats),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nodeTreeW (derefPreW g bl) g d nl ∗
      bl ↦{dqb} bv ∗ structFieldRef Tx go!"stats" bv.tx' ↦ st }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"dereference")) (Val #()))
  {{ (k : w64), RET #(); nodeTreeW (derefPostW g bl) g d nl ∗ bl ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ ({ st with NodeDeref' := st.NodeDeref' + k } : TxStats) }}

end spec

end bbolt
end EtcdGrove
end Perennial
