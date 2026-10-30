module
public import Spec.go_etcd_io.bbolt.node__splitTwo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [ext : FfiSyntax]

/-- The parts `xs` (location, struct, inodes) `n.split` makes of the node `nl` (struct `nv`,
inodes `ins`), under the parent `pl`: the node itself first (its parent `pl`, a prefix of its
inodes), then new nodes of its bucket and kind under `pl`; their inodes, in order, are the
node's, each part's at least two if there are several. -/
def splitPieces (nl : Loc) (nv : node) (pl : Loc) (ins : List internal.common.Inode)
    (xs : List (Loc × node × List internal.common.Inode)) : Prop :=
  (xs.map (fun x => x.2.2)).flatten = ins ∧
  (∃ x0 rest, xs = x0 :: rest ∧ x0.1 = nl ∧
    x0.2.1 = { nv with parent' := pl, inodes' := x0.2.1.inodes' } ∧
    ∀ x ∈ rest, x.1 ≠ null ∧ x.2.1 =
      ({ zero_val node with bucket' := nv.bucket', isLeaf' := nv.isLeaf', parent' := pl, inodes' := x.2.1.inodes' } : node)) ∧
  (2 ≤ xs.length → ∀ x ∈ xs, 2 ≤ x.2.2.length)

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `n.split(pageSize)`: the parts `xs` (`splitPieces`; `node.splitTwo` until it does not
split), returned as a slice. Unsplit, the node is as it was (its parent too). Split, its parent
`pl` is its old one, the new parts appended to its children, or a new one whose children are
the parts; the last part keeps the inodes' capacity, the others have none. -/
abbrev node.split.spec : Prop :=
  ∀ (nl : Loc) (nv : node) (ins : List internal.common.Inode) (bv : Bucket) (dqb : DFrac)
    (st : TxStats) (pv : node) (pcs : List Loc) (ps : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
      ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗ nv.bucket' ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ st ∗ parentOwn nv.parent' pv pcs }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"split")) (Val #ps))
  {{ (s : GoSlice) (xs : List (Loc × node × List internal.common.Inode)), RET #s;
      nv.bucket' ↦{dqb} bv ∗ s ↦* xs.map (fun x => x.1) ∗
      ((⌜xs = [(nl, nv, ins)]⌝ ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
          ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗
          structFieldRef Tx go!"stats" bv.tx' ↦ st ∗ parentOwn nv.parent' pv pcs) ∨
        (∃ (pl : Loc) (pv' : node) (pcs' : List Loc) (xl : Loc × node × List internal.common.Inode),
          ⌜2 ≤ xs.length ∧ splitPieces nl nv pl ins xs ∧ xs.getLast? = some xl ∧ pl ≠ null ∧
            ((nv.parent' = null ∧ pv' = newParent nv pv'.children' ∧ pcs' = xs.map (fun x => x.1)) ∨
             (nv.parent' ≠ null ∧ pl = nv.parent' ∧ pv' = { pv with children' := pv'.children' } ∧
              pcs' = pcs ++ (xs.drop 1).map (fun x => x.1)))⌝ ∗
          ([∗list] x ∈ xs, x.1 ↦ x.2.1 ∗ x.2.1.inodes' ↦* x.2.2) ∗
          ownSliceCap internal.common.Inode xl.2.1.inodes' (DFrac.own 1) ∗
          pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1) ∗
          structFieldRef Tx go!"stats" bv.tx' ↦
            ({ st with Split' := st.Split' + W64 ((xs.length - 1 : Nat) : Int) } : TxStats))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
