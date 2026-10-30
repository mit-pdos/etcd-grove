module
public import Spec.go_etcd_io.bbolt.node__split
public import Spec.go_etcd_io.bbolt.node__splitTwo_x

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
variable [go.FloatConvSemantics]

/-- Every part `j` of `xs` but the last is what `splitIndex` (threshold `thr`) leaves on the left
of the inodes of the parts `j, j+1, ...`. -/
def splitIdxOK (thr : w64) (xs : List (Loc × node × List internal.common.Inode)) : Prop :=
  ∀ (j : Nat) (x : Loc × node × List internal.common.Inode), j + 1 < xs.length → xs[j]? = some x →
    (splitIndexOf thr ((xs.drop j).map (fun x => x.2.2)).flatten).1 = W64 (x.2.2.length : Int)

/-- The last part of `xs` was not split: at most four inodes, or its page below `ps`. -/
def lastFits (ps : w64) (xs : List (Loc × node × List internal.common.Inode)) : Prop :=
  ∀ x, xs.getLast? = some x →
    x.2.2.length ≤ 4 ∨ sizeLessThanFrom (W64 16) ps (W64 16) x.2.2 = true

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [float_sem : go.FloatConvSemantics]

/-- `n.split(pageSize)` (`node.split.spec`), with why: every part but the last is cut where
`splitIndex` cuts (`splitIdxOK`), the last was not split (`lastFits`). The parts `xs` (`splitPieces`; `node.splitTwo` until it does not
split), returned as a slice. Unsplit, the node is as it was (its parent too). Split, its parent
`pl` is its old one, the new parts appended to its children, or a new one whose children are
the parts; the last part keeps the inodes' capacity, the others have none. -/
abbrev node.split.xspec : Prop :=
  ∀ (nl : Loc) (nv : node) (ins : List internal.common.Inode) (bv : Bucket) (dqb : DFrac)
    (st : TxStats) (pv : node) (pcs : List Loc) (ps : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
      ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗ nv.bucket' ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ st ∗ parentOwn nv.parent' pv pcs }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"split")) (Val #ps))
  {{ (s : GoSlice) (xs : List (Loc × node × List internal.common.Inode)), RET #s;
      ⌜splitIdxOK (splitThr ps bv.FillPercent') xs ∧ lastFits ps xs⌝ ∗ nv.bucket' ↦{dqb} bv ∗ s ↦* xs.map (fun x => x.1) ∗
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
