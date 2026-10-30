module
public import Spec.go_etcd_io.bbolt.node__splitTwo
public import Proof.go_etcd_io.bbolt.FloatConv

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section defs
variable [FfiSyntax] [GoLocalContext] [GoGlobalContext] [GoSemanticsFunctions]
variable [go.FloatConvSemantics]

/-- The fill percent `n.splitTwo` uses: the bucket's `FillPercent` (`fp`) clamped to
`[minFillPercent, maxFillPercent]` (0.1 and 1.0, as bit patterns; the comparisons are the
model's `float64Leb`). -/
def clampFP (fp : w64) : w64 :=
  if (float64Leb fp (W64 4591870180066957722) && !decide (fp = W64 4591870180066957722)) = true
  then W64 4591870180066957722
  else if (float64Leb (W64 4607182418800017408) fp && !decide (fp = W64 4607182418800017408)) = true
  then W64 4607182418800017408
  else fp

/-- The threshold `n.splitTwo` splits at: `int(float64(pageSize) * fillPercent)`. -/
def splitThr (ps fp : w64) : w64 :=
  go.float64ToInt64 (float64Mul (go.float64OfUint64 ps) (clampFP fp))

end defs

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [float_sem : go.FloatConvSemantics]

/-- `n.splitTwo(pageSize)` (`node.splitTwo.spec`), with why: it does not split a node of at most
four inodes or whose page is smaller than `pageSize` (`sizeLessThan`), and splits the others at
`splitIndex`'s index for the threshold `splitThr`. -/
abbrev node.splitTwo.xspec : Prop :=
  ∀ (nl : Loc) (nv : node) (ins : List internal.common.Inode) (bv : Bucket) (dqb : DFrac)
    (st : TxStats) (pv : node) (pcs : List Loc) (ps : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ nl ↦ nv ∗ nv.inodes' ↦* ins ∗
      ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗ nv.bucket' ↦{dqb} bv ∗
      structFieldRef Tx go!"stats" bv.tx' ↦ st ∗ parentOwn nv.parent' pv pcs }}
    (App (Val (nl @!! go.GoType.PointerType node.ty @!! go!"splitTwo")) (Val #ps))
  {{ (nx : Loc), RET (PairV #nl #nx); nv.bucket' ↦{dqb} bv ∗
      ((⌜nx = null ∧ (ins.length ≤ 4 ∨ sizeLessThanFrom (W64 16) ps (W64 16) ins = true)⌝ ∗
          nl ↦ nv ∗ nv.inodes' ↦* ins ∗
          ownSliceCap internal.common.Inode nv.inodes' (DFrac.own 1) ∗
          structFieldRef Tx go!"stats" bv.tx' ↦ st ∗ parentOwn nv.parent' pv pcs) ∨
        (∃ (k : Nat) (pl : Loc) (pv' : node) (pcs' : List Loc),
          ⌜2 ≤ k ∧ k + 3 ≤ ins.length ∧ nx ≠ null ∧ pl ≠ null ∧
            splitParent nl nx nv pv pcs pl pv' pcs' ∧
            (splitIndexOf (splitThr ps bv.FillPercent') ins).1 = W64 (k : Int)⌝ ∗
          nl ↦ splitLeft nv pl k ∗ inodesL nv k ↦* ins.take k ∗
          nx ↦ splitRight nv pl k ∗ inodesR nv k ↦* ins.drop k ∗
          ownSliceCap internal.common.Inode (inodesR nv k) (DFrac.own 1) ∗
          pl ↦ pv' ∗ pv'.children' ↦* pcs' ∗ ownSliceCap Loc pv'.children' (DFrac.own 1) ∗
          structFieldRef Tx go!"stats" bv.tx' ↦ ({ st with Split' := st.Split' + W64 1 } : TxStats))) }}

end spec

end bbolt
end EtcdGrove
end Perennial
