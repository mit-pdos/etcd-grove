/-
`elemRef.isLeaf` of a writer cursor's reference (U6aa, `notes/bbolt-proof-plan.md`, "Writer reads at
a fraction"; for `Cursor.last_w`): a node reference's is its live node's `isLeaf`, a page
reference's its page header's flags (the bytes through a source).
-/
module

public import Spec.go_etcd_io.bbolt.internal.common.Page__IsLeafPage
public import Proof.go_etcd_io.bbolt.Read.WFirstCount

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

namespace WLast

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A page reference's `isLeaf`**: its page header's flags. -/
theorem wp_isLeaf_page
    (hIL : internal.common.Page.IsLeafPage.spec (GF := GF) (hG := hG))
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (ptr : Loc) (e : elemRef)
    (src : Src) (pg : List w8) (hnn : e.node' = null)
    (h16 : 16 ≤ pg.length) :
  {{ wtxWQ (GF := GF) K tx r m q X ∗ ptr ↦ e ∗ srcLoc X.v e.page' src pg }}
    (App (Val (ptr @!! go.GoType.PointerType elemRef.ty @!! go!"isLeaf")) (Val #()))
  {{ RET #(decide (pageFlags pg = leafPageFlag)); wtxWQ K tx r m q X ∗ ptr ↦ e }} := by
  wp_start as ⟨Hw, He, #Hsrc⟩
  icases wtxWQ_pkgInit K tx r m q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxWQ_cells_acc K tx r m q X $$ Hw with ⟨%Hbase, Hcells, Hwb⟩
  icases Write.srcLoc_acc (QpMul q wq) X.v e.page' src pg $$ [Hcells] with ⟨%dq, Hp, Hpb⟩
  · iframe; iframe #
  icases Read.bytesPointsto_bounds e.page' dq pg (by intro h; simp [h] at h16) $$ Hp
    with ⟨Hp, %Hlb⟩
  icases bytesPointsto_view_read (V := Page) e.page' dq pg 0 e.page' (by simp) (by omega) Hlb.1
    $$ Hp with ⟨Hh, Hhb⟩
  rw [show (decode (List.take 16 (List.drop 0 pg)) : Page) = pageHdr pg from rfl]
  obtain ⟨hd, hH⟩ : ∃ hd, pageHdr pg = hd := ⟨_, rfl⟩
  have hfz : decide (hd.flags' = W16 2) = decide (pageFlags pg = leafPageFlag) := by
    unfold pageFlags; rw [hH]
    apply decide_eq_decide.2
    constructor
    · intro h; rw [h]; rfl
    · intro h; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
  rw [hH]
  wp_auto
  rw [hnn]
  wp_auto
  wp_apply hIL e.page' hd dq $$ [Hh] as Hh
  · iexact Hh
  try wp_auto
  ihave Hp := Hhb $$ Hh
  ihave Hcells := Hpb $$ Hp
  ihave Hw := Hwb $$ Hcells
  rw [hfz]
  iapply HΦ
  iframe

/-- **A node reference's `isLeaf`**: its live node's. -/
theorem wp_isLeaf_node
    (K : BC) (tx : Loc) (r : TxReg) (m : Bool) (q : Qp) (X : WX) (bl : Loc) (B : BRec)
    (ptr : Loc) (e : elemRef) (rn : NRec) (hB : X.t.bs !! bl = some B) (hnn : e.node' ≠ null)
    (hrn : B.ns !! e.node' = some rn) (hlv : e.node' ∈ X.live) :
  {{ wtxWQ (GF := GF) K tx r m q X ∗ ptr ↦ e }}
    (App (Val (ptr @!! go.GoType.PointerType elemRef.ty @!! go!"isLeaf")) (Val #()))
  {{ RET #(rn.nv.isLeaf'); wtxWQ K tx r m q X ∗ ptr ↦ e }} := by
  wp_start as ⟨Hw, He⟩
  obtain ⟨l, hm⟩ : ∃ l, e.node' = l := ⟨_, rfl⟩
  rw [hm] at hrn hnn hlv
  icases wtxWQ_node_cells_acc K tx r m q X bl B l rn hB hrn hlv $$ Hw with ⟨%Hbase, Ho, Hcells, Hwb⟩
  isimp only [objOwn] at Ho
  icases Ho with ⟨Hn, Hins, Hcapn, Hws, Hch, Hchcap, Hnk⟩
  icases typedPointsto_not_null_dup _ _ _ $$ Hn with ⟨Hn, %Hnn⟩
  iStructNamed Hn
  wp_auto
  rw [hm, decide_eq_false hnn]
  wp_auto
  rw [hm]
  wp_auto
  ihave Hn : (l ↦{DFrac.own q} rn.nv : IProp GF) $$ [bucket isLeaf unbalanced spilled key pgid parent children inodes]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  ihave Ho : objOwn X.v l (DFrac.own q) true (.node bl rn) $$ [Hn Hins Hcapn Hws Hch Hchcap Hnk]
  · simp only [objOwn]; iframe
  ihave Hw := Hwb $$ Ho Hcells
  iapply HΦ
  iframe

end proof

end WLast

end bbolt
end EtcdGrove
end Perennial
