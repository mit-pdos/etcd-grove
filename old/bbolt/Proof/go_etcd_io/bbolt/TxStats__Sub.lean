module
public import Spec.go_etcd_io.bbolt.TxStats__Sub
public import Proof.go_etcd_io.bbolt.Records
public import Spec.go_etcd_io.bbolt.TxStats__GetPageCount
public import Spec.go_etcd_io.bbolt.TxStats__GetPageAlloc
public import Spec.go_etcd_io.bbolt.TxStats__GetCursorCount
public import Spec.go_etcd_io.bbolt.TxStats__GetNodeCount
public import Spec.go_etcd_io.bbolt.TxStats__GetNodeDeref
public import Spec.go_etcd_io.bbolt.TxStats__GetRebalance
public import Spec.go_etcd_io.bbolt.TxStats__GetRebalanceTime
public import Spec.go_etcd_io.bbolt.TxStats__GetSplit
public import Spec.go_etcd_io.bbolt.TxStats__GetSpill
public import Spec.go_etcd_io.bbolt.TxStats__GetSpillTime
public import Spec.go_etcd_io.bbolt.TxStats__GetWrite
public import Spec.go_etcd_io.bbolt.TxStats__GetWriteTime

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

set_option maxHeartbeats 400000 in
theorem TxStats.Sub.wp_proof
    (hGPageCount : TxStats.GetPageCount.spec (GF := GF) (hG := hG))
    (hGPageAlloc : TxStats.GetPageAlloc.spec (GF := GF) (hG := hG))
    (hGCursorCount : TxStats.GetCursorCount.spec (GF := GF) (hG := hG))
    (hGNodeCount : TxStats.GetNodeCount.spec (GF := GF) (hG := hG))
    (hGNodeDeref : TxStats.GetNodeDeref.spec (GF := GF) (hG := hG))
    (hGRebalance : TxStats.GetRebalance.spec (GF := GF) (hG := hG))
    (hGRebalanceTime : TxStats.GetRebalanceTime.spec (GF := GF) (hG := hG))
    (hGSplit : TxStats.GetSplit.spec (GF := GF) (hG := hG))
    (hGSpill : TxStats.GetSpill.spec (GF := GF) (hG := hG))
    (hGSpillTime : TxStats.GetSpillTime.spec (GF := GF) (hG := hG))
    (hGWrite : TxStats.GetWrite.spec (GF := GF) (hG := hG))
    (hGWriteTime : TxStats.GetWriteTime.spec (GF := GF) (hG := hG)) :
    TxStats.Sub.spec (GF := GF) (hG := hG) := by
  intro l o v w dq1 dq2
  wp_start as ⟨Hl, Ho⟩
  try wp_auto
  wp_apply hGPageCount $$ [$Hl] as Hl
  wp_apply hGPageCount $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d1, %Hd1, diff⟩
  wp_apply hGPageAlloc $$ [$Hl] as Hl
  wp_apply hGPageAlloc $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d2, %Hd2, diff⟩
  wp_apply hGCursorCount $$ [$Hl] as Hl
  wp_apply hGCursorCount $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d3, %Hd3, diff⟩
  wp_apply hGNodeCount $$ [$Hl] as Hl
  wp_apply hGNodeCount $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d4, %Hd4, diff⟩
  wp_apply hGNodeDeref $$ [$Hl] as Hl
  wp_apply hGNodeDeref $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d5, %Hd5, diff⟩
  wp_apply hGRebalance $$ [$Hl] as Hl
  wp_apply hGRebalance $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d6, %Hd6, diff⟩
  wp_apply hGRebalanceTime $$ [$Hl] as Hl
  wp_apply hGRebalanceTime $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d7, %Hd7, diff⟩
  wp_apply hGSplit $$ [$Hl] as Hl
  wp_apply hGSplit $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d8, %Hd8, diff⟩
  wp_apply hGSpill $$ [$Hl] as Hl
  wp_apply hGSpill $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d9, %Hd9, diff⟩
  wp_apply hGSpillTime $$ [$Hl] as Hl
  wp_apply hGSpillTime $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d10, %Hd10, diff⟩
  wp_apply hGWrite $$ [$Hl] as Hl
  wp_apply hGWrite $$ [$Ho] as Ho
  try wp_auto
  icases typedPointsto_name _ _ _ $$ diff with ⟨%d11, %Hd11, diff⟩
  wp_apply hGWriteTime $$ [$Hl] as Hl
  wp_apply hGWriteTime $$ [$Ho] as Ho
  try wp_auto
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  simp only [Hd11, Hd10, Hd9, Hd8, Hd7, Hd6, Hd5, Hd4, Hd3, Hd2, Hd1, TxStats.subAll]

end proof

end bbolt
end EtcdGrove
end Perennial
