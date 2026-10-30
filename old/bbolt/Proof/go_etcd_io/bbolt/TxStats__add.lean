module
public import Spec.go_etcd_io.bbolt.TxStats__add
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
public import Spec.go_etcd_io.bbolt.TxStats__IncPageCount
public import Spec.go_etcd_io.bbolt.TxStats__IncPageAlloc
public import Spec.go_etcd_io.bbolt.TxStats__IncCursorCount
public import Spec.go_etcd_io.bbolt.TxStats__IncNodeCount
public import Spec.go_etcd_io.bbolt.TxStats__IncNodeDeref
public import Spec.go_etcd_io.bbolt.TxStats__IncRebalance
public import Spec.go_etcd_io.bbolt.TxStats__IncRebalanceTime
public import Spec.go_etcd_io.bbolt.TxStats__IncSplit
public import Spec.go_etcd_io.bbolt.TxStats__IncSpill
public import Spec.go_etcd_io.bbolt.TxStats__IncSpillTime
public import Spec.go_etcd_io.bbolt.TxStats__IncWrite
public import Spec.go_etcd_io.bbolt.TxStats__IncWriteTime

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
theorem TxStats.add.wp_proof
    (hGPageCount : TxStats.GetPageCount.spec (GF := GF) (hG := hG))
    (hIPageCount : TxStats.IncPageCount.spec (GF := GF) (hG := hG))
    (hGPageAlloc : TxStats.GetPageAlloc.spec (GF := GF) (hG := hG))
    (hIPageAlloc : TxStats.IncPageAlloc.spec (GF := GF) (hG := hG))
    (hGCursorCount : TxStats.GetCursorCount.spec (GF := GF) (hG := hG))
    (hICursorCount : TxStats.IncCursorCount.spec (GF := GF) (hG := hG))
    (hGNodeCount : TxStats.GetNodeCount.spec (GF := GF) (hG := hG))
    (hINodeCount : TxStats.IncNodeCount.spec (GF := GF) (hG := hG))
    (hGNodeDeref : TxStats.GetNodeDeref.spec (GF := GF) (hG := hG))
    (hINodeDeref : TxStats.IncNodeDeref.spec (GF := GF) (hG := hG))
    (hGRebalance : TxStats.GetRebalance.spec (GF := GF) (hG := hG))
    (hIRebalance : TxStats.IncRebalance.spec (GF := GF) (hG := hG))
    (hGRebalanceTime : TxStats.GetRebalanceTime.spec (GF := GF) (hG := hG))
    (hIRebalanceTime : TxStats.IncRebalanceTime.spec (GF := GF) (hG := hG))
    (hGSplit : TxStats.GetSplit.spec (GF := GF) (hG := hG))
    (hISplit : TxStats.IncSplit.spec (GF := GF) (hG := hG))
    (hGSpill : TxStats.GetSpill.spec (GF := GF) (hG := hG))
    (hISpill : TxStats.IncSpill.spec (GF := GF) (hG := hG))
    (hGSpillTime : TxStats.GetSpillTime.spec (GF := GF) (hG := hG))
    (hISpillTime : TxStats.IncSpillTime.spec (GF := GF) (hG := hG))
    (hGWrite : TxStats.GetWrite.spec (GF := GF) (hG := hG))
    (hIWrite : TxStats.IncWrite.spec (GF := GF) (hG := hG))
    (hGWriteTime : TxStats.GetWriteTime.spec (GF := GF) (hG := hG))
    (hIWriteTime : TxStats.IncWriteTime.spec (GF := GF) (hG := hG)) :
    TxStats.add.spec (GF := GF) (hG := hG) := by
  intro l o v w dq
  wp_start as ⟨Hl, Ho⟩
  try wp_auto
  wp_apply hGPageCount $$ [$Ho] as Ho
  wp_apply hIPageCount $$ [$Hl] as %v1 ⟨%Hv1, Hl⟩
  try wp_auto
  wp_apply hGPageAlloc $$ [$Ho] as Ho
  wp_apply hIPageAlloc $$ [$Hl] as %v2 ⟨%Hv2, Hl⟩
  try wp_auto
  wp_apply hGCursorCount $$ [$Ho] as Ho
  wp_apply hICursorCount $$ [$Hl] as %v3 ⟨%Hv3, Hl⟩
  try wp_auto
  wp_apply hGNodeCount $$ [$Ho] as Ho
  wp_apply hINodeCount $$ [$Hl] as %v4 ⟨%Hv4, Hl⟩
  try wp_auto
  wp_apply hGNodeDeref $$ [$Ho] as Ho
  wp_apply hINodeDeref $$ [$Hl] as %v5 ⟨%Hv5, Hl⟩
  try wp_auto
  wp_apply hGRebalance $$ [$Ho] as Ho
  wp_apply hIRebalance $$ [$Hl] as %v6 ⟨%Hv6, Hl⟩
  try wp_auto
  wp_apply hGRebalanceTime $$ [$Ho] as Ho
  wp_apply hIRebalanceTime $$ [$Hl] as %v7 ⟨%Hv7, Hl⟩
  try wp_auto
  wp_apply hGSplit $$ [$Ho] as Ho
  wp_apply hISplit $$ [$Hl] as %v8 ⟨%Hv8, Hl⟩
  try wp_auto
  wp_apply hGSpill $$ [$Ho] as Ho
  wp_apply hISpill $$ [$Hl] as %v9 ⟨%Hv9, Hl⟩
  try wp_auto
  wp_apply hGSpillTime $$ [$Ho] as Ho
  wp_apply hISpillTime $$ [$Hl] as %v10 ⟨%Hv10, Hl⟩
  try wp_auto
  wp_apply hGWrite $$ [$Ho] as Ho
  wp_apply hIWrite $$ [$Hl] as %v11 ⟨%Hv11, Hl⟩
  try wp_auto
  wp_apply hGWriteTime $$ [$Ho] as Ho
  wp_apply hIWriteTime $$ [$Hl] as %v12 ⟨%Hv12, Hl⟩
  try wp_auto
  iapply HΦ
  iframe
  ipureintro
  simp only [Hv12, Hv11, Hv10, Hv9, Hv8, Hv7, Hv6, Hv5, Hv4, Hv3, Hv2, Hv1, TxStats.addAll]

end proof

end bbolt
end EtcdGrove
end Perennial
