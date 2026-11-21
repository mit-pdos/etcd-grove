/- The prefix probe preserves an already open modern WAL handle. -/
module
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__reopenAtRecord
@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove
open Iris Iris.BI Iris.ProofMode
open _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go.Semantics] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

theorem wal.reopenAtRecord.wp_proof
    (wp_Index : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Prefix : wal.snapshotPrefix.spec (GF := GF) (hG := hG)) : wal.reopenAtRecord.spec (GF := GF) (hG := hG) := by
  intro P w fb lg sp dir s v names h0 hlen hprobe
  wp_start as ⟨HP, Hlg, Hdir, Hstart, #Hsp, Hfb, Hnames⟩
  ihave %hn := typedPointsto_not_null fb _ _ $$ Hfb
  iStructNamed Hfb
  (try wp_auto)
  wp_apply wp_Index sp s $$ Hsp
  (try wp_auto)
  wp_apply wp_Prefix P lg dir v.names' names (DFrac.own 1) v.first' s.1 h0 hlen hprobe
    $$ [$HP $Hnames] as %err ⟨HP, Hnames⟩
  cases err <;> wp_auto
  all_goals
    iapply HΦ
    iframe
    iapply typedPointsto_combine _ _ _ hn
    simp only [TypedPointsto.typedPointstoDef]
    iframe

end Perennial.EtcdGrove
