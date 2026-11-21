/- Reading current and legacy configurations from the frozen backend. -/
module
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__createMergedSnapshotMessage
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapshotConfState

@[expose] public section
noncomputable section
namespace Perennial
namespace EtcdGrove
open Iris Iris.BI Iris.ProofMode

variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [go.Semantics]

/-- The two possible disk formats discharge the sender's configuration read. -/
theorem replayConfigRead_of_snapshot
    [srvSem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
    (hUR : backend.snapshot.UnsafeRange.spec (GF := GF) (hG := hG))
    (hID : schema.bucket.ID.spec (GF := GF) (hG := hG))
    (hName : schema.bucket.Name.spec (GF := GF) (hG := hG))
    (hSafe : schema.bucket.IsSafeRangeBucket.spec (GF := GF) (hG := hG))
    (γs : ServerRaftNames) (D : backend.Data)
    (disk : (∃ bytes, backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go!"confState" = some bytes ∧
          snapshotDecodesConfState (GF := GF) bytes (epCsVoters γs)) ∨
      (backend.dget D go_etcd_io.etcd.server.v3.storage.schema.metaName go!"confState" = none ∧
          ∀ lg sp γ, replayMemberRead (GF := GF) γs D lg sp γ)) :
    replayConfigRead (GF := GF) γs D := by
  intro lg sp γ
  iintro %Φ ⟨#Hschema, #Hbe, Hsn⟩ HΦ
  rcases disk with ⟨bytes, hval, hdecode⟩ | ⟨habs, hm⟩
  · wp_apply snapshot_confState_present_open hUR hID hName hSafe lg sp γ D 1 bytes _ hval hdecode
      $$ [$Hschema $Hbe $Hsn] as %p ⟨Hsn, #Hcs⟩
    ihave %hn : ⌜p ≠ null⌝ $$ []
    · iunfold epCsVoters at Hcs
      icases Hcs with ⟨%c, #Hpts, -⟩
      iunfold csPts at Hpts
      iNamed Hpts
      ipureintro; exact Hnn
    iapply HΦ
    simp only [hn, ↓reduceIte]
    iframe Hsn Hcs
  · wp_apply snapshot_confState_absent_open hUR hID hName hSafe lg sp γ D 1 habs
      $$ [$Hschema $Hbe $Hsn] as Hsn
    iapply HΦ
    simp only [↓reduceIte]
    iframe Hsn
    ipureintro; exact hm lg sp γ

end EtcdGrove
end Perennial
