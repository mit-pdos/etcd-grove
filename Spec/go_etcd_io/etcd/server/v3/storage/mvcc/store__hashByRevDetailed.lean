/-
`store.hashByRevDetailed` (`kvstore.go`, etcd-io/etcd#21202; pr-verify/etcd-21202): the hash of
the revisions up to a revision, with a compaction revision, and each pair's (`HashParams.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashParams

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.hashByRevDetailed(rev, compactRev)`: `hashByRevWithCompactRev`'s spec, of the result of
`unsafeHashByRevDetailed`: when its error is `nil`, its total hash's and its own revision and
compaction revision are `hashRev rev cur` and `hashCrev compactRev cm` (on an error, all zero);
the hash values and the per-pair list opaque. That the total hash is `hashByRevWithCompactRev`'s
(the PR's detailed and plain modes agree) is in the crc32 trust boundary, not proved, and false
when a value does not decode (`kvHasherDetailed.WriteKeyValue` then skips the total's write too:
the report's finding 5). -/
abbrev mvcc.store.hashByRevDetailed.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev compactRev : w64),
  mvcc.storeCmp γ → 0 ≤ sint.Z rev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.hashRevSecOk ∗ mvcc.isStore s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.hashCrevOk γ compactRev }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"hashByRevDetailed"))
      (Val #rev)) (Val #compactRev))
  {{ (d : DetailedHashResult) (cur : w64) (err : GoInterface), RET (PairV (PairV #d #cur) #err);
      mvcc.storeReaderC s γ ∗ mvcc.hashCrevOk γ compactRev ∗
      ∃ (log : mvcc.Log) (cm : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx cm ∗
        ⌜log ≠ [] ∧ -1 ≤ cm ∧ cm < log.length⌝ ∗
        (⌜cur = W64 ((log.length : Int) - 1) ∧
            (0 < sint.Z rev → sint.Z (mvcc.hashCrev compactRev cm) ≤ sint.Z rev ∧
              sint.Z rev ≤ sint.Z cur) ∧
            cm ≤ sint.Z (mvcc.hashRev rev cur) ∧ 0 ≤ sint.Z (mvcc.hashRev rev cur) ∧
            sint.Z (mvcc.hashRev rev cur) ≤ sint.Z cur ∧
            (err = GoInterface.nil →
              d.TotalHash'.CompactRevision' = mvcc.hashCrev compactRev cm ∧
              d.TotalHash'.Revision' = mvcc.hashRev rev cur ∧
              d.CompactRevision' = mvcc.hashCrev compactRev cm ∧
              d.Revision' = mvcc.hashRev rev cur)⌝ ∨
        (⌜0 < sint.Z rev ∧ sint.Z rev < sint.Z (mvcc.hashCrev compactRev cm) ∧ cur = W64 0⌝ ∗
          ∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗
            ⌜err = GoInterface.ok ec⌝) ∨
        (⌜0 < sint.Z rev ∧ sint.Z (mvcc.hashCrev compactRev cm) ≤ sint.Z rev ∧
            cur = W64 ((log.length : Int) - 1) ∧ sint.Z cur < sint.Z rev⌝ ∗
          ∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗
            ⌜err = GoInterface.ok ef⌝)) }}

end spec

end EtcdGrove
end Perennial
