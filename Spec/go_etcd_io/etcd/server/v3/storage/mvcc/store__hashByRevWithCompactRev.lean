/-
`store.hashByRevWithCompactRev` (`kvstore.go`, etcd-io/etcd#21202; pr-verify/etcd-21202): the hash
of the revisions up to a revision, with a compaction revision (`HashParams.lean`).
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

/-- `s.hashByRevWithCompactRev(rev, compactRev)`: `prepareHashParams`'s outcomes (its spec's
premises: a reader, `rev ≥ 0`, `hashCrevOk`, `storeCmp`; and the histogram `hashRevSec`), the
hash of the success case's `unsafeHashByRev` (any error of it returned): its revision is
`hashRev rev cur` (`rev`, or the last revision `cur` for `0`) and its compaction revision
`hashCrev compactRev cm` (the caller's if positive, else the store's `cm`), its value opaque;
`ErrCompacted` (`0 < rev < hashCrev compactRev cm`, current revision `0`) and `ErrFutureRev`
(`cur < rev`, `cur`) as `prepareHashParams`'s. The read transaction is unlocked before the return
(the deferred `cleanup`). -/
abbrev mvcc.store.hashByRevWithCompactRev.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev compactRev : w64),
  mvcc.storeCmp γ → 0 ≤ sint.Z rev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.hashRevSecOk ∗ mvcc.isStore s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.hashCrevOk γ compactRev }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"hashByRevWithCompactRev"))
      (Val #rev)) (Val #compactRev))
  {{ (h : KeyValueHash) (cur : w64) (err : GoInterface), RET (PairV (PairV #h #cur) #err);
      mvcc.storeReaderC s γ ∗ mvcc.hashCrevOk γ compactRev ∗
      ∃ (log : mvcc.Log) (cm : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx cm ∗
        ⌜log ≠ [] ∧ -1 ≤ cm ∧ cm < log.length⌝ ∗
        (⌜cur = W64 ((log.length : Int) - 1) ∧
            h.CompactRevision' = mvcc.hashCrev compactRev cm ∧ h.Revision' = mvcc.hashRev rev cur ∧
            (0 < sint.Z rev → sint.Z h.CompactRevision' ≤ sint.Z rev ∧ sint.Z rev ≤ sint.Z cur) ∧
            cm ≤ sint.Z h.Revision' ∧ 0 ≤ sint.Z h.Revision' ∧ sint.Z h.Revision' ≤ sint.Z cur⌝ ∨
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
