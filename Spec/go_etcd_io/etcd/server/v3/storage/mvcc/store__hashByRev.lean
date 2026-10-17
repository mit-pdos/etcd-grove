/-
`store.hashByRev` (`kvstore.go`; after etcd-io/etcd#21202 `hashByRevWithCompactRev(rev, 0)`;
pr-verify/etcd-21202): the hash of the revisions up to a revision (`HashParams.lean`).
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

/-- `s.hashByRev(rev)` by a reader, `rev ≥ 0`: under `s.mu` and `s.revMu` it reads the committed
log `log` (last revision `cur`) and the store's compaction revision `cm`, and returns
* `0 < rev < cm`: `ErrCompacted`, current revision `0`;
* `cur < rev`: `ErrFutureRev`, `cur`;
* otherwise the hash of `unsafeHashByRev` (any error of it) at revision `rev` (`cur` for `0`) with
  compaction revision `cm`, its value opaque, and `cur`.
The behavior of `hashByRev` before #21202 (its code there is `hashByRevWithCompactRev`'s with
`compactRev = 0`, inlined; not translated on `lean`, so not re-proved of it). -/
abbrev mvcc.store.hashByRev.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev : w64),
  mvcc.storeCmp γ → 0 ≤ sint.Z rev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.hashRevSecOk ∗ mvcc.isStore s γ ∗ mvcc.storeReaderC s γ }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"hashByRev")) (Val #rev))
  {{ (h : KeyValueHash) (cur : w64) (err : GoInterface), RET (PairV (PairV #h #cur) #err);
      mvcc.storeReaderC s γ ∗
      ∃ (log : mvcc.Log) (cm : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx cm ∗
        ⌜log ≠ [] ∧ -1 ≤ cm ∧ cm < log.length⌝ ∗
        (⌜cur = W64 ((log.length : Int) - 1) ∧
            h.CompactRevision' = W64 cm ∧ h.Revision' = mvcc.hashRev rev cur ∧
            cm ≤ sint.Z h.Revision' ∧ 0 ≤ sint.Z h.Revision' ∧ sint.Z h.Revision' ≤ sint.Z cur⌝ ∨
        (⌜0 < sint.Z rev ∧ sint.Z rev < cm ∧ cur = W64 0⌝ ∗
          ∃ ec : GoInterfaceOk, globalAddr ErrCompacted ↦□ GoInterface.ok ec ∗
            ⌜err = GoInterface.ok ec⌝) ∨
        (⌜0 < sint.Z rev ∧ cm ≤ sint.Z rev ∧ cur = W64 ((log.length : Int) - 1) ∧
            sint.Z cur < sint.Z rev⌝ ∗
          ∃ ef : GoInterfaceOk, globalAddr ErrFutureRev ↦□ GoInterface.ok ef ∗
            ⌜err = GoInterface.ok ef⌝)) }}

end spec

end EtcdGrove
end Perennial
