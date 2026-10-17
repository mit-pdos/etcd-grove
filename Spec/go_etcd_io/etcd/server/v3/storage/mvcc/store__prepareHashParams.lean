/-
`store.prepareHashParams` (`kvstore.go`, etcd-io/etcd#21202; pr-verify/etcd-21202): the
revision, compaction revision and kept set of a hash (`HashParams.lean`).
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

/-- `s.prepareHashParams(rev, compactRev)` by a reader (`storeReaderC`, given back), for a
revision `rev ≥ 0` and a compaction revision `compactRev` at or above the store's when positive
(`hashCrevOk`, given back: the premise #21202's check needs, finding 1 of the report), on a
backend supporting the compaction (`storeCmp`: its `ReadTx` with no view, `metaReadTx`; the hash
is opaque, so what the transaction reads is not needed). It reads, under `s.mu` and `s.revMu`,
the committed log `log` (its last revision `cur`) and the compaction revision `cm` (at or below
`cur`), and returns the compaction revision `pc = hashCrev compactRev cm` with
* `0 < rev < pc`: `ErrCompacted` (and `0` for the current revision);
* `0 < rev`, `cur < rev`: `ErrFutureRev`, `cur`;
* otherwise `nil`: the revision `prev = hashRev rev cur` (`rev`, or `cur` for `0`), at or above
  the store's compaction revision `cm` and at or below `cur`, `cur`, the map of the revisions
  `Keep(prev)` keeps (`keepOfIs`, owned), a read transaction `ReadTx()`, locked (`metaReadTx`),
  and a function that unlocks it (`hashCleanup`).
With `compactRev ≤ 0` (`HashByRev`, the corruption checks and `HashKV`) these are `hashByRev`'s
results before the PR: `pc = cm`. With `rev = 0` and a positive `compactRev`, nothing bounds `pc`
by `prev` (finding 2: `--compact-rev` above the current revision is accepted, while `--rev` set to
the current revision with the same `--compact-rev` is `ErrCompacted`). -/
abbrev mvcc.store.prepareHashParams.spec : Prop :=
  ∀ (s : Loc) (γ : mvcc.StoreNames) (rev compactRev : w64),
  mvcc.storeCmp γ → 0 ≤ sint.Z rev →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isStore s γ ∗ mvcc.storeReaderC s γ ∗ mvcc.hashCrevOk γ compactRev }}
    (App (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"prepareHashParams")) (Val #rev))
      (Val #compactRev))
  {{ (prev pc : w64) (keep : GoMap) (cur : w64) (tx : GoInterface) (cleanup : GoFunc)
      (err : GoInterface),
      RET (PairV (PairV (PairV (PairV (PairV (PairV #prev #pc) #keep) #cur) #tx) #cleanup) #err);
      mvcc.storeReaderC s γ ∗ mvcc.hashCrevOk γ compactRev ∗
      ∃ (log : mvcc.Log) (cm : Int), mvcc.idxCert γ.idx log ∗ mvcc.crevLb γ.idx cm ∗
        ⌜log ≠ [] ∧ -1 ≤ cm ∧ cm < log.length⌝ ∗
        ((⌜err = GoInterface.nil ∧ cur = W64 ((log.length : Int) - 1) ∧
            pc = mvcc.hashCrev compactRev cm ∧ prev = mvcc.hashRev rev cur ∧
            (0 < sint.Z rev → sint.Z pc ≤ sint.Z rev ∧ sint.Z rev ≤ sint.Z cur) ∧
            cm ≤ sint.Z prev ∧ 0 ≤ sint.Z prev ∧ sint.Z prev ≤ sint.Z cur⌝ ∗
          (∃ A : GMap Revision Unit, ownMap keep (DFrac.own 1) A ∗ ⌜mvcc.keepOfIs A log prev⌝) ∗
          (∃ rt : GoInterfaceOk, ⌜tx = GoInterface.ok rt⌝ ∗ mvcc.metaReadTx rt) ∗
          mvcc.hashCleanup cleanup) ∨
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
