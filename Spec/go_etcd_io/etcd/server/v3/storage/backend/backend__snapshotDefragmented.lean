/-
`snapshotDefragmented` (the backend, `backend.go`; names only, `etcd#21776`).
`b.snapshotDefragmented(defragTxMaxBytes)`: commits the batch transaction (`b.batchTx.Commit()`),
then under `b.mu.RLock()` creates a temporary file in `filepath.Dir(b.db.Path())`, opens a temporary
bbolt database `tmpdb`, compacts `b.db` into `tmpdb` (`bolt.Compact(tmpdb, b.db, defragTxMaxBytes)`),
begins a read transaction on `tmpdb` (`tmpdb.Begin(false)`), starts the warning goroutine
(`newSnapshot(b.lg, tx)`), and returns `&defragmentedSnapshot{snapshot: ..., closer: ...}, nil` (or
`(nil, err)` if creating/opening/compacting/beginning fails).

The trust boundary (`Proof/go_etcd_io/etcd/server/v3/storage/backend/backend__snapshotDefragmented.lean`),
mirroring `backend__Snapshot.lean`. Lean-first (no Rocq counterpart); the vocabulary is
`InvSnapshot.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.InvSnapshot

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.backend backend

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

/-- `b.snapshotDefragmented(defragTxMaxBytes)`: commits `b.batchTx` and either returns a non-nil
error (when temporary file creation, `bolt.Open`, `bolt.Compact`, or `tmpdb.Begin(false)` fails) or
returns a `*defragmentedSnapshot` open over bbolt's committed data `D`, read as the caller's
observation `Q` says of every commit (`bolt.Compact` copies all buckets and key-value pairs of
`b.db`'s read transaction into `tmpdb`, preserving the logical database state `D`). -/
abbrev backend.backend.snapshotDefragmented.spec : Prop :=
  ∀ (γ : BNames) (P : BParams) (W Pk : IProp GF) (b : Loc) (defragTxMaxBytes : w64)
    (qo : Qp) (R : IProp GF)
    (Q : VData → GMap (GoString × GoString) GoString → GMap GoString BktData → Prop),
  0 < sint.Z defragTxMaxBytes →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend ∗
      isBackend γ P W Pk b ∗ bOpen γ qo ∗ wbTok γ ∗ R ∗
      □ (∀ (vd : VData) (d : GMap (GoString × GoString) GoString) (r : GMap GoString BktData),
        R -∗ W -∗ Pk -∗ viewAt γ vd -∗ hkOwn γ d -∗ rbOwn γ r -∗ ⌜Q vd d r⌝) }}
    (App (Val (b @!! go.GoType.PointerType backend.ty @!! go!"snapshotDefragmented"))
      (Val #defragTxMaxBytes))
  {{ (s : GoInterface) (err : GoInterface), RET (PairV #s #err);
      bOpen γ qo ∗ R ∗
      ((⌜err ≠ GoInterface.nil ∧ s = GoInterface.nil⌝) ∨
        (∃ (ds : Loc) (D : Data),
          ⌜err = GoInterface.nil ∧
            s = interface.mkOk (go.GoType.PointerType defragmentedSnapshot.ty) #ds ∧
            Q (sData P D) (hkData P D) (rbData P D)⌝ ∗
          defragSnapOpen ds D)) }}

end spec

end EtcdGrove
end Perennial
