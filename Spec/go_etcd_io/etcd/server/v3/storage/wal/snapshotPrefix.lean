/- The fallback's reverse scan of filenames before the normally selected file. -/
module
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.searchIndex

@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove
open Iris Iris.BI
namespace wal
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go.Semantics] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

/-- A probe of one file before a modern cut. A filesystem error is passed back
to the caller. The caller gets the resources for the next probe in either case. -/
abbrev prefixFileMiss (P : IProp GF) (lg : Loc) (dir name : GoString) (index : w64) : Prop :=
  {{ P }} (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.segmentContainsSnapshot))
    (Val #lg)) (Val #dir)) (Val #name)) (Val #index))
  {{ (err : GoInterface), RET (PairV #false #err); P }}

abbrev snapshotPrefix.spec : Prop :=
  ∀ (P : IProp GF) (lg : Loc) (dir : GoString) (sl : GoSlice) (names : List GoString)
    (dq : DFrac) (first index : w64),
    0 ≤ sint.Z first → sint.nat first ≤ names.length →
    (∀ i < sint.nat first, ∀ name, names[i]? = some name → prefixFileMiss P lg dir name index) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ P ∗ sl ↦*{dq} names }}
      (App (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.snapshotPrefix))
        (Val #lg)) (Val #dir)) (Val #sl)) (Val #first)) (Val #index))
    {{ (err : GoInterface), RET (PairV #(W64 (-1)) #err); P ∗ sl ↦*{dq} names }}

end wal
end Perennial.EtcdGrove
