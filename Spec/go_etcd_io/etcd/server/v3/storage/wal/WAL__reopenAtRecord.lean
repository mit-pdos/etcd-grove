/- Reopening a modern WAL cannot extend its selected segment range. -/
module
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadDefs
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.snapshotPrefix
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
@[expose] public section
noncomputable section
namespace Perennial.EtcdGrove
open Iris Iris.BI
open _root_.Perennial.go_etcd_io.etcd.server.v3.storage.wal
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go.Semantics] [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]

abbrev wal.reopenAtRecord.spec : Prop :=
  ∀ (P : IProp GF) (w fb lg sp : Loc) (dir : GoString) (s : w64 × w64)
    (v : walReadRange) (names : List GoString),
    0 ≤ sint.Z v.first' → sint.nat v.first' ≤ names.length →
    (∀ i < sint.nat v.first', ∀ name, names[i]? = some name → wal.prefixFileMiss P lg dir name s.1) →
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗ "HP" ∷ P ∗
       "Hlg" ∷ structFieldRef WAL go!"lg" w ↦ lg ∗ "Hdir" ∷ structFieldRef WAL go!"dir" w ↦ dir ∗
       "Hstart" ∷ structFieldRef WAL go!"start" w ↦ sp ∗ "#Hsp" ∷ walSnapIdTerm sp s ∗
       "Hfb" ∷ fb ↦ v ∗ "Hnames" ∷ v.names' ↦* names }}
      (App (Val (w @!! go.GoType.PointerType WAL.ty @!! go!"reopenAtRecord")) (Val #fb))
    {{ (err : GoInterface), RET (PairV #false #err);
       P ∗ structFieldRef WAL go!"lg" w ↦ lg ∗ structFieldRef WAL go!"dir" w ↦ dir ∗
       structFieldRef WAL go!"start" w ↦ sp ∗ fb ↦ v ∗ v.names' ↦* names }}

end Perennial.EtcdGrove
