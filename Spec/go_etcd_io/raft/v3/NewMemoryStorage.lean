/- `NewMemoryStorage` (`storage.go:113`), specified 2026-10-10 (Lean-first: no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.raft.v3.InvMemstorage

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `NewMemoryStorage()`: `&MemoryStorage{ents: make([]pb.Entry, 1)}`, a storage with
nothing stored (the dummy entry at index `0`), no snapshot and nothing pending
(`memStorEmpty`), under fresh ghost names. Its snapshot is empty, which
`isStorage`'s `Snapshot` clause excludes (`MemstorageInstance.lean`). -/
abbrev NewMemoryStorage.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions NewMemoryStorage [])) (Val #()))
  {{ (ms : Loc) (γs : MemStorNames), RET #ms; ownMemoryStorage ms γs memStorEmpty }}

end spec

end EtcdGrove
end Perennial
