/-
`(*raftNode).persistRaftData(hardState, entries, raftSnap, snapshotPersistedC)` (raft.go;
etcd-io/etcd#22223, `pr-verify/etcd-22223`): the `Ready` loop's persistence step, factored out of
`start` so the asynchronous append worker can share it. Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftNode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `r.persistRaftData(hp, es, nil, c)` with no snapshot (raft's contract, `rnReadyData`: the
legacy path passes `proto.Clone(nil)`, which is nil): the WAL's `Save(hp, es)` (exiting the
process on an error), the `proposalsCommitted` gauge, and `raftStorage.Append(es)`, which turns
the append right into the receipt `Advance` takes. The snapshot channel `c` is not touched. (The
asynchronous path passes `raftpb.EnsureSnapshot(nil)`, a non-nil empty snapshot, and a snapshot
when one arrives: neither is covered.) -/
abbrev raftNode.persistRaftData.spec : Prop :=
  ∀ (E : RNEnv GF) (γ : RNNames) (r hp : Loc) (hs : HardStateModel) (sl : GoSlice)
    (esL : List Loc) (es : List EntryModel) (c : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      isRaftNode E γ r ∗ hardStateAt hp hs ∗ sl ↦*□ esL ∗ entriesAt esL es ∗
      rnAppendRight γ es }}
    (App (App (App (App (Val (r @!! go.GoType.PointerType raftNode.ty @!! go!"persistRaftData"))
      (Val #hp)) (Val #sl)) (Val #(null : Loc))) (Val #c))
  {{ RET #(); rnAppendReceipt γ es }}

end spec

end EtcdGrove
end Perennial
