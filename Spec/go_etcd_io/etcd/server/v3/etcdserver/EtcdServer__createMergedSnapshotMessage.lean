/-
`s.createMergedSnapshotMessage(m, snapt, snapi, confState)` (`snapshot_merge.go`): the merged
snapshot message. Lean-first (no Rocq counterpart); D22 S-h, 2026-10-20 (`notes/decisions.md`, "D22
S-h carried out"); the vocabulary is `InvSnapSend.lean`. (A `True`-postcondition axiom until D19p,
2026-10-18, which removed it as false.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvSnapSend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.createMergedSnapshotMessage(ml, snapt, snapi, cs)`, by the apply thread (the logger's reader
slot), of an owned raft message `ml` (`m.Snapshot` is written) and a valid `ep.confState` `cs`
(`epCsOk`: nil or read-only for good), given the contracts of `s.KV().Commit()` and of
`s.be.Snapshot()` (`srvKVCommitOk`, `srvBeSnapOk`, with their resources; `s.kv` and `s.be`
read-only): the merged message `mg` (`mergedMsg`: `NewMessage` of `ml` and a reader `rc`), the raft
message read-only for good with its snapshot replaced by `(c, snapi, snapt)`, `c` the content of
`cs` (`csOpt`; `proto.Clone`'s copy, so the sender's later changes to `ep.confState` do not reach
it), and the reader streaming a bbolt image of the backend snapshot's data `D`, of which the
caller's observation `Qd` holds. The reader goroutine (`newSnapshotReaderCloser`) does not panic. -/
abbrev EtcdServer.createMergedSnapshotMessage.spec : Prop :=
  ∀ (s ml : Loc) (st : MsgSt) (snapt snapi : w64) (cs lg : Loc) (kv be : GoInterface)
    (RC RC' RS RS' : IProp GF) (Qd : backend.Data → Prop),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗
      srvBeAddr s ↦□ be ∗ srvBeSnapOk be RS RS' Qd ∗ RS ∗
      msgOwn ml (DFrac.own 1) st ∗ epCsOk cs }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"createMergedSnapshotMessage")) (Val #ml)) (Val #snapt)) (Val #snapi)) (Val #cs))
  {{ (mg : Loc), RET #mg; srvLgReader s ∗ RC' ∗ RS' ∗
      ∃ (rc : GoInterface) (D : backend.Data) (c : ConfStateM),
        mergedMsg mg ml rc ∗ msgOwn ml DFrac.discard (mergedSt st c snapi snapt) ∗
        csOpt cs DFrac.discard c ∗
        backend.readerStreams rc (fun bs => backend.boltImage bs D) ∗ ⌜Qd D⌝ }}

end spec

end EtcdGrove
end Perennial
