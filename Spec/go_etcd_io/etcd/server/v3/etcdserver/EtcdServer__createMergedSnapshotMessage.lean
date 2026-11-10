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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.createMergedSnapshotMessage(ml, snapt, snapi, cs)`, by the apply thread (the logger's reader
slot), of an owned raft message `ml` (`m.Snapshot` is written) and a valid `ep.confState` `cs`
(`epCsOk`: nil or read-only for good), given the contracts of `s.KV().Commit()` and of
`s.be.Snapshot()` (`srvKVCommitOk`, `srvBeSnapOk`, with their resources, `Snapshot()`'s from what
`Commit()` gives back, `RC' -∗ RS`: D22 the stored-index window, 2026-10-23; `s.kv` read-only,
`s.be` at some fraction, given back: the apply thread's, `srvBeOwn`, D22 receiver epochs, S7b): the merged message `mg` (`mergedMsg`: `NewMessage` of `ml` and a reader `rc`), the raft
message read-only for good with its snapshot replaced by `(c, snapi, snapt)`, `c` the content of
`cs` (`csOpt`; `proto.Clone`'s copy, so the sender's later changes to `ep.confState` do not reach
it), and the reader streaming a bbolt image of the backend snapshot's data `D`, of which the
caller's observation `Qd` holds (strict M1, 2026-11-06: a resource, `srvBeSnapOk`'s, in place of
a pure fact: the snapshot's image is mvcc's persistent `mvccImage`). The reader goroutine (`newSnapshotReaderCloser`) does not panic.
(2026-11-06, `notes/begin-tok-plan.md`) The caller's `threadTok` pays for `Snapshot()`'s reader
slot (`srvBeSnapOk`), and the reader goroutine's fork token comes back to it. (raft-entsize [r3c],
2026-11-09) `cs` is the voters' conf state (`epCsVoters`, in place of `epCsOk`) of a configuration
of at most `2 ^ 20` members (`srvMemOk`'s bound), so the merged conf state `c` lists at most
`2 ^ 20` ids: what bounds the merged message's size. (raft-entsize [r3c], 2026-11-10) The raft
message has no top-level unknown fields (`pbMsg … []`, `rnSnapMsg`'s) and no entries, `Context` or
responses (a `MsgSnap`'s `SentMsgShape`), so the merged message is frozen at a content below
`2 ^ 47` bytes (`msgSzC False`): what the envelope's encoder needs (`netSnapBundle`). -/
abbrev EtcdServer.createMergedSnapshotMessage.spec : Prop :=
  ∀ (s ml : Loc) (st : MsgSt) (snapt snapi : w64) (cs lg : Loc) (kv be : GoInterface) (dq : DFrac)
    (RC RC' RS RS' : IProp GF) (Qd : backend.Data → IProp GF) (γs : ServerRaftNames),
  GMap.size γs.raft.cfg ≤ 2 ^ 20 → st.ents = [] ∧ st.ctx = [] ∧ st.resps = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvLgAddr s ↦□ lg ∗ ⌜lg ≠ null⌝ ∗ srvLgReader s ∗
      srvKVAddr s ↦□ kv ∗ srvKVCommitOk kv RC RC' ∗ RC ∗
      srvBeAddr s ↦{dq} be ∗ srvBeSnapOk be RS RS' Qd ∗ (RC' -∗ RS) ∗
      msgOwn ml (DFrac.own 1) st ∗ pbMsg go_etcd_io.raft.v3.raftpb.Message ml [] ∗
      epCsVoters γs cs ∗ threadTok }}
    (App (App (App (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!!
      go!"createMergedSnapshotMessage")) (Val #ml)) (Val #snapt)) (Val #snapi)) (Val #cs))
  {{ (mg : Loc), RET #mg; srvLgReader s ∗ RS' ∗ srvBeAddr s ↦{dq} be ∗ threadTok ∗
      ∃ (rc : GoInterface) (D : backend.Data) (c : ConfStateM),
        mergedMsg mg ml rc ∗ msgOwn ml DFrac.discard (mergedSt st c snapi snapt) ∗
        msgSzC False ml (mergedSt st c snapi snapt) ∗
        csOpt cs DFrac.discard c ∗
        ⌜(c.Voters' ++ c.Learners' ++ c.VotersOutgoing' ++ c.LearnersNext').length ≤ 2 ^ 20⌝ ∗
        backend.readerStreams rc (fun bs => backend.boltImage bs D) ∗ Qd D }}

end spec

end EtcdGrove
end Perennial
