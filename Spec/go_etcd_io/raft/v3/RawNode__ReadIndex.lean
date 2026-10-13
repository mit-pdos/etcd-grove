/- Lean-first (no Rocq counterpart).

## `RawNode.ReadIndex` (rawnode.go:560), a linearizable read's request (2026-10-13)

`ReadIndex(rctx)` is `rn.raft.Step(pb.Message{Type: MsgReadIndex, Entries:
[]pb.Entry{{Data: rctx}}})` (`readIndexMsg`), its error dropped: at a leader the request is
queued until an entry of its term is committed, then confirmed by a quorum's heartbeat
acknowledgements (`ReadOnlySafe`); at a follower it is forwarded to the leader (and the
answer comes back as a `MsgReadIndexResp`); with no leader known it is dropped. Once
confirmed, a `Ready` hands out `ReadState{Index: i, RequestCtx: rctx}` (`readStateOk`).

The client supplies the read context: its slice `rctx` recorded as a proposed slice
holding `c` (`isPropData`; through a node: `node_read_register`), the request's record
`readReq γ c Lc` -- created fresh by the holder of the read registry's authority
(`readReq_alloc`) with a committed log `Lc` it knows -- and one read credit (`rdCred`,
`Protocol/GhostState.lean`: the credits bound the requests a leader may count, so that its
request positions do not wrap). From a `ReadState` whose context is `rctx` the client
reads `readOk γ c i` (`readStateOk_readOk`): `|Lc| ≤ i`, so the committed log up to `i`
extends `Lc` (`readStateOk_prefix`).

`IsSingleton`'s immediate answer (a single voter) is out of scope: the configuration has
more than one voter (`raft.Step`'s premise). The `RawNode`'s client-facing state is
unchanged: a `MsgReadIndex` moves no term and no log (`raft.Step`'s `NetFrame`,
`TermStep`).

Lean notes: as `RawNode.Propose.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The message `ReadIndex` builds: `pb.Message{Type: MsgReadIndex, Entries: esl}`. -/
def readIndexMsg [FfiSyntax] (esl : GoSlice) : raftpb.Message :=
  { (zero_val raftpb.Message) with Type' := MsgReadIndex, Entries' := esl }

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- See the file header. -/
abbrev RawNode.ReadIndex.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (rctx : GoSlice) (c : List w8)
    (Lc : List raftpb.Entry),
  1 < GMap.size γ.reCfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      "#Hpd" ∷ isPropData γ rctx c ∗
      "#Hrq" ∷ readReq γ c Lc ∗
      "Hcred" ∷ rdCred γ 1 }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReadIndex")) (Val #rctx))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs }}

end spec

end EtcdGrove
end Perennial
