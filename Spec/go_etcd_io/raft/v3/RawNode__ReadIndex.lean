/- Lean-first (no Rocq counterpart).

## `RawNode.ReadIndex` (rawnode.go:560), a linearizable read's request (2026-10-13)

`ReadIndex(rctx)` is `rn.raft.Step(pb.Message{Type: MsgReadIndex, Entries:
[]pb.Entry{{Data: rctx}}})` (`readIndexMsg`), its error dropped: at a leader the request is
queued until an entry of its term is committed, then confirmed by a quorum's heartbeat
acknowledgements (`ReadOnlySafe`), or answered at once when the leader is the only voter
(stage F); at a follower it is forwarded to the leader (and the answer comes back as a
`MsgReadIndexResp`); with no leader known it is dropped. Once confirmed, a `Ready` hands out
`ReadState{Index: i, RequestCtx: rctx}` (`readStateOk`).

**A persistent atomic update (2026-10-14, stage R; `notes/raft-readindex-spec.md`).** The
client passes a persistent atomic update `readAu γ Qr` = `□ AU <{ ∃∃ L, rLog γ L }> @ ⊤ ∖
↑raftN, ∅ <{ rLog γ L, COMM □ Qr L }>` over raft's full committed log (`rLog`), with the
context's fresh token (`rdFresh`) and a committed log it knows (`L0`, `[]` if none). The call
deposits it (`read_deposit`): it is fired at once, at the global committed log `Lc` of that
moment -- a log extending `L0` --, and then at every commit after it. The client gets the
request's record `readReq γ c Lc` (`Lc` exact) and its handle `isRead γ c Qr`. A `ReadState`
with context `c` and index `i` carries `readOk γ c i` (`|Lc| ≤ i`); with the handle it is the
witness `readWit γ c Qr i`, which gives `▷ ▷ □ Qr L` for every committed `L` at least `i` long
(`read_collect`): each such log was the global one at some commit after the deposit. The
client also supplies the read context's slice `rctx` recorded as a proposed slice holding `c`
(`isPropData`; through a node: `node_read_register`) and one read credit (`rdCred`: the
credits bound the requests a leader may count, so that its request positions do not wrap).

Any number of voters (the single-voter premise went with stage F's fix). The `RawNode`'s
client-facing state is unchanged: a `MsgReadIndex` moves no term and no log (`raft.Step`'s
`NetFrame`, `TermStep`).

raft v3.7 (2026-10-16, stage R5): the request is `&pb.Message{Type: MsgReadIndex.Enum(), Entries:
[]*pb.Entry{{Data: rctx}}}`, stepped with `raft.Step` (`msgIn ml □`). D6: a read context is its
bytes (`readStateOk` over `ReadStateM`, etcd matches read states by `bytes.Equal`), so the client
supplies `rctx ↦*□ c` (the entry holds the slice read-only) instead of the proposed slice.

Lean notes: as `RawNode.Propose.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnode

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

/-- The scalars of the message `ReadIndex` builds: `pb.Message{Type: MsgReadIndex, ...}`
(2026-10-16, stage R5: a record; its one entry is `propEntryM c`, the context's bytes; until
then the Goose value `readIndexMsg esl` with the entries' slice). -/
def readIndexMsgM [FfiSyntax] : MessageM := { (zero_val MessageM) with Type' := MsgReadIndex }

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
    (Qr : List EntryM → IProp GF) (L0 : List EntryM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      -- (2026-10-16, stage R5, D6) the context's bytes, read-only (until then a proposed slice,
      -- `isPropData γ rctx c`): the request's entry holds them
      "#Hctx" ∷ rctx ↦*□ c ∗
      "Hfr" ∷ rdFresh γ c ∗
      "#Hau" ∷ readAu γ Qr ∗
      "#HL0" ∷ isCommitted γ L0 ∗
      "Hcred" ∷ rdCred γ 1 }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReadIndex")) (Val #rctx))
  {{ RET #(); "Hrn" ∷ ownRawNode γ rn id rs ∗
      ∃ Lc, "%HL0c" ∷ ⌜L0 <+: Lc⌝ ∗ "#Hrq" ∷ readReq γ c Lc ∗ "#Hrd" ∷ isRead γ c Qr }}

end spec

end EtcdGrove
end Perennial
