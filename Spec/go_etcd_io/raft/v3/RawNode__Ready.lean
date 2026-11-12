/-
Port of `election_proof/spec_RawNode__Ready.v` (857d09190), made client-facing on
2026-10-09.

Until 2026-10-09 the spec was stated on the node's states: `ownRawNode cfg rn id s rs`
at the `NState` `s`, with `ownRaftGhost`, `NStateRel` and the `Step.drain` it takes in
the postcondition; the committed entries as `∃ pre, isCommitted γ (pre ++ ce)` with
`pre` as long as `s.logst.applying`, and `ce` a prefix of `logCommittedEnts s.logst`;
the messages' abstractions in the protocol outbox `ps.outbox`; and the values of
`HardState`, `SoftState` and `MustSync` against the previous ones. Those are gone: the
committed entries extend `rs.delivered`, the messages are `isRaftMsg`, and nothing is
said of `HardState`/`SoftState`/`MustSync`, which only a durability argument (phase 2)
would need.

Lean notes: As for `raft.Step.spec`, the section fixes `hlc := HasLC.hasLC` and has
`[AllG GF]` (`ownRawNode` holds ghost state); `zero_val _` is written at its type.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, as in `Spec/raft__Step.lean`
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `rn.Ready()` (`rawnode.go:133`) is `readyWithoutAccept` then `acceptReady`.

Premises: `Advance` ran since the last `Ready` (`acceptReady` `Panicf`s on a non-empty
`stepsOnAdvance`), and the application appended the previous `Ready`'s entries to the
storage (and handed the receipt back, `ownRawNode_appended`).

The `Ready` it returns:
- `CommittedEntries`: `ce`, read-only, the committed entries right after the ones
  handed out so far -- `rs.delivered ++ ce` is a prefix of the global committed log
  (`isCommitted`, `Protocol`): the entries the application applies are the cluster's,
  in order and without gaps (`ce` may be empty, e.g. while applying is paused);
- `Entries`: `es`, read-only, the entries the application must append to the storage
  before the next `Ready` (`RNState.unpersisted`), with the right to do so
  (`appendRight`, 2026-10-10: the storage's hand-out law, `InvStorage.lean`), which an
  implementation's `Append` turns into the receipt `ownRawNode_appended` takes back --
  on the application's goroutine, while the node keeps reading the storage;
- `Messages`: the application's slice, to send; each message is `isRaftMsg` once the batch is
  entered (*enter*, below; at role leader at once: since 2026-11-01, until then outright), and
  (2026-10-13) comes with its read credit (`rdCred`: one for a `MsgReadIndex`, none
  otherwise), which the transport passes to the receiver's `Step`;
- `Snapshot` empty (no snapshot pending);
- `ReadStates`: `sts`, read-only (2026-10-13), each `readStateRaw`: its context a slice
  proposed (`isPropData`), and its index at least the length of the committed log the
  read was created knowing (`readOk`), so applying up to it reads a linearizable state.

The node's new state: `delivered` grows by `ce`, `unpersisted` is `es`, and the local
messages for `Advance` are queued (`steps`), which `Advance` takes whatever they are.
(Until 2026-10-10 the postcondition also returned a flag `advanceable`, whether
`Advance` was proved for the queue: not when it held a self-addressed response, which
no client could rule out.)

raft v3.7 (2026-10-16, stage R5; `notes/decisions.md`, D8): `readyWithoutAccept` then
`acceptReady` (`RawNode.readyWithoutAccept.spec`'s file says what changed): the messages handed
out (`ms : List QMsg`, a response at half -- `acceptReady` read the other half, which stays with
the node's way back and is dropped with the queues: the application gets responses read-only,
`nonissues/raft-ready-messages-read-after-handout.md`), the entries `entsRO`, the read states
`readStatesPts`, `rd.Snapshot` `nil`, and the hard state `hsOpt rd.HardState' h` (new). The
`ReadState`s' contexts are bytes (D6), `readStateRaw` over `ReadStateM`. (D22 S-d3a, 2026-10-21) With
a snapshot pending (until then a premise `rs.psnap = false`): handed out with the storage itself,
the loan `L` recorded (`RawNode.readyWithoutAccept.spec`, `RawNode.acceptReady.spec`).

(2026-11-01, durability stage II (k); the user's decision) **Restated like the node API's
receive** (`readyGot`): `RawNode` has no `run` goroutine, so the batch is cut inside `Ready` itself
(`ownRawNodeReady_handout`), in the node's generation `g` (a share of it, `slotLive`, and its free
queue, `slotFree`); the messages' facts come with *enter* (`Henter`, moving the application's
durable half `ownDurGhost` from `rs.dur` to the batch's state, which also gives back the free queue
and the batch's fragments `durFrags γ id W`, what `Advance` takes) and at role leader at once
(`Hlead`); the read states as before. -/
abbrev RawNode.Ready.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (q : Qp) (g : Nat),
  rs.steps = [] →
  rs.unpersisted = [] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNode γ rn id rs ∗
      -- (2026-11-01, durability stage II (k)) the node's generation `g` of its id's slot: a share
      -- (the node being live), and its free queue, in which the `Ready` cuts its batch
      "Hlive" ∷ slotLive γ id q g ∗ "Hfree" ∷ slotFree γ id g }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Ready")) (Val #()))
  {{ (rd : Ready) (ce es : List EntryM) (ms : List QMsg)
      (sts : List ReadStateM) (h : HardStateM) (steps : List Pending) (L : Option SnapLoan)
      (ss : Option (w64 × StateType)) (W : DurMaps), RET #rd;
      "Hrn" ∷ ownRawNode γ rn id
        { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
                  outlb := 0, unst := false, phs := phsNext rs.phs h, psnap := false,
                  slent := L, dur := readyDurable rs.dur (phsNext rs.phs h) L es,
                  role := roleAfter rs.role ss, bw := W } ∗
      "Hlive" ∷ slotLive γ id q g ∗
      -- (2026-11-01, durability stage II (k)) **enter** (the node API's `readyEnter`): when the
      -- application enters the batch's durable state (`readyDurable`; a durable application: in the
      -- write that makes it durable), with a share of the generation (a stopped node's batch is
      -- dead), the durable half moves to it, and it gets the generation's free queue (for the next
      -- `Ready`), the batch's fragments (`durFrags`, what `Advance` takes: `RawNode.Advance.spec`)
      -- and the messages' `isRaftMsg` (until then given here outright)
      "Henter" ∷ (∀ (E : CoPset) (q' : Qp), ⌜↑(raftN γ) ⊆ E⌝ -∗
        ownDurGhost γ id rs.dur ∗ slotLive γ id q' g ={E}=∗
          ownDurGhost γ id (readyDurable rs.dur (phsNext rs.phs h) L es) ∗ slotLive γ id q' g ∗
          slotFree γ id g ∗ durFrags γ id W ∗ [∗list] q ∈ ms, isRaftMsg γ id q.st) ∗
      -- (2026-11-01, durability stage II (k)) at role leader (after the `Ready`'s soft state) the
      -- messages may be sent first (the node API's `readyLeaderMsgs`)
      "#Hlead" ∷ (⌜roleAfter rs.role ss = StateLeader⌝ -∗ [∗list] q ∈ ms, isRaftMsg γ id q.st) ∗
      -- (2026-11-01, durability stage I fix G2) the soft state the node records
      "#Hss" ∷ softStateIs rd.SoftState' ss ∗
      "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ entsRO rd.Entries' es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms.map QMsg.loc ∗
      "Hmsgs_cap" ∷ ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
      -- (2026-10-16, stage R5, D8) the messages, a response at half
      "Hmsgs_own" ∷ ([∗list] q ∈ ms, msgOwn q.loc (readyDq q.st) q.st) ∗
      -- each message's read credit (2026-10-13)
      "Hmsgs_cred" ∷ ([∗list] q ∈ ms,
        rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
      -- every message is of a term at most the node's at the call (2026-10-10)
      -- (2026-10-17; until then at most `rs.term`) within the term ceiling (a granted pre-vote)
      "%Hmsgs_term" ∷ ⌜∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc⌝ ∗
      -- (D22 S-d3a) the snapshot: none, or the loan's (until then `rd.Snapshot' = null`)
      "Hsnapz" ∷ rdSnapOut γ rs rd ce es L ∗
      "%Hpsn" ∷ ⌜rs.psnap = false → L = none⌝ ∗
      -- the read states (2026-10-13)
      "#Hrs" ∷ readStatesPts rd.ReadStates' sts ∗
      "#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateRaw γ st) ∗
      -- (2026-10-16, stage R5) the hard state, `nil` or fresh and read-only
      "#Hhard" ∷ hsOpt rd.HardState' h ∗
      -- (D22 S-b) a non-`nil` one is the node's: its witness (`hsWit`); (D22l) of `prevHardSt`
      -- after the `Ready` (`phsNext`)
      "#Hhsw" ∷ hsWit γ (phsNext rs.phs h) (dlvAfter rs.delivered ce L).length ∗
      -- the right to append `es` to the node's storage (2026-10-10); (D22 S-d3a) with a snapshot,
      -- the storage itself (`readyOut`); (U8 v2, raft-final phase 1) over the ranges: the log from
      -- the batch on, or after a snapshot from an index at most it with the snapshot handed out
      "Happ" ∷ readyOut rs.storage rs.sn es L ∗
      -- (U8 v2) the committed entries below the batch, frozen, and raft's certified terms of the
      -- committed log handed out (`ownRawNodeReady_handout`)
      "#Hfrz" ∷ (⌜L ≠ none⌝ ∨ ceFrozen rs.storage rs.delivered.length ce es) ∗
      "#Hdk" ∷ dlvKeysAt rs.sn rs.delivered.length
        ((dlvAfter rs.delivered ce L).drop rs.delivered.length) }}

end spec

end EtcdGrove
end Perennial
