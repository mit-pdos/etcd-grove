/-
`RawNode.readyWithoutAccept` (`rawnode.go:141`), Lean-first (2026-10-10): the first half
of `RawNode.Ready`, which `node.go`'s `run` calls on its own, handing the `Ready` to the
application before `acceptReady`.

Lean notes: as `RawNode.Ready.spec` (`hlc := HasLC.hasLC`, `[AllG GF]`).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRawnodeReady
public import Proof.go_etcd_io.raft.v3.RawNodeAt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `rn.readyWithoutAccept()` builds the `Ready` and changes nothing in the node (Go:
"a read-only operation").

Premises as `RawNode.Ready.spec`'s: `Advance` ran since the last accepted `Ready` and the
application appended its entries (in `node.go`: `advancec == nil`).

What the application gets with `rd` (all of `RawNode.Ready.spec`'s postcondition but the
node and the right to append): the committed entries `ce` extending `rs.delivered`, the
entries `es` to append, the messages to send (their facts with the cut, `ownRawNodeReady_handout`, since 2026-11-01), no snapshot, and (since
2026-10-13) the read states `sts`: `rd.ReadStates` read-only, each `ReadState`
`readStateRaw` -- its context a proposed slice whose read was created knowing a committed
log of length at most its index (`readOk`). The slice is read-only because the node
keeps it until `acceptReady` (which sets `r.readStates` to `nil`). The node is `ownRawNodeReady` (`InvRawnodeReady.lean`): the outbox's slice is now
`rd.Messages`, and `acceptReady rd` takes it to `ownRawNode` at the post-`Ready` state.

Since 2026-10-10 also:
- `Hmsgs_term`: every message handed out is of a term within the node's term ceiling
  (`rs.tc`; until 2026-10-17, with pre-vote off, at most the node's term `rs.term`), which
  `node.go`'s budget covers;
- `Habandon`: the `Ready` may be dropped instead of accepted (`node.go`'s `select` takes
  another case): with the messages given back, the node is whole again, at `rs` with the
  lower bounds raised to what the `Ready` held (`ownRawNodeReady_abandon`).

(#33 S4, 2026-11-24) **At the node's protocol state** (`RawNode.Ready.absSpec`'s first half): the node
comes in as `ownRawNodeAt` at the protocol state `ps`, the queue `qs`, the in-progress boundary `ip`
and the scope flag `sc`, and leaves as `ownRawNodeReadyS` at a named state `s` (`ownRawNodeReady`'s
body) with the scope kept, reading as `ps` (`toPState s = ps`), the boundary `ip + 1`; the messages
handed out read (`absMsgOf`) as the outbox's to others, each to another node; the `Ready`'s soft
state reports `s`'s role; and, in the scope, the committed log handed out a prefix of the log, within
the commit index. (antithesis parity B1, step C4) The scope an `Option RnMode` (at each mode without
snapshots, conf changes, forwarding or async writes); with transfer off every message handed out typed;
the role's protocol reading no longer stated (a pre-candidate reads as a follower: `ReadyOut` reads the
role through `roleProto`).

raft v3.7 (2026-10-16, stage R5; `notes/decisions.md`, D8): **the messages are handed out** --
`rd.Messages` (a `[]*pb.Message` aliasing `r.msgs`, extended by the `msgsAfterAppend` messages to
others) holds the pointers of `ms : List QMsg`, each message owned at `readyDq` (a
`MsgAppResp`/`MsgVoteResp`/`MsgPreVoteResp` at half: `acceptReady` reads the other half's
`To`; the application gets those read-only, `nonissues/raft-ready-messages-read-after-handout.md`;
every other message whole); `Habandon` takes them back. `Entries`/`CommittedEntries` are
`entsRO` (`[]*pb.Entry`, read-only), the read states `readStatesPts` (their contexts bytes, D6),
`rd.Snapshot` `nil` (was the zero `Snapshot`), and the hard state `hsOptC rd.HardState' h` (new; canonical since 2026-11-17:
the `Ready` hands out `hardState()`'s fresh pointer, or `nil`). (D22 S-b, 2026-10-19: with the
witness `hsWit` of a non-`nil` one: the node's term and commit index at the `Ready`, `commitWit`,
and the committed log handed out within the commit index.) (D22l, 2026-10-20: the witness is of
`prevHardSt` as `acceptReady` leaves it, `phsNext rs.phs h`: for a `nil` `HardState` the node's
hard state is `prevHardSt`'s, `RNState.phs`, so every `Ready` bounds its committed log by the
witness of the last non-empty hard state handed out.) (2026-10-31: the log it bounds is the committed log
handed out after the `Ready`, `dlvAfter`: with a snapshot, the log up to the snapshot.) (D22 S-d3a, 2026-10-21: **with a
snapshot pending** too, until then a premise `rs.psnap = false`: the `Ready` then hands it out --
`rd.Snapshot` a fresh clone, half of it the application's (`rdSnapOut`), with the committed log up
to it, the loan `L` (`SnapLoan`); no committed entries -- and with no snapshot restored since the
last `Ready` (`rs.psnap = false`) none, as until then.) -/
abbrev RawNode.readyWithoutAccept.spec : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (sc : Option RnMode),
  (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧ md.forwarding = false ∧
    md.async = false) →
  rs.steps = [] →
  rs.unpersisted = [] →
  -- (2026-11-09 to 2026-11-11, Q8 stage 0 to slice 28n: `γ.reTrace = none`, an untraced node; the
  -- function logs nothing, and the node's logger is handed on in either mode, `TraceLoggerOkS`)
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNodeAt γ rn id rs r qs ip sc }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"readyWithoutAccept"))
      (Val #()))
  {{ (rd : Ready) (ce es : List EntryM) (ms : List QMsg)
      (sts : List ReadStateM) (h : HardStateM) (L : Option SnapLoan), RET #rd;
      -- (#33 S4) at a named state `s`, which reads as `r` (antithesis parity B1: at `r`'s ghost
      -- prefix; until then as `ps`), with the scope kept
      "Hrn" ∷ (∃ s : NState, ownRawNodeReadyS γ rn id rs rd ce es ms false L s ∗
        rnScopeAt γ id sc rs s ∗
        ⌜toRState rs r.fp s = r ∧ uint.nat s.logst.inprogress = ip + 1 ∧
          ms.filterMap (fun q => absMsgOf q.st) ≡ₚ s.outbox.filter (fun m => decide (m.dst ≠ id)) ∧
          (∀ q ∈ ms, q.st.msg.To' ≠ id) ∧
          (∀ md, sc = some md → rs.delivered ++ ce <+: r.p.log ∧
            (rs.delivered ++ ce).length ≤ uint.nat r.p.commit ∧
            -- (#33 S4, 2026-11-24) every message reads as a protocol message: of a type the model
            -- describes (no transfer request stepped in the scope, `NGhost.xs`: `XfOk`'s last clause)
            -- (antithesis parity B1, step C4) at transfer off
            (md.transfer = false → ∀ q ∈ ms, (absMsgOf q.st).isSome))⌝ ∗
        ∃ ss : Option (w64 × StateType), softStateIs rd.SoftState' ss ∗
          ⌜roleAfter rs.role ss = stateW64 s.role⌝) ∗
      "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      -- (out_size C3, 2026-11-12; until then `entsRO`) at contents of bounded size in a cluster
      -- bounding proposed data (`entsROz`)
      "#Hents" ∷ entsROz γ.maxData.isSome rd.Entries' es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms.map QMsg.loc ∗
      "Hmsgs_cap" ∷ ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
      -- (2026-10-16, stage R5, D8) the messages handed out, a response at half
      -- (out_size C3, 2026-11-12; until then `msgOwn` and each one's `snapUf`) at a content
      -- (`msgOwnZ`): pinned (`sentOk`) and, in a cluster bounding proposed data, of bounded size
      "Hmsgs_own" ∷ ([∗list] q ∈ ms, msgOwnZ γ.maxData.isSome q.loc (readyDq q.st) q.st) ∗
      -- (2026-11-01, durability stage II (k), fix C; until then each message's `isRaftMsg` here)
      -- the messages' facts come with the cut (`ownRawNodeReady_handout`)
      -- (2026-10-17; until then at most `rs.term`) within the term ceiling (a granted pre-vote)
      "%Hmsgs_term" ∷ ⌜∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc⌝ ∗
      "Habandon" ∷ (rd.Messages' ↦* ms.map QMsg.loc -∗
                    ownSliceCap Loc rd.Messages' (DFrac.own 1) -∗
                    ([∗list] q ∈ ms, msgOwnZ γ.maxData.isSome q.loc (readyDq q.st) q.st) -∗
                    ownRawNodeReady γ rn id rs rd ce es ms false L -∗
                    ∃ (n : Nat) (u : Bool) (c : w64),
                      ⌜ms.length ≤ n ∧ (es ≠ [] → u = true) ∧
                       (∀ e, ce.getLast? = some e → uint.Z e.Index' ≤ uint.Z c ∧
                         uint.Z e.Index' = (rs.delivered.length : Int) + (ce.length : Int))⌝ ∗
                      ownRawNode γ rn id { rs with outlb := n, unst := u, clb := c }) ∗
      -- (D22 S-d3a) the snapshot: none, or the loan's (until then `rd.Snapshot' = null`); none
      -- with no snapshot restored since the last `Ready`
      "Hsnapz" ∷ rdSnapOut γ rs rd ce es L ∗
      "%Hpsn" ∷ ⌜rs.psnap = false → L = none⌝ ∗
      -- the read states (2026-10-13)
      "#Hrs" ∷ readStatesPts rd.ReadStates' sts ∗
      "#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateRaw γ st) ∗
      -- (2026-10-16, stage R5) the hard state: `nil` when unchanged, else `hardState()`'s fresh
      -- read-only one
      "#Hhard" ∷ hsOptC rd.HardState' h ∗
      -- (#33 S4) a non-empty one differs from `prevHardSt`'s record (raft hands it out only when
      -- `!isHardStateEqual(hardSt, prevHardSt)`)
      "%Hhnew" ∷ ⌜¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) → h ≠ rs.phs⌝ ∗
      -- (D22 S-b) a non-`nil` one is the node's hard state: its witness (`hsWit`), bounding the
      -- committed log handed out; (D22l) of `prevHardSt` after the `Ready` (`phsNext`): a `nil`
      -- or empty one leaves the witness `prevHardSt`'s (`rs.phs`), the node's hard state then
      "#Hhsw" ∷ hsWit γ (phsNext rs.phs h) (dlvAfter rs.delivered ce L).length }}

end spec

end EtcdGrove
end Perennial
