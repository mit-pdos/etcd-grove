/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 11 (2026-11-10): `raft.Step.spec`'s untraced
instance, the statement before slice 11 (stage 0's premise `s.gh.tr = none`, no gate, raft's ghost
state held by `Step` throughout), for the node API (`RawNode`, `node`, `tickElection`,
`tickHeartbeat`), which stays untraced (`notes/decisions.md`, "Q8 stage 1 (slice 11)"). From the one
spec with every resource raft's ghost state at the start (`stepGates_none`), the caller's own `emp`.
-/
module

public import Spec.go_etcd_io.raft.v3.raft__Step
public import Proof.go_etcd_io.raft.v3.TracedStepGates

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section untraced
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `raft.Step.spec` at an untraced node (the statement before slice 11). -/
abbrev raft.Step.untracedTriple : Prop :=
  ∀ (c : CfgM)
    -- (2026-10-14, stage B7) the mode of the ghost state: static (`ownRaftGhost`, at a
    -- configuration with the ghost state's voters) or dynamic (`ownRaftGhostR`, the node's
    -- reconfiguration state over the struct's configuration); see `StepGhostMode.lean`
    (md : GMode)
    (γ : RaftNames) (r : Loc) (id : w64) (s : NState)
    -- (stage R4) the message's pointer; its scalars `m`, entries `ents`, context `ctx`,
    -- snapshot `sn` and responses `rs`
    (ml : Loc) (m : MessageM)
    -- The message's `Entries` (`[]` for a message without entries), bound here rather
    -- than in `"Hm"` since 2026-10-06. (Until 2026-10-10 also, for a `MsgProp`, the
    -- client's result predicate for each entry: a proposal's atomic update is now
    -- deposited before the proposal reaches `Step` (`prop_deposit`), and its entries'
    -- `isMessage` says so (`entData`).)
    (ents : List EntryM)
    -- (2026-10-12) the list the message's `Context` holds, which the abstract message
    -- carries (a heartbeat's response echoes it; a forwarded proposal keeps it)
    (ctx : List w8) (sn : Option SnapshotM) (rs : List Loc),
  StepMsg m →
  -- (Until 2026-10-14, stage B8, a premise `m.Type' = MsgSnap → id ∈ γ.reCfg`: the node one of
  -- the ghost state's voters, which a snapshot's `restore` needs. It is now one of the
  -- snapshot's ids, in `"Hsnap"`.)
  -- A `MsgHup` is local (`Term = 0`) and may start an election, which increments the
  -- term; `send` panics if that wraps to zero.
  (m.Type' = MsgHup →
     m.Term' = W64 0 ∧
     uint.Z s.term + 1 < 2 ^ 64 ∧
     -- (2026-10-17) with pre-vote on a `MsgHup` pre-campaigns: its `MsgPreVote`s are of the next
     -- term, which the ceiling (`NGhost.tc`) must cover; the `RawNode` raises it first
     (s.prevote = true → uint.Z s.term + 1 ≤ uint.Z s.gh.tc) ∧
     -- (D19i part 1) the floor at most `applied` (`hup`'s)
     uint.Z s.logst.fl ≤ uint.Z s.logst.applied) →
  (m.Type' = MsgVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0) →
  (m.Type' = MsgVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0) →
  -- Pre-vote (2026-10-04), by what the transport and the peers guarantee, like
  -- `MsgVote`; Go checks none of it. Two more:
  -- - a `MsgPreVote` of a higher term is answered at the node's own term when the
  --   candidate's log is behind (`Term: r.Term, Reject: true`; the term is not raised
  --   for a pre-vote), and `send` panics on a vote message with `Term = 0`. So a node
  --   at term `0` must find every pre-vote candidate up to date -- true of a node
  --   whose log holds nothing past term `0`, i.e. of every node etcd builds (a fresh
  --   node has an empty log; `Bootstrap` and `RestartNode` start at a term of at
  --   least the log's), but not implied by `ownRaftPhys`, which admits a persisted
  --   log ahead of the persisted term;
  -- - a `MsgPreVoteResp` at a pre-candidate may win, which runs the real `campaign`
  --   and increments the term: it must not wrap (as for `MsgHup`). Only at a
  --   pre-candidate (2026-10-10: `RawNode.Advance` may step its own pre-vote response
  --   after a won pre-vote raised the term, at a candidate, which ignores it);
  -- - a `MsgPreVote`'s term within the node's term ceiling (`NGhost.tc`; 2026-10-17, until
  --   then it reached only a node with pre-vote on, and `RawNode.Step` took none): a granted
  --   pre-vote answers at the request's term (`OutTermOk`).
  (m.Type' = MsgPreVote →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id ∧
     (s.term = W64 0 →
      plogUpToDate s.logst.prev (s.logst.sents ++ s.logst.uents)
        (entryID.mk m.LogTerm' m.Index') = true) ∧
     -- (2026-10-17) a grant answers at the requested term, which the ceiling (`NGhost.tc`)
     -- must cover when it is past the node's; the `RawNode` raises it first
     (uint.Z m.Term' ≤ uint.Z s.term ∨ uint.Z m.Term' ≤ uint.Z s.gh.tc)) →
  (m.Type' = MsgPreVoteResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     (s.role = .preCandidate → uint.Z s.term + 1 < 2 ^ 64)) →
  -- The replication types, by what the transport and the peers guarantee (Go checks
  -- none of it). A leader's `MsgApp`/`MsgHeartbeat`, and a `MsgHeartbeatResp`, come
  -- from another node: `send` never queues them to oneself. An accepting
  -- `MsgAppResp` may be the node's own (`appendEntry`'s self-acknowledgement); a
  -- rejecting one is not.
  (m.Type' = MsgApp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgHeartbeat →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  (m.Type' = MsgAppResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧
     (m.Reject' = true → m.From' ≠ id)) →
  (m.Type' = MsgHeartbeatResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- A leader's `MsgSnap`, likewise (2026-10-02).
  (m.Type' = MsgSnap →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧
     m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- `MsgBeat` and `MsgProp` are local (`Term = 0`); a proposal is not yet stamped
  -- with a sender (`From = 0`), or is stamped with the node's own id
  -- (`RawNode.Propose` sets `From: r.id`; since 2026-10-06). The proposal's batch is
  -- constrained in `Hm` below, where its list is named.
  -- (2026-10-17, `CheckQuorum` on) so is the quorum check `tickHeartbeat` steps
  (m.Type' = MsgBeat ∨ m.Type' = MsgCheckQuorum → m.Term' = W64 0) →
  (m.Type' = MsgProp →
     m.Term' = W64 0 ∧
     (m.From' = W64 0 ∨ m.From' = id)) →
  -- The two local acknowledgements `RawNode.Advance` steps (2026-10-05), as
  -- `acceptReady` builds them (`InvRawnode.lean`, `appendAckMsg`, `applyAckMsg`). A
  -- `MsgStorageAppendResp` (until D22 S-d2 carrying no snapshot) is not from a later term (it would make the node
  -- step down to a term no message brought), and -- when its `stableTo` runs (`Term`
  -- `0` or current, a nonzero `Index`) -- acknowledges only persisted entries
  -- (`StableOk`: Go compares only the term at `Index`). A `MsgStorageApplyResp` is
  -- local (`Term = 0`); its entries' last index is committed (the bound is in `"Hm"`,
  -- where the list is named).
  -- (D22 S-d2, 2026-10-21) It may carry a snapshot (until then `sn = none`), the one the
  -- storage is at if it is the pending one (`sat`; the application's receipt absorbed before
  -- the step), at or below the log's boundary (the pending one, or older after a second restore),
  -- (until stage U3, 2026-10-28, in the static mode only), with `appliedTo`'s auto-leave
  -- premise; the `StableOk` is of the log in the window the arm opens (`ackLog`).
  (m.Type' = MsgStorageAppendResp →
     (∀ sv, sn = some sv →
        snapHit s.logst.snap sv.Metadata'.Index' = s.logst.sat ∧
        uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.prev.index' ∧
        -- (2026-10-28, stage U0; until then `appliedTo`'s auto-leave premise, `c.autoLeave = true →
        -- s.role ≠ .leader`) `appliedSnap`'s rebuild: a follower, the snapshot as `SnapAckOk` in
        -- the static mode, and (stage U3; until then the static mode only) as `SnapAckDyn` in the
        -- dynamic one
        s.role = .follower ∧ ((md.isDyn = false ∧ SnapAckOk γ id sv) ∨ SnapAckDyn md s sv) ∧
        -- (D22 S-d4 item 3) with a snapshot pending and the storage back, the storage holds the
        -- log up to the acknowledged snapshot (`LogState.sxt`; `appliedSnap` moves `applying` there)
        (s.logst.snap ≠ none → s.logst.lent = false →
          uint.Z sv.Metadata'.Index' ≤ uint.Z s.logst.sxt) ∧
        (∀ k, s.gh.snp = some k → uint.Z k.sid.index' ≤ uint.Z sv.Metadata'.Index')) ∧
     uint.Z m.Term' ≤ uint.Z s.term ∧
     (m.Term' = W64 0 ∨ m.Term' = s.term →
      m.Index' ≠ W64 0 →
      StableOk (ackLog s.logst sn) (entryID.mk m.LogTerm' m.Index')) ∧
     -- (2026-10-10) `stableTo` may hand out every unstable entry still to come
     -- (`NGhost.unst`): `RawNode.Advance` steps it only after `acceptReady` reset the flag
     s.gh.unst = false) →
  (m.Type' = MsgStorageApplyResp → m.Term' = W64 0) →
  -- Read-index (2026-10-13): a request is unstamped (`Term = 0`; a local one from
  -- `ReadIndex`, a forwarded one from a follower); a response is a leader's, from another
  -- node. (Until 2026-10-14 also not in a single-voter configuration, `IsSingleton`'s
  -- immediate answer: in scope since the pinned raft has the fix of
  -- `issues/raft-readindex-singleton-stale.md`.)
  (m.Type' = MsgReadIndex → m.Term' = W64 0) →
  -- (2026-10-14, stage B7, to 2026-10-29, stage U5: `appliedTo`'s automatic leave, proved since,
  -- was excluded here by a premise `m.Type' = MsgStorageApplyResp → c.autoLeave = true → s.role ≠
  -- .leader`)
  (m.Type' = MsgReadIndexResp →
     m.To' = id ∧ m.Term' ≠ W64 0 ∧ m.From' ≠ W64 0 ∧ m.From' ≠ id) →
  -- (2026-10-13) the local reports, `ForgetLeader` and leader transfer (`RestMsgOk`)
  RestMsgOk s m ents ctx →
  -- `r.step` agrees with the role (until 2026-10-14 `NStateRel s ps`, with the protocol
  -- state `ps` the ghost state was about: now `toPState s`, in `ownStepGhost`)
  NStateWf s →
  -- (2026-10-14, stage B7) the dynamic mode's premises (`GMode.Pre`): no `MsgSnap` (a
  -- snapshot restore at a dynamic configuration is stage B8), a pre-candidate only with its
  -- campaign guard (`PreGuardF`; 2026-10-25, T-M M2b: until then none, pre-vote off at the
  -- `RawNode` API), A1 at a `MsgStorageApplyResp` (no conf entry between the
  -- configuration index and the acknowledged index: `ApplyConfChange` before `Advance`), and a
  -- log short enough for a dropped proposal's `pendingConfIndex`; none in the static mode
  md.Pre m ents s →
  -- (2026-10-19, D21 M3) no snapshot in the no-snapshot mode (`NGhost.ns`; `RawNode.Step` takes
  -- none)
  (m.Type' = MsgSnap → s.gh.ns = false) →
  -- (2026-11-09, Q8 stage 0 of `notes/trace-validation-plan.md`) an untraced node: its trace
  -- hooks see a nil logger (`TraceLoggerOkS`); stage 1 replaces this premise by the traced
  -- capability (`trCapB s.gh.tr …`, `TracedHooksDraft.lean`)
  s.gh.tr = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hghost" ∷ ownStepGhost γ md c id s ∗
      -- (raft-final, 2026-10-29, U7: the design's §2.3) a stamped transfer request's witness that
      -- the node leads its term (`isRaftMsg`'s transfer clause, from the forwarder's `xfW`):
      -- `ownStepGhost_xferRefute` refutes a follower of that term with a leader, which would forward
      -- it again (`send` panics on a stamped `MsgTransferLeader`); until then `RestMsgOk`'s premise
      "#Hxfer" ∷ □ (⌜m.Type' = MsgTransferLeader ∧ m.Term' ≠ W64 0⌝ -∗ isLeader γ id m.Term') ∗
      -- The message's `Entries` slice, holding `ents` (`[]` for a message without
      -- entries, `Entries = nil`):
      -- - a proposal is a local message whose batch the caller owns outright --
      --   `appendEntry` writes `Term`/`Index` into the entries -- while every network
      --   message's entries are read-only;
      -- - the slice's capacity, owned: `raftLog.maybeAppend` can adopt the caller's
      --   slice (`unstable.truncateAndAppend`'s replace arm), so a received `MsgApp`
      --   needs it;
      -- - a proposal's batch is non-empty (`stepLeader`'s `Panicf`) and short enough for
      --   `appendEntry`'s indices not to wrap, and (2026-10-13, reconfiguration stage D;
      --   until then `EntryNormal` only) its conf-change entries' bytes decode (`ccEntsOk`:
      --   `stepLeader` `Unmarshal`s them, panicking on an error);
      -- - what the message carries as a protocol message: its abstraction (`absMsg`,
      --   which needs the entries) was legitimately sent -- for every type but
      --   `MsgSnap`, whose abstraction is `absSnap` (`"Hsnap"` below).
      -- (stage R4) the message, taken for good (`msgIn`: the struct, the `Entries` capacity
      -- and the snapshot owned; the entry pointers owned for a `MsgProp`, read-only
      -- otherwise; the `Context` holding `ctx`)
      "Hm" ∷ (
         "Hmsg_in" ∷ msgIn ml (if m.Type' = MsgProp then DFrac.own 1 else DFrac.discard)
                       ⟨m, ents, sn, ctx, rs⟩ ∗
         -- a proposal's conf-change entries' bytes, which decode
         -- (2026-10-19, D21 M6) and its entries' tickets (`entTk`), which the leader consumes
         "Hents" ∷ (if m.Type' = MsgProp then
                      iprop((∃ cs, ccEntsOk ents cs) ∗ [∗list] e ∈ ents, entTk γ e) else emp) ∗
         "%Hprop" ∷ ⌜m.Type' = MsgProp →
                      ents ≠ [] ∧
                      (ents.length : Int) < 2^61⌝ ∗
         -- (2026-10-22, D38a) a message a follower forwards to the leader has no responses
         -- (`send`'s premise; raft sets them only on its local storage messages)
         "%Hnors" ∷ ⌜m.Type' = MsgProp ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader →
                      rs = []⌝ ∗
         -- (D19i part 1) and at most `applying` (`RawNode.Advance` acknowledges entries
         -- `Ready` handed out; `appliedTo` then leaves `applying`)
         "%Happly" ∷ ⌜m.Type' = MsgStorageApplyResp →
                       ∀ e, ents.getLast? = some e →
                       uint.Z e.Index' ≤ uint.Z s.logst.committed ∧
                       uint.Z e.Index' ≤ uint.Z s.logst.applying⌝ ∗
         "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf m.Type' = some ty⌝ -∗
                            ⌜ty ≠ .snap⌝ -∗
                            isMessage γ (absMsg ty m ents ctx))) ∗
      -- the `Context`. (Until 2026-10-13 not the leader-transfer marker -- a transfer's
      -- vote request is now an ordinary one, whose `force` only bypasses the lease check
      -- (2026-10-17, `checkQuorum` on) -- and empty on a heartbeat response; a read-index position is now what
      -- `isMessage` says it is.)
      -- (2026-10-13) a read-index request carries a read credit (`rdOwn`)
      "Hcred" ∷ rdCred γ (if m.Type' = MsgReadIndex then 1 else 0) ∗
      -- (2026-10-14, stage R) a later credit, for the ghost step: the commit invariant's
      -- registry half is opened around it, its persistent updates fired at every commit
      "Hlc" ∷ £ 1 ∗
      -- A `MsgSnap`'s snapshot (2026-10-02; any `ConfState` since 2026-10-14, stage B8): what
      -- `m.Snapshot` points to, read-only, and the four lists `scfg` its `ConfState`'s
      -- slices hold, read-only (`ownCSL`); well formed (`SnapScope`, `Spec/raft__restore.lean`:
      -- `CSWf`, no repeats, `AutoLeave` off when not joint, the index below `2^61` -- a pending
      -- snapshot becomes the `Storage`'s boundary, which `isStorageD`'s `Hbounded` bounds the
      -- same way) (since D22 S-b, D22j, naming the node or not: `restore`'s `!found` exit refuses
      -- it, `Step.snapStale`; until then a premise `CSLists.Has`); what the mode asks of it
      -- (`GMode.SnapOk`: statically the ghost state's voters, not joint; dynamically A3, the
      -- `ConfState` the fold of the snapshot's prefix); and the abstraction `absSnap`
      -- (`Defs.lean`) -- the snapshot's metadata, not `m`'s own `Index`/`LogTerm` -- was
      -- legitimately sent. Transport/client assumptions like the rest. (Since D22 S-b′4,
      -- 2026-10-20, the scope and the static mode's need are the message certificate's, under
      -- the lists' naming the node, `SnapScopeIf`/`GMode.SnapOkIf`: only the index bound and,
      -- dynamically, `GMode.SnapOk` (`GMode.SnapDyn`) were left; since 2026-10-28, stage U3c,
      -- dynamically the certificate's dynamic clause too, under the lists' naming the node: only
      -- the index bound.)
      -- (stage R4) the snapshot the message holds (`sn = some sv`, owned in `"Hm"`) and the
      -- lists of its `ConfState` (until the retarget the read-only slices, `ownCSL`)
      "#Hsnap" ∷ □ (⌜m.Type' = MsgSnap⌝ -∗
         ∃ (sv : SnapshotM) (scfg : CSLists),
           -- (D22 S-b′4, 2026-10-20) the index bound only: the lists' scope and, statically, what
           -- the mode asks come from the message's certificate (under its naming the node)
           ⌜sn = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
             uint.Z sv.Metadata'.Index' < 2^61⌝ ∗
           -- (D22 S-b′3, 2026-10-20) certified (`isMessageC`): its snapshot's configuration
           -- certificate, which the step registers in the storage (`certLink`) before the restore
           isMessageC γ (absSnap m sv scfg) ∗
           -- (D22 S-r, 2026-10-21) and its data certificate, registered with it
           snapDataOk γ sv.Metadata'.Index' sv.Data') }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface) (s' : NState) (c' : CfgM) (md' : GMode), RET #err;
      "Hphys" ∷ ownRaftPhysCV c' c'.voters r id s' ∗
      "Hghost" ∷ ownStepGhost γ md' c' id s' ∗
      "%Hwf'" ∷ ⌜NStateWf s'⌝ ∗
      -- the step in the mode's model: `StepC c` statically, `StepR` dynamically
      -- (2026-10-14, stage B7 part 2) and in the dynamic mode the configuration index moves only
      -- by a `MsgStorageApplyResp` (`CidxMove`)
      "%Hrefines" ∷ ⌜md.StepOut c id m s s' md'⌝ ∗
      -- the configuration afterwards: `c`, but the snapshot's after its acknowledgement (2026-10-28,
      -- stage U0; until then after a `MsgSnap` that restored it)
      "%Hcfg'" ∷ ⌜(m.Type' = MsgStorageAppendResp → sn = none) → c' = c⌝ ∗
      -- for the local messages `RawNode` steps, what is kept of the physical state
      -- (2026-10-09)
      -- (D22 S-d2) but for a snapshot's acknowledgement, which moves the log as `ackSnapLog` says
      -- and nothing else
      "%Hlocal" ∷ ⌜((m.Type' = MsgStorageAppendResp → sn = none) → LocalStepOk m ents s s') ∧
                   (m.Type' = MsgStorageAppendResp → ∀ sv, sn = some sv →
                      -- (U0) at the snapshot's configuration, the tracker rebuilt
                      c' = snapCfg sv sv.Metadata'.ConfState'.lists ∧
                      (∃ (prs : GMap w64 Loc) (pvs : GMap w64 Progress) (il : Bool),
                        s' = { s with logst := ackSnapLog s.logst m s.term sv, progress := prs,
                                      prvals := pvs, isLearner := il }) ∧
                      -- (2026-10-28, stage U3c) dynamically the configuration index at the
                      -- snapshot's, the full prefix kept (`StepR.applySnap`)
                      (∀ dec c0 h0 g, md = .dyn dec c0 h0 g →
                        ∃ cs', md' = .dyn dec c0 h0 ⟨uint.nat sv.Metadata'.Index', cs', g.fp, g.decs⟩))⌝ ∗
      -- for every other message but a snapshot (and its acknowledgement), what is kept of the
      -- log (2026-10-09)
      -- (raft-final phase 2, 2026-10-29) but a transfer request, which may record the node's
      -- leader and term in `NGhost.xw` (the forward's witness, `ownStepGhost_xw_record`)
      "%Hframe" ∷ ⌜m.Type' ≠ MsgSnap → m.Type' ≠ MsgStorageApplyResp → m.Type' ≠ MsgTransferLeader →
                   (m.Type' = MsgStorageAppendResp → sn = none) → NetFrame s s'⌝ ∗
      -- a transfer request's frame: `NetFrame` but for the ghost state's `xw`, which only grows
      "%Hxwframe" ∷ ⌜m.Type' = MsgTransferLeader → NetFrame s { s' with gh := s.gh } ∧
                   s'.gh = { s.gh with xw := s'.gh.xw } ∧ ∀ p, p ∈ s.gh.xw → p ∈ s'.gh.xw⌝ ∗
      -- and how the term moves (2026-10-09)
      "%Hterm" ∷ ⌜m.Type' ≠ MsgSnap → TermStep m s s'⌝ ∗
      -- and what a response does to the role and the term (2026-10-10)
      "%Hresp" ∷ ⌜RespStep m s s'⌝ ∗
      -- (2026-10-20, D22 S-c) for a snapshot, what is kept of the state and how the term moves
      -- (`SnapStep`) (until stage U0 also the configuration afterwards, `SnapCfgOut`)
      "%Hsnapfr" ∷ ⌜m.Type' = MsgSnap → SnapStep m s s' ∧
                     -- (D22 S-d3b) and what it did to the log (`SnapLogStep`)
                     ∀ sv, sn = some sv → SnapLogStep sv m s s'⌝ ∗
      -- (D22 S-d3b, 2026-10-21) a `MsgApp`'s truncation's mark (`AppTrunc`)
      "%Htrunc" ∷ ⌜m.Type' = MsgApp → AppTrunc m ents s s'⌝ ∗
      -- only a proposal can be dropped, with `ErrProposalDropped`
      "Herr" ∷ (⌜err = interface.nil⌝ ∨
                (⌜m.Type' = MsgProp⌝ ∗
                 globalAddr ErrProposalDropped ↦□ err)) }}

/-- `raft.Step.spec`'s untraced instance: the gates from the struct's nil logger, every resource raft's
ghost state (`stepGates_none`), the caller's `emp`. -/
theorem raft.Step.untraced (h : raft.Step.spec (GF := GF) (hG := hG)) :
    raft.Step.untracedTriple (GF := GF) (hG := hG) := by
  intro c md γ r id s ml m ents ctx sn rs Hsm Hhup Hvote Hvoteresp Hprevote Hprevoteresp
    Happ Hhb Happresp Hhbresp Hsnapt Hbeat Hprop Hsar Hsapr Hri Hrir Hrest Hwf Hpre Hnsx htr
  iintro %Φ ⟨#Hinit, Hphys, Hghost, #Hxfer, Hm, Hcred, Hlc, #Hsnap⟩ HΦ
  icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl, #Htl, %Htlok, Hphys⟩
  ihave Hgates := stepGates_none (GF := GF) c r id s m ents sn ctx rs tl
    iprop(ownStepGhost γ md c id s ∗ emp) (ownStepGhost γ md c id s)
    (by iintro ⟨H, -⟩; iexact H) htr Htlok $$ Htl
  have hgi : ghostIn γ md c id s ⟨iprop(emp), ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      ownStepGhost γ md c id s, ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      ownStepGhost γ md c id s, ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      fun _ _ => ownStepGhost γ md c id s⟩ =
    ⟨iprop(ownStepGhost γ md c id s ∗ emp), ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      ownStepGhost γ md c id s, ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      ownStepGhost γ md c id s, ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      fun _ _ => ownStepGhost γ md c id s⟩ := rfl
  iapply h c md γ r id s ml m ents ctx sn rs
    ⟨iprop(emp), ownStepGhost γ md c id s, ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      ownStepGhost γ md c id s, ownStepGhost γ md c id s, ownStepGhost γ md c id s,
      ownStepGhost γ md c id s, ownStepGhost γ md c id s, fun _ _ => ownStepGhost γ md c id s⟩
    iprop(emp) Hsm Hhup Hvote Hvoteresp Hprevote Hprevoteresp
    Happ Hhb Happresp Hhbresp Hsnapt Hbeat Hprop Hsar Hsapr Hri Hrir Hrest Hwf Hpre Hnsx
    (fun _ => htr) (fun _ _ => htr) (fun _ _ => htr) (fun _ h => absurd htr h)
    $$ [Hphys Hghost Hm Hcred Hlc Hgates]
  · rw [hgi]
    iframe Hinit Hphys Hghost Hxfer Hm Hcred Hlc Hsnap Hgates
    unfold stepClose
    iintro %s' %B %recv %_ Hout
    ihave HX := stepOut_const (GF := GF) iprop(emp) (ownStepGhost γ md c id s) $$ Hout
    imodintro
    iframe HX
    ipureintro; exact ⟨trivial, OutTrStep.of_none htr⟩
  inext
  iintro %err %s' %c' %md' H
  iapply HΦ $$ %err %s' %c' %md'
  iNamed H
  iframe Hphys Hghost Herr
  ipureintro
  exact ⟨Hwf', Hrefines, Hcfg', Hlocal, Hframe, Hxwframe, Hterm, Hresp, Hsnapfr, Htrunc⟩

end untraced

end EtcdGrove
end Perennial
