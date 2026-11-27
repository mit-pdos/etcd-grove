-- The copy for the part `KvRaft/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Lean-first (#33 S3c step 3, `notes/antithesis-rawnode-design.md` §2.2, §2.6). **The strengthened
`RawNode` specs, as statements**: for each function the harness calls (`Step`, `Tick`, `Propose`,
`HasReady`, `Ready`, `Advance`) and for `NewRawNode` at an empty storage, the old spec's text with
`ownRawNode` replaced by `ownRawNodeAt` (`RawNodeAt.lean`) and the input's exact effect on the
protocol state added (`Protocol/InputEnd.lean`'s relations, `ReadyOut`, `PIdle`). Each is proved in
its function's proof file (`RawNode.<F>.wp_absProof`, phase 2); the old `RawNode.<F>.spec`, text
unchanged, is its corollary (`RawNode.<F>.spec_of_abs.law`, stated here, proved with them).

**One text, two predicates.** A triple is written once, as `RawNode.<F>.form R S`, over the node's
predicate `R γ rn id rs r qs ip` (antithesis parity B1, design §4: over the node's `RState` `r`, until
then its `PState` `ps`) and a predicate `S : RnMode → Prop` of the scope's modes guarding the new post
conjuncts (`∀ md, S md → End`):
- `RawNode.<F>.absSpec := ∀ sc, form (ownRawNodeAt · · · · · · (basicScope sc)) (fun md => basicScope sc = some md)`: in the
  harness's basic scope (`sc = true`, the scope `some {}`) the exact effect, outside it (`sc = false`, what `ownRawNode_at` gives any
  `ownRawNode`) the old spec's content, which makes `spec_of_abs` provable;
- the API form (`RawNodeApi.lean`): `form rawNode (fun md => md = {})`.

**The ends over `RState`** (antithesis parity B1, design §4): `Step` and `Propose` give `RecvEndR` (at
every `Adm`: no snapshot in the scope, so the ghost prefix is kept), `Tick` `TickEndR`, `Advance`
`AdvanceEndR` (stage 3b; given no undecided conf entry among those applied), all at the node constant `rs.k`, the
configuration the node's `r.cfg.cfg` (until then the names' `rnCfg γ`); `HasReady`, `Ready` read `r.p`.
`HasReady` (whose old false arm is `ownRawNodeIdle`, internal) and the start spec are written out.

Deviations from the design's table (§2.6 of the design): the pre is at any queue `qs` (not `[]`:
the old `Step`, `Tick`, `Propose` specs allow a `Ready` outstanding), kept by those three; `Step` in
the scope only for the harness's network types (`stepTypes md`; the old premises otherwise), with
reads off a heartbeat response with no context, at non-voters off a sender among the voters (else
`errStepPeer`'s unchanged arm);
`ProposeEnd` at the proposal message (`InputEnd.lean`'s form); `Ready`'s post at `pAccepted ps` (the
read states cleared too, `acceptReady`'s `r.readStates = nil`) with the queue and `ReadyOut` guarded;
`PIdle` without the id (unused); `ReadyOut` without the voters (2026-11-24: a response goes to
the sender of a message received, which no node-local fact names a voter; the Sim side reads the
destinations off the network relation) and with the messages' protocol readings, not their
types (a physical message of no model type, `MsgTimeoutNow`/`MsgTransferLeader`, has none:
`msgAbs`'s `none` arm).

**The in-progress boundary** (2026-11-24, decision 3): each form's node predicate takes `ip`
(`ownRawNodeAt`'s, `offsetInProgress - 1`). An input (`Step`, `Tick`, `Propose`) and `Advance` leave it
at `min ip (lcpLen ps.log ps'.log)` (`truncateAndAppend` lowers `offsetInProgress` to the first index
it writes, the first conflict); `HasReady`'s `false` has it at the log's end; `Ready` hands out the
entries from `ip + 1` and moves it to the log's end (`acceptInProgress`). Each guarded by `S`.
-/
module

public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeAt
public import KvRaft.Proof.go_etcd_io.raft.v3.Protocol.InputEnd
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__Step
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__Tick
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__Campaign
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__Propose
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__Ready
public import KvRaft.Spec.go_etcd_io.raft.v3.RawNode__Advance
public import KvRaft.Proof.go_etcd_io.raft.v3.RawNodeStartSpec

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- The static configuration of the harness's cluster: the ghost state's voters, simple, no
learners (`CfgStatic`'s; the end relations read only its quorums and voters). -/
def rnCfg (γ : RaftNames) : CfgM := CfgM.simple γ.reCfg ∅

/-- The message types the harness's network delivers to `RawNode.Step`: replication and leader
election (no pre-vote, read-index, transfer, snapshot or local report). -/
def antStepTypes : List w32 :=
  [MsgApp, MsgAppResp, MsgVote, MsgVoteResp, MsgHeartbeat, MsgHeartbeatResp]

/-- (antithesis parity B1, design §2) **The message types the harness's network delivers to
`RawNode.Step` at the mode `md`**: `antStepTypes`, and each feature's types when it is on (the
pre-vote pair, the read-index pair, the transfer pair, a forwarded proposal, a snapshot, the storage
acknowledgements). -/
def stepTypes (md : RnMode) : List w32 :=
  antStepTypes ++ (if md.prevote then [MsgPreVote, MsgPreVoteResp] else []) ++
  (if md.reads then [MsgReadIndex, MsgReadIndexResp] else []) ++
  (if md.transfer then [MsgTransferLeader, MsgTimeoutNow] else []) ++
  (if md.forwarding then [MsgProp] else []) ++ (if md.snapshots then [MsgSnap] else []) ++
  (if md.async then [MsgStorageAppendResp, MsgStorageApplyResp] else [])

/-- The first harness's types: every feature off. -/
theorem stepTypes_empty : stepTypes {} = antStepTypes := by
  simp [stepTypes]

/-- The initial protocol state of a node of a cluster without a bootstrap log: term `0`, no vote,
a follower with no leader, no tally, nothing queued, the empty log at `base0`, commit `0`. -/
abbrev pInit : PState := initPState

/-- The protocol state after `Ready`'s `acceptReady`: the outbox handed out (`r.msgs`,
`r.msgsAfterAppend`: to the application or to `stepsOnAdvance`) and the read states
(`r.readStates = nil`); nothing else of `PState` moves. -/
def pAccepted (ps : PState) : PState :=
  { ps with outbox := [], rd := { ps.rd with states := [] } }

/-- (antithesis parity B1) `pAccepted` over `RState`: the bookkeeping fields kept. -/
def rAccepted (r : RState) : RState := { r with p := pAccepted r.p }

/-- (antithesis parity B1) **A fresh node's `RState`** (`NewRawNode` at an empty storage): the initial
protocol state, nothing applied, no pending conf index, no snapshot, the configuration `cs` at index
`0`, no ghost prefix (the Sim's `PInitR` at a run without boot). -/
def rInit (cs : CCState) : RState :=
  { p := pInit, applied := W64 0, pci := W64 0, snap := false, cidx := 0, cfg := cs, fp := [] }

/-- **`HasReady`'s `false`, at the protocol level** (design §2.2, revision 2-3): nothing queued
(Go's `HasReady` is true on any message, self-addressed or not, `rawnode.go:460`); the hard state the
last reported one (`prevHardSt`'s record `rs.phs`: the zero one at a fresh node); the role the last
reported soft state's (Go compares `softState()` with `prevSoftSt`; antithesis parity B1, item 5:
its protocol reading `roleProto`, a reported pre-candidate a follower); the log the durable state the
client entered (nothing unpersisted: `hasNextUnstableEnts` false). -/
def PIdle (rs : RNState) (ps : PState) : Prop :=
  ps.outbox = [] ∧ HardStateM.mk ps.term ps.vote ps.commit = rs.phs ∧ roleProto rs.role = ps.role ∧
  rs.dur.ents = ps.log

/-- **A `Ready`'s fields against the node's protocol state at the call** (design §2.2, "The `Ready`
binding"): the role it reports is the node's (`roleAfter`, `softStateIs`; antithesis parity B1, item 5:
read by `roleProto`, a reported pre-candidate a follower with no leader); the hard state after it is
the node's term, vote and commit (`phsNext`); the durable state the write makes has the node's log,
the entries `es` the log's suffix from `es[0].Index`; the messages' protocol readings are the outbox's but
those to the node itself (which go to `stepsOnAdvance`), each message to another node; the committed entries are
the log's after those delivered, up to at most the commit index; no snapshot (`L = none`). -/
def ReadyOut (id : w64) (rs : RNState) (ps : PState) (h : HardStateM)
    (es ce : List EntryM) (ms : List QMsg) (ss : Option (w64 × StateType)) (L : Option SnapLoan) :
    Prop :=
  (roleProto (roleAfter rs.role ss) = ps.role ∧
    (roleAfter rs.role ss = StatePreCandidate → ps.lead = W64 0)) ∧
  phsNext rs.phs h = HardStateM.mk ps.term ps.vote ps.commit ∧
  (readyDurable rs.dur (phsNext rs.phs h) L es).ents = ps.log ∧
  (∀ e0 ∈ es.head?, ps.log.drop (uint.nat e0.Index' - 1) = es) ∧
  ms.filterMap (fun q => absMsgOf q.st) ≡ₚ ps.outbox.filter (fun m => decide (m.dst ≠ id)) ∧
  (∀ q ∈ ms, q.st.msg.To' ≠ id) ∧
  rs.delivered ++ ce <+: ps.log ∧ (rs.delivered ++ ce).length ≤ uint.nat ps.commit ∧
  L = none

/-- (antithesis parity B1, Q3) **A `Ready`'s untyped message against the node's protocol state** at
the call (`p`) and the mode `md`: a `MsgTimeoutNow` from the node at a term past `0`; every one to
another node, of a term at most the node's (`XQOk`); a forwarded `MsgTransferLeader` past term `0`
(its `NGhost.xw` record's, `XScopeOk`: raft forwards at a known leader's term) and, with non-voters off,
to a member of the configuration (its destination the node's leader when it forwarded, `XScopeOk`). No
destination fact for a `MsgTimeoutNow` (the driver routes by destination, dropping one to a
non-server; the lead's decision, Q3 option 1): what a `MsgTimeoutNow` says of its destination is
`isRaftMsg`'s timeout clause (antithesis parity B1, option (b): the destination acknowledged an index
past `0` at the message's term, durable `isAcked`, from the sender's `NGhost.xt` witnesses), which the
`Ready` hands out with every message (`"#Hlead"`, `isRaftMsg`). -/
def XReadyOk (γ : RaftNames) (md : RnMode) (id : w64) (p : PState) (x : XMsg) : Prop :=
  (x.ty = .timeoutNow → x.src = id ∧ x.term ≠ W64 0) ∧
  (x.dst ≠ id ∧ uint.Z x.term ≤ uint.Z p.term) ∧
  (x.ty = .transferLeader → x.term ≠ W64 0) ∧
  (md.nonVoters = false → x.ty = .transferLeader → x.dst ∈ γ.reCfg) ∧
  -- (antithesis parity B1, transfer source) a forward's sender the node itself (`send` puts its id for
  -- an unset `From`) or one the cluster's acknowledgement map names (`XScopeOk`'s sender clause)
  (x.ty = .transferLeader → x.src = id ∨ (γ.reAcks !! x.src).isSome)

end pure

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-! ### `RawNode.Step` -/

/-- `RawNode.Step.spec`'s triple over the node predicate `R`, at a queue `qs` kept, and (under `S`)
for a message of the harness's types, the exact end state `RecvEnd` from the protocol state `ps` at
the call to the one `ps'` after, at the message's abstraction. -/
abbrev RawNode.Step.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (ml : Loc) (st : MsgSt),
  NetMsgOk id st →
  -- (#33 S3c) in the scope, a message of the harness's network at the mode (antithesis parity B1:
  -- `stepTypes md`), with reads off a heartbeat response with no read-index context, with non-voters
  -- off from a voter (2026-11-24: a response from a sender outside the progress map returns
  -- `errStepPeer` with the state unchanged, not `RecvEnd`'s step-down to a higher term;
  -- notes/specs-only/ledger.md. Antithesis parity B1, lead-approved: with non-voters on the sender may
  -- be outside it, `%Hend`'s unchanged arm)
  -- (antithesis parity B1, transfer source, lead-approved 11-27) a transfer request's sender one the
  -- cluster's acknowledgement map names (`XScopeOk`'s sender clause, what a `Ready` reads of a forward)
  (∀ md, S md → st.msg.Type' ∈ stepTypes md ∧
    (md.reads = false → st.msg.Type' = MsgHeartbeatResp → st.ctx = []) ∧
    (md.nonVoters = false → st.msg.From' ∈ γ.reCfg) ∧
    (st.msg.Type' = MsgTransferLeader → (γ.reAcks !! st.msg.From').isSome)) →
  uint.Z st.msg.Term' ≤ uint.Z rs.tc →
  (st.msg.Type' = MsgTimeoutNow → max (uint.Z rs.term) (uint.Z st.msg.Term') + 1 ≤ uint.Z rs.tc) →
  rs.flw = false →
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip ∗
      "Hm" ∷ (∃ c : MsgC, msgPtsCC ml (DFrac.own 1) DFrac.discard (needsCap st.msg) c ∗
        ⌜c.model = st ∧ c.csUfNil ∧
          (∀ b, γ.maxData = some b → st.msg.Type' ≠ MsgSnap → msgSizeOk c)⌝) ∗
      "#Hxfer" ∷ □ (⌜st.msg.Type' = MsgTransferLeader ∧ st.msg.Term' ≠ W64 0⌝ -∗
        isLeader γ id st.msg.Term') ∗
      "#Hmsg" ∷ □ (∀ ty, ⌜mtypeOf st.msg.Type' = some ty⌝ -∗ ⌜ty ≠ .snap⌝ -∗
        isMessage γ (absMsg ty st.msg st.ents st.ctx)) ∗
      "#Hsnap" ∷ □ (⌜st.msg.Type' = MsgSnap⌝ -∗
         ∃ (sv : SnapshotM) (scfg : CSLists),
           ⌜st.snap = some sv ∧ scfg = sv.Metadata'.ConfState'.lists ∧
             uint.Z sv.Metadata'.Index' < 2^61 ∧
             γ.reNoSnap = false⌝ ∗
           isMessageC γ (absSnap st.msg sv scfg) ∗
           snapDataOk γ sv.Metadata'.Index' sv.Data' ∗
           snapLocal γ id sv.Metadata'.Index') ∗
      "Hcred" ∷ rdCred γ (if st.msg.Type' = MsgReadIndex then 1 else 0) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Step")) (Val #ml))
  {{ (err : GoInterface) (t : w64) (r' : RState) (ip' : Nat), RET #err;
      "Hrn" ∷ R γ rn id
        { rs with term := t, psnap := rs.psnap || decide (st.msg.Type' = MsgSnap) } r' qs ip' ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.tc ∧
               (st.msg.Type' ≠ MsgPreVoteResp →
                 uint.Z t ≤ max (uint.Z rs.term) (uint.Z st.msg.Term') +
                   (if st.msg.Type' = MsgTimeoutNow then 1 else 0))⌝ ∗
      -- (#33 S3c) the exact effect (`Protocol/InputEnd.lean`): at the message's protocol reading
      -- `RecvEndR`; (antithesis parity B1) at its transfer reading (`xmsgOf`: no protocol reading) the
      -- Sim's `InputStep .recvX` (`TimeoutNowEndR` or `TransferRecvEndR`); (antithesis parity B1,
      -- lead-approved) or, a response from a sender with no `Progress` (`errStepPeer`, at non-voters
      -- on), unchanged: taken only for response types, so not for a `MsgProp` and the error unread
      "%Hend" ∷ ⌜∀ md, S md → (r' = r ∧ ip' = ip) ∨
        ((∀ ty, mtypeOf st.msg.Type' = some ty → ∀ Adm,
          RecvEndR Adm rs.k id r (absMsg ty st.msg st.ents st.ctx) r') ∧
        (∀ x, xmsgOf st = some x → (x.ty = .timeoutNow ∧ TimeoutNowEndR id r x r') ∨
          (x.ty = .transferLeader ∧ TransferRecvEndR id r x r')) ∧
        ip' = min ip (lcpLen r.p.log r'.p.log))⌝ }}

/-- **`RawNode.Step`, strengthened** (design §2.2's table), at every scope `sc` (antithesis parity B1,
step C1: at a mode without snapshots, configuration changes, forwarding or asynchronous storage, the
features B1 does not turn on; `none` the old spec's content). -/
abbrev RawNode.Step.absSpec : Prop :=
  ∀ sc : Option RnMode, (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧
      md.forwarding = false ∧ md.async = false) →
    RawNode.Step.form
      (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc)
      (fun md => sc = some md)

/-- The old spec, its text unchanged, from the strengthened one (`ownRawNode_at` in at `sc = false`,
`ownRawNodeAt_ownRawNode` out). -/
abbrev RawNode.Step.spec_of_abs.law : Prop :=
  RawNode.Step.absSpec (GF := GF) (hG := hG) → RawNode.Step.spec (GF := GF) (hG := hG)

/-! ### `RawNode.Tick` -/

/-- `RawNode.Tick.spec`'s triple over `R`, and (under `S`) the tick's exact effect `TickEnd`. -/
abbrev RawNode.Tick.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat),
  uint.Z rs.term + 1 ≤ uint.Z rs.tc →
  rs.flw = false →
  (γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Tick")) (Val #()))
  {{ (t : w64) (r' : RState) (ip' : Nat), RET #();
      "Hrn" ∷ R γ rn id { rs with term := t } r' qs ip' ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ ∗
      -- (the scope's exact effect at an untraced node only: the traced tick carries no `StepEnd`;
      -- the harness's cluster is untraced, `NewRawNode.emptyStartForm`)
      "%Hend" ∷ ⌜∀ md, S md → γ.reTrace = none → TickEndR rs.k id r r' ∧
        ip' = min ip (lcpLen r.p.log r'.p.log)⌝ }}

/-- **`RawNode.Tick`, strengthened**. -/
abbrev RawNode.Tick.absSpec : Prop :=
  ∀ sc : Option RnMode, (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧
      md.forwarding = false ∧ md.async = false) →
    RawNode.Tick.form
      (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc)
      (fun md => sc = some md)

abbrev RawNode.Tick.spec_of_abs.law : Prop :=
  RawNode.Tick.absSpec (GF := GF) (hG := hG) → RawNode.Tick.spec (GF := GF) (hG := hG)

/-! ### `RawNode.Campaign` -/

/-- (antithesis parity B1, phase 2; design §4) `RawNode.Campaign.spec`'s triple over `R`, and (under `S`) the
campaign's exact effect `CampaignEndR` (`hup`'s guards, then nothing or an election; the node's log kept, so
the in-progress boundary too). (No `spec_of_abs`: the old spec keeps its own proof.) -/
abbrev RawNode.Campaign.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat),
  uint.Z rs.term + 1 ≤ uint.Z rs.tc →
  rs.flw = false →
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Campaign")) (Val #()))
  {{ (err : GoInterface) (t : w64) (r' : RState) (ip' : Nat), RET #err;
      "Hrn" ∷ R γ rn id { rs with term := t } r' qs ip' ∗
      "%Ht" ∷ ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ ∗
      "%Herr" ∷ ⌜err = interface.nil⌝ ∗
      "%Hend" ∷ ⌜∀ md, S md → CampaignEndR rs.k id r r' ∧ ip' = min ip (lcpLen r.p.log r'.p.log)⌝ }}

/-- **`RawNode.Campaign`, strengthened**. -/
abbrev RawNode.Campaign.absSpec : Prop :=
  ∀ sc : Option RnMode, (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧
      md.forwarding = false ∧ md.async = false) →
    RawNode.Campaign.form
      (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc)
      (fun md => sc = some md)

/-! ### `RawNode.Propose` -/

/-- `RawNode.Propose.spec`'s triple over `R`, and (under `S`) the proposal's exact effect
`ProposeEnd`, at the message `Propose` steps (`pb.Message{Type: MsgProp, From: r.id, Entries:
[{Data: data}]}`); a dropped proposal (`ErrProposalDropped`) is `ProposeEnd`'s `ps' = ps` arm. -/
abbrev RawNode.Propose.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (data_sl : GoSlice) (data : List w8),
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip ∗
      "#Hdata" ∷ data_sl ↦*□ data ∗
      "%Hmd" ∷ ⌜∀ b, γ.maxData = some b → data.length ≤ b⌝ ∗
      "#Hent" ∷ propData γ (propEntryM data) ∗
      "Htk" ∷ entTk γ (propEntryM data) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Propose")) (Val #data_sl))
  {{ (err : GoInterface) (r' : RState) (ip' : Nat), RET #err;
      "Hrn" ∷ R γ rn id rs r' qs ip' ∗
      "Herr" ∷ (⌜err = interface.nil⌝ ∨ globalAddr ErrProposalDropped ↦□ err) ∗
      "%Hend" ∷ ⌜∀ md, S md → (∀ Adm, RecvEndR Adm rs.k id r
        (absMsg .propose { propMsgM with From' := id } [propEntryM data]) r') ∧
        ip' = min ip (lcpLen r.p.log r'.p.log)⌝ }}

/-- **`RawNode.Propose`, strengthened**. -/
abbrev RawNode.Propose.absSpec : Prop :=
  ∀ sc : Option RnMode, (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧
      md.forwarding = false ∧ md.async = false) →
    RawNode.Propose.form
      (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc)
      (fun md => sc = some md)

abbrev RawNode.Propose.spec_of_abs.law : Prop :=
  RawNode.Propose.absSpec (GF := GF) (hG := hG) → RawNode.Propose.spec (GF := GF) (hG := hG)

/-! ### `RawNode.TransferLeader` -/

/-- (antithesis parity B1, Q3; design §4) `RawNode.TransferLeader.spec`'s triple over `R`, and (under
`S`) the transfer's exact effect `TransferEndR` at the target `to`, the log kept. Only in a scope
with transfer on (stepping the request sets `NGhost.xs`, which `RnScope` keeps `false` without it).
A leader ignores a target outside its progress map (`stepLeader`'s `pr == nil`), `TransferEndR`'s
`r'.p = r.p` arm. (antithesis parity B1, transfer source, lead-approved 11-27) Under `S`, the target one
the cluster's acknowledgement map names (the driver draws a server of the run): a follower forwards
the request with it as sender (`XScopeOk`'s sender clause, what a `Ready` reads of a forward). -/
abbrev RawNode.TransferLeader.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (to : w64),
  (∀ md, S md → md.transfer = true) →
  (∀ md, S md → (γ.reAcks !! to).isSome) →
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"TransferLeader")) (Val #to))
  {{ (r' : RState), RET #();
      "Hrn" ∷ R γ rn id rs r' qs ip ∗
      "%Hend" ∷ ⌜∀ md, S md → TransferEndR id r to r'⌝ }}

/-- **`RawNode.TransferLeader`, strengthened**, in the harness's scope at a mode with transfer (the
form's premise), without snapshots or configuration changes (`raft.Step.untracedNs`, `AckScope`). -/
abbrev RawNode.TransferLeader.absSpec : Prop :=
  ∀ md : RnMode, md.snapshots = false → md.confChanges = false → RawNode.TransferLeader.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (some md)) (fun md' => md' = md)

/-! ### `RawNode.ReportUnreachable` -/

/-- (antithesis parity B1, phase 2; design §4) `RawNode.ReportUnreachable.spec`'s triple over `R`, the
node's state unchanged (`MsgUnreachable`, local: a leader's `pr.BecomeProbe()`, which keeps the
peer's `Match`; nothing elsewhere), so the client's record, the `RState`, the queue and the
in-progress boundary too. (No `spec_of_abs`: the old spec keeps its own proof.) -/
abbrev RawNode.ReportUnreachable.form
    (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (to : w64),
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReportUnreachable")) (Val #to))
  {{ RET #(); "Hrn" ∷ R γ rn id rs r qs ip }}

/-- **`RawNode.ReportUnreachable`, strengthened**, in the harness's scope at a mode without snapshots
or configuration changes (B1's: the step's end state, `raft.Step.untracedNs`, needs the log never
compacted and no automatic leave). -/
abbrev RawNode.ReportUnreachable.absSpec : Prop :=
  ∀ md : RnMode, md.snapshots = false → md.confChanges = false → RawNode.ReportUnreachable.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (some md))

/-! ### `RawNode.ReadIndex` -/

/-- (antithesis parity B1, phase 2; design §4) `RawNode.ReadIndex.spec`'s triple over `R` (the deposit:
the request's `readReq` at a committed log past `L0`, and `isRead`), the client's record kept (the
message's term is `0`), and (under `S`, with reads on) the request's exact effect `RecvEndR` at
`readMsg rctx` (local, `From` unset); the log kept, so the in-progress boundary too. -/
abbrev RawNode.ReadIndex.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (rctx : GoSlice) (c : List w8) (Qr : List EntryM → IProp GF) (L0 : List EntryM),
  (∀ md, S md → md.reads = true) →
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip ∗
      "#Hctx" ∷ rctx ↦*□ c ∗
      "%Hmd" ∷ ⌜∀ b, γ.maxData = some b → c.length ≤ b⌝ ∗
      "Hfr" ∷ rdFresh γ c ∗
      "#Hau" ∷ readAu γ Qr ∗
      "#HL0" ∷ isCommitted γ L0 ∗
      "Hcred" ∷ rdCred γ 1 }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"ReadIndex")) (Val #rctx))
  {{ (r' : RState), RET #();
      "Hrn" ∷ R γ rn id rs r' qs ip ∗
      "#Hrq" ∷ (∃ Lc, ⌜L0 <+: Lc⌝ ∗ readReq γ c Lc ∗ isRead γ c Qr) ∗
      "%Hend" ∷ ⌜∀ md, S md → ∀ Adm, RecvEndR Adm rs.k id r (readMsg c) r'⌝ }}

/-- **`RawNode.ReadIndex`, strengthened**, in the harness's scope at a mode with reads, without
snapshots or configuration changes (`raft.Step.untracedNs`, `AckScope`). -/
abbrev RawNode.ReadIndex.absSpec : Prop :=
  ∀ md : RnMode, md.snapshots = false → md.confChanges = false → RawNode.ReadIndex.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (some md)) (fun md' => md' = md)

/-! ### `RawNode.HasReady` -/

/-- **`RawNode.HasReady`, strengthened** (design §2.2, revision 2's T3): read-only; on `false`, in
the scope, the protocol-level idle fact `PIdle` and the in-progress boundary at the log's end
(`hasNextUnstableEnts` false), (antithesis parity B1) no read state (Go's `HasReady` is true on any),
and both views of the node: the old spec's
`ownRawNodeIdle` and `ownRawNodeAt` (an Iris conjunction: either, of the same resources). -/
abbrev RawNode.HasReady.absSpec : Prop :=
  ∀ (sc : Option RnMode), (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧
      md.forwarding = false ∧ md.async = false) →
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg)
    (ip : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNodeAt γ rn id rs r qs ip sc }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"HasReady")) (Val #()))
  {{ (b : Bool), RET #b;
      (⌜b = true⌝ ∗ ownRawNodeAt γ rn id rs r qs ip sc) ∨
      (⌜b = false⌝ ∗
        ⌜(∀ md, sc = some md → PIdle rs r.p ∧ ip = r.p.log.length) ∧ r.p.rd.states = []⌝ ∗
        (ownRawNodeIdle γ rn id rs ∧ ownRawNodeAt γ rn id rs r qs ip sc)) }}

abbrev RawNode.HasReady.spec_of_abs.law : Prop :=
  RawNode.HasReady.absSpec (GF := GF) (hG := hG) → RawNode.HasReady.spec (GF := GF) (hG := hG)

/-! ### `RawNode.Ready` -/

/-- `RawNode.Ready.spec`'s triple over `R`: the node after at `r'` (`rAccepted r` under `S`), its queue `qs'`, its
in-progress boundary `ip'`; and (under `S`) the queue the outbox's self-addressed messages, the
`Ready`'s fields `ReadyOut`, the first entry at the boundary `ip + 1` and the boundary moved to the
log's end; (antithesis parity B1) a reported pre-candidate's pre-vote flag on, the read states handed out
the node's. -/
abbrev RawNode.Ready.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (x : CrashNames) (rs : RNState) (r : RState)
    (qs : List Msg) (ip : Nat) (q : Qp) (g : Nat),
  rs.steps = [] →
  rs.unpersisted = [] →
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip ∗
      "Hlive" ∷ genView γ id x q g ∗ "Hfree" ∷ slotFree γ id g }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Ready")) (Val #()))
  {{ (rd : Ready) (ce es : List EntryM) (ms : List QMsg)
      (sts : List ReadStateM) (h : HardStateM) (steps : List Pending) (L : Option SnapLoan)
      (ss : Option (w64 × StateType)) (W : DurMaps) (r' : RState) (qs' : List Msg) (ip' : Nat), RET #rd;
      "Hrn" ∷ R γ rn id
        { rs with delivered := rs.delivered ++ ce, unpersisted := es, steps := steps,
                  outlb := 0, unst := false, phs := phsNext rs.phs h, psnap := false,
                  slent := L, dur := readyDurable rs.dur (phsNext rs.phs h) L es,
                  role := roleAfter rs.role ss, bw := W } r' qs' ip' ∗
      "Hlive" ∷ genView γ id x q g ∗
      "Henter" ∷ (∀ (E : CoPset) (q' : Qp), ⌜↑(raftN γ) ⊆ E⌝ -∗ notCrashed -∗
        ownDurGhost γ id rs.dur ∗ genView γ id x q' g ={E}=∗
          notCrashed ∗ ownDurGhost γ id (readyDurable rs.dur (phsNext rs.phs h) L es) ∗
          genView γ id x q' g ∗
          slotFree γ id g ∗ durFrags γ id W ∗ [∗list] q ∈ ms, isRaftMsg γ id q.st) ∗
      "#Hlead" ∷ (⌜roleAfter rs.role ss = StateLeader⌝ -∗ [∗list] q ∈ ms, isRaftMsg γ id q.st) ∗
      "#Hsnapto" ∷ ([∗list] q ∈ ms, snapToOk γ id q.st) ∗
      "#Hsrcs" ∷ readyMsgOrigins γ id rs.sn ms ∗
      "#Hss" ∷ softStateIs rd.SoftState' ss ∗
      "#Hce" ∷ entsRO rd.CommittedEntries' ce ∗
      "#Hcommitted" ∷ isCommitted γ (rs.delivered ++ ce) ∗
      "#Hents" ∷ entsROz γ.maxData.isSome rd.Entries' es ∗
      "Hmsgs" ∷ rd.Messages' ↦* ms.map QMsg.loc ∗
      "Hmsgs_cap" ∷ ownSliceCap Loc rd.Messages' (DFrac.own 1) ∗
      "Hmsgs_own" ∷ ([∗list] q ∈ ms, msgOwnZ γ.maxData.isSome q.loc (readyDq q.st) q.st) ∗
      "Hmsgs_cred" ∷ ([∗list] q ∈ ms,
        rdCred γ (if q.st.msg.Type' = MsgReadIndex then 1 else 0)) ∗
      "%Hmsgs_term" ∷ ⌜∀ q ∈ ms, uint.Z q.st.msg.Term' ≤ uint.Z rs.tc⌝ ∗
      "Hsnapz" ∷ rdSnapOut γ rs rd ce es L ∗
      "%Hpsn" ∷ ⌜rs.psnap = false → L = none⌝ ∗
      "#Hrs" ∷ readStatesPts rd.ReadStates' sts ∗
      "#Hrs_ok" ∷ ([∗list] st ∈ sts, readStateRaw γ st) ∗
      "#Hhard" ∷ hsOptC rd.HardState' h ∗
      "#Hhsw" ∷ hsWit γ (phsNext rs.phs h) (dlvAfter rs.delivered ce L).length ∗
      "Happ" ∷ readyOut rs.storage rs.sn es L ∗
      "#Hfrz" ∷ (⌜L ≠ none⌝ ∨ ceFrozen rs.storage rs.delivered.length ce es) ∗
      "#Hdk" ∷ dlvKeysAt rs.sn rs.delivered.length
        ((dlvAfter rs.delivered ce L).drop rs.delivered.length) ∗
      -- (#33 S3c) the queue `Advance` steps, and the `Ready` against the protocol state
      -- (antithesis parity B1) the node after at `rAccepted r` (in the scope: outside it the ghost prefix
      -- below the log's boundary is not pinned across the call)
      "%Hout" ∷ ⌜∀ md, S md → r' = rAccepted r ∧ qs' ≡ₚ r.p.outbox.filter (fun m => decide (m.dst = id)) ∧
        ReadyOut id rs r.p h es ce ms ss L ∧
        -- (decision 3) the entries from the in-progress boundary on; the boundary to the end
        (∀ e0 ∈ es.head?, uint.nat e0.Index' = ip + 1) ∧ ip' = r.p.log.length ∧
        -- (#33 S4, 2026-11-24) a non-empty hard state differs from the last one handed out
        -- (`rd.HardState` is set only when `!isHardStateEqual(hardSt, prevHardSt)`; ledger)
        (¬ (h.Term' = W64 0 ∧ h.Vote' = W64 0 ∧ h.Commit' = W64 0) → h ≠ rs.phs) ∧
        -- (#33 S4, 2026-11-24) every message handed out reads as a protocol message or (antithesis
        -- parity B1, Q3) as a transfer message (`xmsgOf`), each of those against the node (`XReadyOk`)
        (∀ q ∈ ms, (absMsgOf q.st).isSome ∨ (xmsgOf q.st).isSome) ∧
        (∀ q ∈ ms, ∀ x, xmsgOf q.st = some x → XReadyOk γ md id r.p x) ∧
        -- (antithesis parity B1, the drain's send side) at transfer off, every one a protocol message
        (md.transfer = false → ∀ q ∈ ms, (absMsgOf q.st).isSome) ∧
        -- (antithesis parity B1, the drain's send side) a transfer message's other numbers zero, no
        -- rejection (`SentMsgShape`'s)
        (∀ q ∈ ms, ∀ x, xmsgOf q.st = some x →
          q.st.msg.Index' = W64 0 ∧ q.st.msg.LogTerm' = W64 0 ∧ q.st.msg.Commit' = W64 0 ∧
            q.st.msg.Reject' = false) ∧
        -- (antithesis parity B1, group E's S4) the role reported a pre-candidate only with the node
        -- constant's pre-vote on, and the read states handed out the node's
        (roleAfter rs.role ss = StatePreCandidate → rs.k.prevote = true) ∧ sts = r.p.rd.states⌝ }}

/-- **`RawNode.Ready`, strengthened**. -/
abbrev RawNode.Ready.absSpec : Prop :=
  ∀ sc : Option RnMode, (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧
      md.forwarding = false ∧ md.async = false) →
    RawNode.Ready.form
      (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc)
      (fun md => sc = some md)

abbrev RawNode.Ready.spec_of_abs.law : Prop :=
  RawNode.Ready.absSpec (GF := GF) (hG := hG) → RawNode.Ready.spec (GF := GF) (hG := hG)

/-! ### `RawNode.Advance` -/

/-- `RawNode.Advance.spec`'s triple over `R`: the queue empty after; and (under `S`) the queued
messages `qs` stepped in order and the acknowledgements' `applied` (`AdvanceEndR`). -/
abbrev RawNode.Advance.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (rd : Ready),
  (rs.slent = none → rs.unpersisted = []) →
  rs.unst = false →
  (γ.reTrace ≠ none → uint.Z rs.tc + 1 < traceNumBound ∧ traceReadyFits GF γ ∧ rs.slent = none) →
  -- (#33 S4, 2026-11-24) in the scope, no queued pre-vote response: a self `MsgPreVoteResp` of the
  -- next term has no `RecvEnd` (ledger); the harness's queue is `QsOk`'s. (antithesis parity B1, step
  -- C3; design §2 table) only at pre-vote off
  (∀ md, S md → md.prevote = false → ∀ q ∈ qs, q.ty ≠ .preVoteResp) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip ∗
      "Hret" ∷ loanRet rs ∗
      "#HA1" ∷ □ (⌜rs.slent = none⌝ -∗
        cfgKeepIn γ rs.mode rs.delivered rs.capplied rs.delivered.length rs.cfg) ∗
      "#Hbw" ∷ durFrags γ id rs.bw }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"Advance")) (Val #rd))
  {{ (t : w64) (ca : Nat) (r' : RState) (ip' : Nat), RET #();
      R γ rn id (advRS rs t ca) r' [] ip' ∗
      ⌜uint.Z rs.term ≤ uint.Z t ∧ uint.Z t ≤ uint.Z rs.term + 1⌝ ∗
      ⌜uint.Z t ≤ uint.Z rs.tc⌝ ∗
      ⌜(rs.slent = none → rs.capplied ≤ ca ∧ ca ≤ max rs.capplied rs.delivered.length) ∧
        (∀ l, rs.slent = some l → rs.mode.isDyn = true → ca = l.dlv.length) ∧
        (rs.mode = .static → ca = rs.capplied)⌝ ∗
      ⌜rs.slent = none → rs.mode.isDyn = true → ca = max rs.capplied rs.delivered.length⌝ ∗
      -- (#33 S3c) the exact effect
      -- (#33 S4, 2026-11-24) the boundary's fact at a boundary at the log's end (the harness's, after a
      -- `Ready`): in general an acknowledgement can raise it past `min ip lcp` (ledger)
      -- (antithesis parity B1 stage 3b) `AdvanceEndR`: the queue stepped in order, then the storage
      -- acknowledgements' `applied` (`AckEndR`'s second arm, `StepR.advance`), whose premise is the
      -- caller's: the configuration kept over the entries applied (2026-11-27, option D's `CfgKeep`: until
      -- then no undecided conf entry there, `NoUndecConfIn`); (antithesis parity B1, item 2b) at
      -- a mode without snapshots, `AdvanceEndRNoSnap` (no snapshot applied: the Sim's `AdvanceNoSnap`),
      -- and the premise over the inputs: the committed log handed out, `delivered`, in `r`'s full log
      -- (`applied` reaches its end; `Advance` keeps that prefix)
      ⌜∀ md, S md → γ.reTrace = none →
        (∀ (Adm : List EntryM → CCState → Prop) (dec : CCDec),
          CfgKeep dec r.full r.cidx rs.delivered.length r.cfg →
            AdvanceEndR Adm dec rs.k id r qs r' ∧
            (md.snapshots = false → AdvanceEndRNoSnap Adm dec rs.k id r qs r')) ∧
        (ip = r.p.log.length → ip' = min ip (lcpLen r.p.log r'.p.log))⌝ }}

/-- **`RawNode.Advance`, strengthened**. -/
abbrev RawNode.Advance.absSpec : Prop :=
  ∀ sc : Option RnMode, (∀ md, sc = some md → md.snapshots = false ∧ md.confChanges = false ∧
      md.forwarding = false ∧ md.async = false) →
    RawNode.Advance.form
      (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc)
      (fun md => sc = some md)

abbrev RawNode.Advance.spec_of_abs.law : Prop :=
  RawNode.Advance.absSpec (GF := GF) (hG := hG) → RawNode.Advance.spec (GF := GF) (hG := hG)

/-! ### `NewRawNode` at an empty storage -/

/-- `NewRawNode.emptyStartSpec`'s triple, the post's node over `R` at `rInit` (the initial protocol
state `pInit`; antithesis parity B1: with the node constant the `Config`'s flags, `cfgK cv`) with nothing queued,
with the harness's scope as premises: pre-vote and check-quorum off (F6), the names' voters the
cluster's (`vs`) with the node among them, and the storage never compacted past `0` (`storCapF`: the harness never calls `Compact`; the
storage's contract states it). -/
abbrev NewRawNode.emptyStartForm (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF) :
    Prop :=
  ∀ (γ : Cluster) (N : Namespace) (c : Loc) (cv : Config) (lok si : GoInterfaceOk) (vs : List w64)
    (F : GName → IProp GF),
  ∀ (SV : SnapshotM → IProp GF) [∀ sv, Persistent (SV sv)],
  (∀ sv, SV sv ⊢ snapshotValid γ sv) →
  ConfigValid cv →
  cv.Logger' = interface.ok lok →
  cv.Storage' = interface.ok si →
  sint.Z cv.MaxInflightMsgs' < 2 ^ 62 →
  cv.DisableProposalForwarding' = false →
  cv.ReadOnlyOption' = W64 0 →
  cv.DisableConfChangeValidation' = false →
  (cv.MaxCommittedSizePerReady' ≠ W64 0 ∨ cv.MaxSizePerMsg' ≠ W64 0) →
  cv.AsyncStorageWrites' = false →
  (γ.maxData ≠ none → uint.Z cv.MaxSizePerMsg' ≤ entsCutMax) →
  cv.Applied' = W64 0 →
  γ.bootLen = 0 →
  vs.Nodup →
  ¬ clusterNoSnap γ →
  TraceLoggerOk cv.TraceLogger' →
  Cluster.trace γ = none →
  -- (#33 S3c, F6) pre-vote and check-quorum off; (2026-11-24) the names' voters the cluster's, the
  -- node one of them (until then the static mode, `γ.rnMode = .static`, which `isCluster`
  -- contradicts: its nodes are in the dynamic mode, `InvApi.lean`'s `ModeDec`)
  cv.PreVote' = false ∧ cv.CheckQuorum' = false →
  γ.raftNames.reCfg = GMap.listToSet vs ∧ cv.ID' ∈ vs →
  ∀ (x : CrashNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ c ↦ cv ∗ isLogger lok ∗
      isCluster γ N ∗ nodeVacantA γ cv.ID' x ∗ readyFits γ N ∗
      raftState γ cv.ID' RaftState.init ∗
      confAt γ 0 (Membership.simple (GMap.listToSet vs)) ∗
      restartStorage γ (interface.ok si) emptyStorContents (votersConfState vs) 0 F SV ∗
      -- (#33 S3c, §2.5) the storage never compacted past `0`
      storCapF (interface.ok si) 0 }}
    (App (Val #(functions NewRawNode [])) (Val #c))
  {{ (rn : Loc) (err : GoInterface), RET (PairV #rn #err);
      ⌜err = interface.nil⌝ ∗
      ∃ (sn : StorNames) (g : Nat) (K : GName),
        R γ.raftNames rn cv.ID' { rawNodeRestarted γ [] (interface.ok si) sn hsZero RaftState.init
          (Membership.simple (GMap.listToSet vs)) 0 with k := cfgK cv }
          (rInit (ApiImpl.stOf (Membership.simple (GMap.listToSet vs)))) [] 0 ∗
        genView γ.raftNames cv.ID' x 1 g ∗ slotFree γ.raftNames cv.ID' g ∗
        raftState γ cv.ID' RaftState.init ∗ F K }}

/-- **`NewRawNode` at an empty storage, in the harness's scope** (design §2.2's last row): the node
in the scope (`sc = true`) at the initial protocol state. (No `spec_of_abs`: its premises are
stronger than `emptyStartSpec`'s, which keeps its own proof.) -/
abbrev NewRawNode.emptyStartAbsSpec : Prop :=
  NewRawNode.emptyStartForm (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (some {}))

end spec

end EtcdGrove
end Perennial
