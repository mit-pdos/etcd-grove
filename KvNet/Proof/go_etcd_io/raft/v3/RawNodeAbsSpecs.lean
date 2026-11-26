-- The copy for the part `KvNet/` of `RaftNoAx/Proof/go_etcd_io/raft/v3/RawNodeAbsSpecs.lean` (etc/copy-part.py; rerun it, do not edit).
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
the scope only for the harness's network types (`antStepTypes`; the old premises otherwise), a
heartbeat response with no context, a sender among the voters (`errStepPeer`);
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

public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeAt
public import KvNet.Proof.go_etcd_io.raft.v3.Protocol.InputEnd
public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__Step
public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__Tick
public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__Campaign
public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__Propose
public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__HasReady
public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__Ready
public import KvNet.Spec.go_etcd_io.raft.v3.RawNode__Advance
public import KvNet.Proof.go_etcd_io.raft.v3.RawNodeStartSpec

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
reported soft state's (Go compares `softState()` with `prevSoftSt`); the log the durable state the
client entered (nothing unpersisted: `hasNextUnstableEnts` false). -/
def PIdle (rs : RNState) (ps : PState) : Prop :=
  ps.outbox = [] ∧ HardStateM.mk ps.term ps.vote ps.commit = rs.phs ∧ roleGo ps.role = rs.role ∧
  rs.dur.ents = ps.log

/-- **A `Ready`'s fields against the node's protocol state at the call** (design §2.2, "The `Ready`
binding"): the role it reports is the node's (`roleAfter`, `softStateIs`); the hard state after it is
the node's term, vote and commit (`phsNext`); the durable state the write makes has the node's log,
the entries `es` the log's suffix from `es[0].Index`; the messages' protocol readings are the outbox's but
those to the node itself (which go to `stepsOnAdvance`), each message to another node; the committed entries are
the log's after those delivered, up to at most the commit index; no snapshot (`L = none`). -/
def ReadyOut (id : w64) (rs : RNState) (ps : PState) (h : HardStateM)
    (es ce : List EntryM) (ms : List QMsg) (ss : Option (w64 × StateType)) (L : Option SnapLoan) :
    Prop :=
  roleAfter rs.role ss = roleGo ps.role ∧
  phsNext rs.phs h = HardStateM.mk ps.term ps.vote ps.commit ∧
  (readyDurable rs.dur (phsNext rs.phs h) L es).ents = ps.log ∧
  (∀ e0 ∈ es.head?, ps.log.drop (uint.nat e0.Index' - 1) = es) ∧
  ms.filterMap (fun q => absMsgOf q.st) ≡ₚ ps.outbox.filter (fun m => decide (m.dst ≠ id)) ∧
  (∀ q ∈ ms, q.st.msg.To' ≠ id) ∧
  rs.delivered ++ ce <+: ps.log ∧ (rs.delivered ++ ce).length ≤ uint.nat ps.commit ∧
  L = none

/-- (antithesis parity B1, Q3) **A `Ready`'s untyped message against the node's protocol state** at
the call (`p`): a `MsgTimeoutNow` from the node at a term past `0`; a `MsgTimeoutNow` or a stamped
`MsgTransferLeader` to another node, of a term at most the node's (`XQOk`); a stamped forward to a
member of the configuration (its destination the node's leader when it forwarded, `XScopeOk`). No
destination fact for a `MsgTimeoutNow` (the driver routes by destination, dropping one to a
non-server; the lead's decision, Q3 option 1). -/
def XReadyOk (γ : RaftNames) (id : w64) (p : PState) (x : XMsg) : Prop :=
  (x.ty = .timeoutNow → x.src = id ∧ x.term ≠ W64 0) ∧
  (x.ty = .timeoutNow ∨ x.term ≠ W64 0 → x.dst ≠ id ∧ uint.Z x.term ≤ uint.Z p.term) ∧
  (x.ty = .transferLeader → x.term ≠ W64 0 → x.dst ∈ γ.reCfg)

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
  -- (#33 S3c) in the scope, a message of the harness's network, a heartbeat response with no
  -- read-index context (`recvEnd_of_stepEnd_heartbeatResp`'s premise), from a voter (2026-11-24: a
  -- response from a sender outside the progress map returns `errStepPeer` with the state unchanged,
  -- not `RecvEnd`'s step-down to a higher term; notes/specs-only/ledger.md)
  (∀ md, S md → st.msg.Type' ∈ antStepTypes ∧ (st.msg.Type' = MsgHeartbeatResp → st.ctx = []) ∧
    st.msg.From' ∈ γ.reCfg) →
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
      -- (#33 S3c) the exact effect (`Protocol/InputEnd.lean`)
      "%Hend" ∷ ⌜∀ md, S md → (∀ ty, mtypeOf st.msg.Type' = some ty → ∀ Adm,
        RecvEndR Adm rs.k id r (absMsg ty st.msg st.ents st.ctx) r') ∧
        ip' = min ip (lcpLen r.p.log r'.p.log)⌝ }}

/-- **`RawNode.Step`, strengthened** (design §2.2's table). -/
abbrev RawNode.Step.absSpec : Prop :=
  ∀ sc : Bool, RawNode.Step.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (basicScope sc))
    (fun md => basicScope sc = some md)

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
  ∀ sc : Bool, RawNode.Tick.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (basicScope sc))
    (fun md => basicScope sc = some md)

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
  ∀ sc : Bool, RawNode.Campaign.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (basicScope sc))
    (fun md => basicScope sc = some md)

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
  ∀ sc : Bool, RawNode.Propose.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (basicScope sc)) (fun md => basicScope sc = some md)

abbrev RawNode.Propose.spec_of_abs.law : Prop :=
  RawNode.Propose.absSpec (GF := GF) (hG := hG) → RawNode.Propose.spec (GF := GF) (hG := hG)

/-! ### `RawNode.TransferLeader` -/

/-- (antithesis parity B1, Q3; design §4) `RawNode.TransferLeader.spec`'s triple over `R`, and (under
`S`) the transfer's exact effect `TransferEndR` at the target `to`, the log kept. Only in a scope
with transfer on (stepping the request sets `NGhost.xs`, which `RnScope` keeps `false` without it).
No premise on `to`: the driver draws any server of the run; a leader ignores a target outside its
progress map (`stepLeader`'s `pr == nil`), `TransferEndR`'s `r'.p = r.p` arm. -/
abbrev RawNode.TransferLeader.form (R : RaftNames → Loc → w64 → RNState → RState → List Msg → Nat → IProp GF)
    (S : RnMode → Prop) : Prop :=
  ∀ (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg) (ip : Nat)
    (to : w64),
  (∀ md, S md → md.transfer = true) →
  γ.reTrace = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"TransferLeader")) (Val #to))
  {{ (r' : RState), RET #();
      "Hrn" ∷ R γ rn id rs r' qs ip ∗
      "%Hend" ∷ ⌜∀ md, S md → TransferEndR id r to r'⌝ }}

/-- **`RawNode.TransferLeader`, strengthened**, at every scope (transfer exists only past the basic
scope). -/
abbrev RawNode.TransferLeader.absSpec : Prop :=
  ∀ sc : Option RnMode, RawNode.TransferLeader.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip sc) (fun md => sc = some md)

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

/-! ### `RawNode.HasReady` -/

/-- **`RawNode.HasReady`, strengthened** (design §2.2, revision 2's T3): read-only; on `false`, in
the scope, the protocol-level idle fact `PIdle` and the in-progress boundary at the log's end
(`hasNextUnstableEnts` false), and both views of the node: the old spec's
`ownRawNodeIdle` and `ownRawNodeAt` (an Iris conjunction: either, of the same resources). -/
abbrev RawNode.HasReady.absSpec : Prop :=
  ∀ (sc : Bool) (γ : RaftNames) (rn : Loc) (id : w64) (rs : RNState) (r : RState) (qs : List Msg)
    (ip : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ ownRawNodeAt γ rn id rs r qs ip (basicScope sc) }}
    (App (Val (rn @!! go.GoType.PointerType RawNode.ty @!! go!"HasReady")) (Val #()))
  {{ (b : Bool), RET #b;
      (⌜b = true⌝ ∗ ownRawNodeAt γ rn id rs r qs ip (basicScope sc)) ∨
      (⌜b = false⌝ ∗ ⌜sc = true → PIdle rs r.p ∧ ip = r.p.log.length⌝ ∗
        (ownRawNodeIdle γ rn id rs ∧ ownRawNodeAt γ rn id rs r qs ip (basicScope sc))) }}

abbrev RawNode.HasReady.spec_of_abs.law : Prop :=
  RawNode.HasReady.absSpec (GF := GF) (hG := hG) → RawNode.HasReady.spec (GF := GF) (hG := hG)

/-! ### `RawNode.Ready` -/

/-- `RawNode.Ready.spec`'s triple over `R`: the node after at `r'` (`rAccepted r` under `S`), its queue `qs'`, its
in-progress boundary `ip'`; and (under `S`) the queue the outbox's self-addressed messages, the
`Ready`'s fields `ReadyOut`, the first entry at the boundary `ip + 1` and the boundary moved to the
log's end. -/
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
        (∀ q ∈ ms, ∀ x, xmsgOf q.st = some x → XReadyOk γ id r.p x)⌝ }}

/-- **`RawNode.Ready`, strengthened**. -/
abbrev RawNode.Ready.absSpec : Prop :=
  ∀ sc : Bool, RawNode.Ready.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (basicScope sc)) (fun md => basicScope sc = some md)

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
  -- next term has no `RecvEnd` (ledger); the harness's queue is `QsOk`'s
  (∀ md, S md → ∀ q ∈ qs, q.ty ≠ .preVoteResp) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hrn" ∷ R γ rn id rs r qs ip ∗
      "Hret" ∷ loanRet rs ∗
      "#HA1" ∷ □ (⌜rs.slent = none⌝ -∗ undecFree γ rs.mode rs.delivered rs.capplied rs.delivered.length) ∗
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
      -- caller's: no undecided conf entry among the entries applied
      ⌜∀ md, S md → γ.reTrace = none →
        (∀ (Adm : List EntryM → CCState → Prop) (dec : CCDec),
          NoUndecConfIn dec r'.full r.cidx (uint.nat r'.applied) → AdvanceEndR Adm dec rs.k id r qs r') ∧
        (ip = r.p.log.length → ip' = min ip (lcpLen r.p.log r'.p.log))⌝ }}

/-- **`RawNode.Advance`, strengthened**. -/
abbrev RawNode.Advance.absSpec : Prop :=
  ∀ sc : Bool, RawNode.Advance.form
    (fun γ rn id rs r qs ip => ownRawNodeAt (GF := GF) γ rn id rs r qs ip (basicScope sc)) (fun md => basicScope sc = some md)

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
