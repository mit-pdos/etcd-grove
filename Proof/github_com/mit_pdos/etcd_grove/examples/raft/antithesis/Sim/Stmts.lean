/-
Lean-first (no Rocq counterpart).

# The refinement to Antithesis's binding: the per-report statements (#33 S3c step 5 / S4)

One statement per report kind, plus the reportless steps (`quiet`) and `GC`
(`notes/antithesis-parity-design.md` §3.5-§3.6; S4's `notes/antithesis-rawnode-design.md` §3.3):

    SimPre R dec S V net xnet evs G → <raft's facts> → SimStep R dec evs G ev V' net' xnet'

with `ev` the harness's report as a function of the raft data (`Abs.lean`) and `V'`, `net'` as the
report moves them. The `GC` steps the checker takes before each event are inside `Prefix`'s step
(`Checker.next`); `antSim_gc` is the statement each proof uses for them. Raft's facts are pure
relations over `RState`: the per-input end relations (`Protocol/InputEnd.lean`: `RecvEndR`,
`TickEndR`, `CampaignEndR`, `TransferEndR`, `TimeoutNowEndR`, `SnapStatusEndR`, `ApplyConfEndR`,
`StoreAckEndR`, `AdvanceEndR`), the `Ready`'s data as a function of the node's state (`ReadyOutP`,
the protocol reading of `ReadyOut`), and the global facts already in `G` (`ReadyFacts`,
`MsgFacts`). The kinds of parity B2 (async storage, restarts) and B3 (snapshots, conf changes) are
stated here and proved by those batches (the batch kinds `flush`, `net`, `made` over `R.drv`). The S4 harness proof applies them, one per report, inside the recorder's
atomic update (§3.4). Statements only (phase 1 of the spec-first plan): `abbrev <name>.stmt : Prop`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Rel

@[expose] public section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace AntSim

open GMap

section stmts
variable [GooseExts]

open go_etcd_io.raft.v3

/-! ## Raft's side of a report -/

/-- One input of a node's goroutine (`node.go`): a protocol or transfer message (`RawNode.Step`), a
tick, a proposal's data (`Propose`), a conf change's entry (`ProposeConfChange`: the type and the
bytes it marshals; parity B3), a read context (`ReadIndex`), `Campaign`, `TransferLeader(to)`,
`ReportSnapshot` (B3), `ReportUnreachable`, `ApplyConfChange` of the entry at position `k` (B3), a
storage write's or apply's responses stepped back (async, B2). -/
inductive Input where
  | recv (m : Msg)
  | recvX (x : XMsg)
  | tick
  | propose (data : List w8)
  | proposeConf (ty : w32) (data : List w8)
  | readIndex (ctx : List w8)
  | campaign
  | transfer (to : w64)
  | snapStatus (to : w64) (ok : Bool)
  | unreachable (to : w64)
  | applyConf (k : Nat)
  | storeAck (resp : List Msg)

/-- The `by` of the input's drain (`n.input(by, …)`). -/
def Input.byE : Input → AntCheck.Str
  | .recv _ | .recvX _ => go!"recv"
  | .tick | .unreachable _ => go!"tick"
  | .propose _ | .proposeConf _ _ => go!"propose"
  | .readIndex _ => go!"read"
  | .campaign => go!"campaign"
  | .transfer _ => go!"transfer"
  | .snapStatus _ _ => go!"snapstatus"
  | .applyConf _ => go!"apply"
  | .storeAck _ => go!"write"

/-- The protocol message the input's drain handles (`n.cause`). -/
def Input.cause : Input → Option Msg
  | .recv m => some m
  | _ => none

/-- The transfer message the input's drain handles. -/
def Input.xcause : Input → Option XMsg
  | .recvX x => some x
  | _ => none

/-- `RawNode.Propose(data)`'s message (`rawnode.go`: `MsgProp` from the node, one entry of the data,
term and index 0). -/
def propMsg (id : w64) (data : List w8) : Msg :=
  Msg.mk .propose id (W64 0) (W64 0) false (W64 0) (W64 0) (W64 0) (W64 0)
    [EntryM.mk (W64 0) (W64 0) (W32 0) data]

/-- `RawNode.ProposeConfChange(cc)`'s message (`ConfChangeToMsg`): `MsgProp` from the node, one entry
of the conf type `ty` (`EntryConfChange` or `EntryConfChangeV2`) with `cc`'s marshalled bytes. -/
def propConfMsg (id : w64) (ty : w32) (data : List w8) : Msg :=
  Msg.mk .propose id (W64 0) (W64 0) false (W64 0) (W64 0) (W64 0) (W64 0)
    [EntryM.mk (W64 0) (W64 0) ty data]

/-- The configuration fold's admissible pairs certified in `G` (raft's `Adm`, parity B3). -/
def admOf (G : RaftFacts) : List EntryM → CCState → Prop := fun l cs => (l, cs) ∈ G.confs

/-- What one input does to node `n`'s state (design §3.4). A
conf change is proposed only with conf changes on. `ApplyConfChange` is no input here: the driver
reports `conf` at the apply, in the node's goroutine, so `antSim_conf` takes it and its report as one
step (`ApplyConfEndR`). -/
def InputStep (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop) (n : Fin R.N)
    (r : RState) : Input → RState → Prop
  | .recv m, r' => RecvEndR Adm (R.k n) (nodeId n) r m r'
  | .recvX x, r' => (x.ty = .timeoutNow ∧ TimeoutNowEndR (nodeId n) r x r') ∨
                        (x.ty = .transferLeader ∧ TransferRecvEndR (nodeId n) r x r')
  | .tick, r' => TickEndR (R.k n) (nodeId n) r r'
  | .propose d, r' => RecvEndR Adm (R.k n) (nodeId n) r (propMsg (nodeId n) d) r'
  | .proposeConf ty d, r' =>
      R.md.confChanges = true ∧ RecvEndR Adm (R.k n) (nodeId n) r (propConfMsg (nodeId n) ty d) r'
  | .readIndex c, r' => RecvEndR Adm (R.k n) (nodeId n) r (readMsg c) r'
  | .campaign, r' => CampaignEndR (R.k n) (nodeId n) r r'
  | .transfer to, r' => TransferEndR (nodeId n) r to r'
  | .snapStatus to ok, r' => SnapStatusEndR (nodeId n) r r'
  | .unreachable _, r' => r' = r
  | .applyConf _, _ => False
  | .storeAck resp, r' => StoreAckEndR Adm dec (R.k n) (nodeId n) r resp r'

/-- The view once the node has taken an input (before any report): the drain's `by` and cause; its
`recv` not reported yet. -/
def NodeView.noteInput (v : NodeView) (inp : Input) : NodeView :=
  { v with byE := inp.byE, cause := inp.cause, xcause := inp.xcause, told := false }

/-- **`Advance` with no snapshot applied** (parity B1, snapshots off): `AdvanceEndR` whose storage
acknowledgement is `AckEndR`'s first or second arm (nothing, or the applied index moved), never
`appliedSnap`. Parity B3 lifts it with snapshots. -/
inductive AdvanceNoSnap (Adm : List EntryM → CCState → Prop) (dec : CCDec) (k : NodeK) (id : w64) :
    RState → List Msg → RState → Prop
  | nil (r r' : RState) :
      (r' = r ∨ ∃ a, StepR Adm dec id 0 r [] { r with applied := a, cidx := max r.cidx (uint.nat a) } ∧
        r' = { r with applied := a, cidx := max r.cidx (uint.nat a) }) →
      AdvanceNoSnap Adm dec k id r [] r'
  | cons (r r1 r' : RState) (q : Msg) (qs : List Msg) :
      RecvEndR Adm k id r q r1 → AdvanceNoSnap Adm dec k id r1 qs r' →
      AdvanceNoSnap Adm dec k id r (q :: qs) r'

/-- The `by`s of the harness's drains (`n.input`'s, and `boot`'s right after the `boot` report). -/
def DrainBy (b : AntCheck.Str) : Prop := b = go!"boot" ∨ ∃ inp : Input, b = inp.byE

/-- **How node `n` reached the state `r₁` a `Ready` (or `HasReady`) is taken at**, from its view `v`: no input taken (a drain's, at the view's own
state), an input taken between inputs (`v` noted it; a message received was sent to it; a protocol
message has a nonzero term), or `Advance` at the end of a `Ready` whose reports are all made
(`AdvanceEndR` stepping the `Ready`'s self-addressed messages; with snapshots off, applying none:
`AdvanceNoSnap`). -/
inductive Reach (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop) (net : List Msg)
    (xnet : List XMsg) (n : Fin R.N) : NodeView → RState → Prop
  | stay (v : NodeView) : v.Idle → DrainBy v.byE → Reach R dec Adm net xnet n v v.r
  | input (v : NodeView) (inp : Input) (r₁ : RState) :
      v.Idle → v.byE = inp.byE → v.cause = inp.cause → v.xcause = inp.xcause →
      (∀ m, inp = .recv m → m ∈ net ∧ m.dst = nodeId n ∧ m.term ≠ W64 0) →
      (∀ x, inp = .recvX x → x ∈ xnet ∧ x.dst = nodeId n) →
      InputStep R dec Adm n v.r inp r₁ → Reach R dec Adm net xnet n v r₁
  | advance (v : NodeView) (r₁ : RState) :
      v.pend = [] → v.xpend = [] → v.ce = [] → v.rpend = [] → DrainBy v.byE →
      AdvanceEndR Adm dec (R.k n) (nodeId n) v.r v.qs r₁ →
      (R.md.snapshots = false → AdvanceNoSnap Adm dec (R.k n) (nodeId n) v.r v.qs r₁) →
      Reach R dec Adm net xnet n v r₁

/-- A `Ready`'s data, as the harness reads it: the role after it (`SoftState`, or the last reported
one; `pre` for `StatePreCandidate`) and its hard state (or the last written one), its entries to
write, its messages to other nodes in its order (sync: all; async: those sent at once), the
responses its write releases (async: `AfterAppTy`), its transfer messages, the self-addressed
messages `Advance` steps, its committed entries, its read states, its snapshot's id. -/
structure ReadyD where
  role : Role
  pre : Bool
  term : w64
  vote : w64
  commit : w64
  ents : List EntryM
  msgs : List Msg
  resp : List Msg
  xmsgs : List XMsg
  qs : List Msg
  ce : List EntryM
  reads : List ReadStateM
  snap : Option entryID

/-- A `Ready`'s messages to others are to servers (`msgShape.stmt` concludes it). -/
def ReadyMsgsToVoters (N : Nat) (rd : ReadyD) : Prop :=
  ∀ q ∈ rd.msgs ++ rd.resp, ∃ j : Fin N, q.dst = nodeId j

/-- The messages a storage write's `Responses` hold in async mode (`raft.go:546`, `send`). -/
def AfterAppTy (t : MsgType) : Prop := t = .appResp ∨ t = .voteResp ∨ t = .preVoteResp

instance (t : MsgType) : Decidable (AfterAppTy t) := by unfold AfterAppTy; infer_instance

/-- **The `Ready` binding at the protocol level** (`ReadyOut` over `RState`): a `Ready` taken at `r`
from node `n`'s view `v` reports `r`'s role (a
pre-candidate's protocol role is a follower, and only with pre-vote on) and hard state; its entries
are what the write appends (the full log after it, from the first entry's index, which starts at a
conflict with the disk's log or past its end); without a snapshot and with no entries, the full log
is the disk's; its messages are `r`'s outbox, those to itself queued for `Advance` (up to
permutation), the others to servers (in async mode split: `AfterAppTy` ones released by the write);
its transfer messages raft's (`XReadyOk`: `XPendOk` at `r`); its committed entries follow what was handed out, within the commit;
its read states `r`'s; without snapshots no snapshot, the log from `base0` and no snapshot message; the full log's
indices its positions. -/
def ReadyOutP (R : RunCfg) (n : Fin R.N) (v : NodeView) (r : RState) (rd : ReadyD) : Prop :=
  rd.role = r.p.role ∧ (rd.pre = true → rd.role = .follower ∧ (R.k n).prevote = true) ∧
  rd.term = r.p.term ∧ rd.vote = r.p.vote ∧ rd.commit = r.p.commit ∧
  (rd.snap = none → rd.ents = [] → r.full = v.dur.log) ∧
  (∀ e0 ∈ rd.ents.head?, r.full = v.dur.log.take (uint.nat e0.Index' - 1) ++ rd.ents ∧
    ∀ e ∈ v.dur.log[uint.nat e0.Index' - 1]?, e.Term' ≠ e0.Term') ∧
  rd.qs.Perm (r.p.outbox.filter (fun q => decide (q.dst = nodeId n))) ∧
  (R.md.async = false → rd.resp = [] ∧
    rd.msgs.Perm (r.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n)))) ∧
  (R.md.async = true →
    rd.msgs.Perm (r.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n ∧ ¬ AfterAppTy q.ty))) ∧
    rd.resp.Perm (r.p.outbox.filter (fun q => decide (q.dst ≠ nodeId n ∧ AfterAppTy q.ty)))) ∧
  (∀ x ∈ rd.xmsgs, XPendOk R.N (nodeId n) r.p x) ∧
  v.delivered ++ rd.ce <+: r.full ∧ (v.delivered ++ rd.ce).length ≤ uint.nat r.p.commit ∧
  rd.reads = r.p.rd.states ∧
  (R.md.snapshots = false → r.p.base = base0 ∧ rd.snap = none ∧ ∀ q ∈ r.p.outbox, q.ty ≠ .snap) ∧
  LogIdx r.full ∧
  ReadyMsgsToVoters R.N rd

/-- The harness reports the `Ready` (`write || role != n.role`, or a snapshot): its hard state differs
from the last written one, it has entries or a snapshot, or its role from the last reported. -/
def Reported (v : NodeView) (rd : ReadyD) : Prop :=
  rd.term ≠ v.dur.term ∨ rd.vote ≠ v.dur.vote ∨ rd.commit ≠ v.dur.commit ∨ rd.ents ≠ [] ∨
    rd.snap ≠ none ∨ roleStr rd.pre rd.role ≠ roleS v

/-- What raft's `Ready` leaves (`pAccepted`): `r` with the outbox and the read states cleared. -/
def accepted (r : RState) : RState :=
  { r with p := { r.p with outbox := [], rd := { r.p.rd with states := [] } } }

/-- The drain phase after a `Ready` taken at `r`: raft's state after it, the reported role, the
`Ready`'s messages, transfer messages, committed entries and read states to report, its
self-addressed messages for `Advance`. -/
def NodeView.drainOf (v : NodeView) (r : RState) (rd : ReadyD) : NodeView :=
  { v with r := accepted r, pre := rd.pre, qs := rd.qs, pend := rd.msgs, xpend := rd.xmsgs,
           ce := rd.ce, rpend := rd.reads }

/-- The view after a reported `Ready` in sync mode: the drain phase, the disk now the `Ready`'s state,
the disk before it the announced write's undo, not made (B 349-359). -/
def NodeView.afterReady (v : NodeView) (r : RState) (rd : ReadyD) : NodeView :=
  { v.drainOf r rd with dur := durOf (accepted r), undo := some v.dur, made := false }

/-- **The steps of a node that report nothing**: taking an input (noted in the view); reaching a
state with no `Ready` (`HasReady` false: nothing to write, send, apply or read, the same hard state,
log and role); a `Ready` whose write and role the harness does not report. -/
inductive Quiet (R : RunCfg) (dec : CCDec) (Adm : List EntryM → CCState → Prop) (net : List Msg)
    (xnet : List XMsg) (n : Fin R.N) : NodeView → NodeView → Prop
  | input (v : NodeView) (inp : Input) :
      v.Idle → (∀ m, inp = .recv m → m ∈ net ∧ m.dst = nodeId n) →
      (∀ x, inp = .recvX x → x ∈ xnet ∧ x.dst = nodeId n) →
      Quiet R dec Adm net xnet n v (v.noteInput inp)
  | noReady (v : NodeView) (r₁ : RState) :
      Reach R dec Adm net xnet n v r₁ → r₁.p.outbox = [] → r₁.p.rd.states = [] →
      r₁.p.term = v.ps.term → r₁.p.vote = v.ps.vote → r₁.p.commit = v.ps.commit →
      r₁.p.role = v.ps.role → r₁.full = v.r.full →
      Quiet R dec Adm net xnet n v { v with r := r₁, qs := [] }
  | silentReady (v : NodeView) (r₁ : RState) (rd : ReadyD) :
      Reach R dec Adm net xnet n v r₁ → ReadyOutP R n v r₁ rd → ¬ Reported v rd →
      Quiet R dec Adm net xnet n v (v.drainOf r₁ rd)

/-- `V` with node `n`'s view replaced. -/
def setV {N : Nat} (V : Fin N → NodeView) (n : Fin N) (v : NodeView) : Fin N → NodeView :=
  fun j => if j = n then v else V j

/-- The drain's reports after its `recv` (`reportCause` first, for `by = recv`). -/
def Told (v : NodeView) : Prop := v.byE = go!"recv" → v.told = true

/-- The term budget: a campaign's `term + 1` does not wrap (raft's term budget). -/
def TermRoom (v : NodeView) : Prop := uint.Z v.ps.term + 1 < 2 ^ 64

/-! ## The statements: the run -/

/-- A node of the run before its `boot` report (`antSim_init`): at its start (`PInitR`), nothing
handed out, its disk its own state, no announced write, nothing queued, the initial configuration,
no read, not running yet, between inputs. -/
def FreshView (R : RunCfg) (v : NodeView) : Prop :=
  PInitR R v.r ∧ v.delivered = [] ∧ v.dur = durOf v.r ∧ v.undo = none ∧ v.mems = [] ∧
  v.conf = R.c0 ∧ v.confAt = 0 ∧ v.pre = false ∧ v.reads = [] ∧ v.alive = false ∧ v.Idle ∧
  v.told = false ∧ v.cause = none ∧ v.xcause = none

/-- **The initial state** (`Init0`, B 755-764): before any report, at the run's fresh nodes, the
checker is at a state related to them, with nothing sent; its facts are certified by any `G` with
the run's boot facts and no acknowledgement yet. -/
abbrev antSim_init.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (V : Fin R.N → NodeView), (∀ n, FreshView R (V n)) →
    ∃ S, Prefix R.cfg [] S ∧ AntSim R dec S V [] [] ∧
      ∀ G : RaftFacts, BootFacts R G → G.acks = [] → GlobalOk R S [] G

/-! ## The statements: the reports -/

/-- **`boot`, fresh** (`node.start`, B 162-194): a fresh node's `boot` report (`evBoot`); it runs. -/
abbrev antSim_boot.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
    SimPre R dec S V net xnet evs G → FreshView R (V n) →
    SimStep R dec evs G (evBoot R (nodeId n)) (setV V n { V n with alive := true }) net xnet

/-- Restart (parity B2, `restartAtSpec`'s post): the state raft restarts at from the disk `d` with
`a` entries applied, at the configuration `cs` they make (no snapshot: B3 adds the stored one). -/
def RestartR (dec : CCDec) (R : RunCfg) (d : DurW) (a : Nat) (cs : CCState) (r0 : RState) : Prop :=
  r0.p.term = d.term ∧ r0.p.vote = d.vote ∧ r0.p.commit = d.commit ∧ r0.p.log = d.log ∧
  r0.p.base = base0 ∧ r0.fp = [] ∧ r0.p.lead = W64 0 ∧ r0.p.role = .follower ∧ r0.p.votes = ∅ ∧
  r0.p.outbox = [] ∧ r0.p.matched = ∅ ∧ uint.nat r0.applied = a ∧ r0.pci = W64 0 ∧
  r0.snap = false ∧ r0.cidx = a ∧ r0.cfg = cs ∧ cfgFold dec R.c0 (d.log.take a) = some cs ∧
  a ≤ uint.nat d.commit

/-- The view of a restarted node at its `boot` (the binding's `Boot` clears `pending`, `queue`,
`reads` and `undo`, and sets `role := follower`, B 162-166). -/
def NodeView.boot (v : NodeView) (r0 : RState) (d : DurW) (a : Nat) (cs : CCState) : NodeView :=
  { r := r0, delivered := d.log.take a, dur := d, undo := none, made := true, mems := [],
    conf := cs, confAt := lastConfIdx d.log a, pre := false, reads := [], alive := true,
    byE := v.byE }

/-- The last index and term of a full log (the `boot` report's `lastIndex`, `lastTerm`). -/
def lastIT (l : List EntryM) : Int × Int :=
  match l.getLast? with
  | some e => ((l.length : Int), uint.Z e.Term')
  | none => (0, 0)

/-- **`boot` after a restart** (parity B2, B 162-194): a stopped node restarts from its disk, or from
the disk before an unmade write; it reports what it recovered and the applied index (within the
committed log). -/
abbrev antSim_bootR.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (d : DurW)
    (a : Nat) (cs : CCState) (r0 : RState),
    SimPre R dec S V net xnet evs G → (V n).alive = false →
    (d = (V n).dur ∨ ((V n).undo = some d ∧ (V n).made = false)) → RestartR dec R d a cs r0 →
    d.log.take a <+: G.committed →
    SimStep R dec evs G
      (evBootR (nodeId n) d.term d.vote d.commit (lastIT d.log).1 (lastIT d.log).2 a
        (confView R.N cs))
      (setV V n ((V n).boot r0 d a cs)) net xnet

/-- **`recv`** (`reportCause`, B 199-204): the message a node handles, sent to it, is reported (at its
drain's first report); the binding's `pending[n]` is then it. -/
abbrev antSim_recv.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (m : Msg),
    SimPre R dec S V net xnet evs G → m ∈ net → m.dst = nodeId n → (V n).cause = some m →
    SimStep R dec evs G (evRecv (nodeId n) m) (setV V n { V n with told := true }) net xnet

/-- **`recv` of a transfer message** (`MsgTimeoutNow`, a forwarded `MsgTransferLeader`; B 199-204,
unmodelled: no `Sendable` check). -/
abbrev antSim_recvX.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (x : XMsg),
    SimPre R dec S V net xnet evs G → x ∈ xnet → x.dst = nodeId n → (V n).xcause = some x →
    SimStep R dec evs G (evRecvX (nodeId n) x) (setV V n { V n with told := true }) net xnet

/-- **The steps that report nothing** (`Quiet`): the relation holds of the new view, `S` unchanged. -/
abbrev antSim_quiet.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts) (n : Fin R.N) (v' : NodeView),
    AntSim R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    Quiet R dec (admOf G) net xnet n (V n) v' → AntSim R dec S (setV V n v') net xnet

/-- **`ready`** (sync, B 439-447: `InMemory` then `OnDisk`): a `Ready` taken after an input or an
`Advance`, whose write, snapshot or role the harness reports, is taken; the node's view becomes the
`Ready`'s (the drain phase), its disk the `Ready`'s state. -/
abbrev antSim_ready.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
    (rd : ReadyD),
    SimPre R dec S V net xnet evs G → R.md.async = false →
    Reach R dec (admOf G) net xnet n (V n) r₁ → ReadyOutP R n (V n) r₁ rd → Reported (V n) rd →
    Told (V n) → ReadyFacts G (nodeId n) r₁ → TermRoom (V n) →
    SimStep R dec evs G
      (evReady (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents rd.snap)
      (setV V n ((V n).afterReady r₁ rd)) net xnet

/-- **`send`** (sync, B 510-593): the next message of the node's `Ready` is reported, then it is on
the network; the announced write is over (B 546). -/
abbrev antSim_send.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (q : Msg)
    (rest : List Msg),
    SimPre R dec S V net xnet evs G → R.md.async = false → (V n).pend = q :: rest → Told (V n) →
    MsgFacts G q →
    SimStep R dec evs G (evSend (nodeId n) (V n).byE q)
      (setV V n { V n with pend := rest, undo := none, made := true }) (net ++ [q]) xnet

/-- The raft facts a `send` of a transfer message needs (raft's, added to `G` before the report): a
`MsgTimeoutNow`'s transferee acknowledged at its term (`isAcked`; design §6.4). -/
def XMsgFacts (G : RaftFacts) (x : XMsg) : Prop :=
  x.ty = .timeoutNow → ∃ i : w64, uint.Z i ≠ 0 ∧ (x.dst, x.term, i) ∈ G.acks

/-- **`send` of a transfer message** (B 510-524, unmodelled, B 702): the next transfer message of the
node's `Ready` is reported, then it is on the network. -/
abbrev antSim_sendX.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (x : XMsg)
    (rest : List XMsg),
    SimPre R dec S V net xnet evs G → R.md.async = false → (V n).xpend = x :: rest → Told (V n) →
    XMsgFacts G x →
    SimStep R dec evs G (evSendX (nodeId n) (V n).byE x)
      (setV V n { V n with xpend := rest, undo := none, made := true }) net (xnet ++ [x])

/-- **`apply`** (sync, B 598-609): the `Ready`'s committed entries are reported, then handed out. -/
abbrev antSim_apply.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
    SimPre R dec S V net xnet evs G → R.md.async = false → (V n).ce ≠ [] → Told (V n) →
    SimStep R dec evs G (evApply (nodeId n) (V n).byE (V n).ce)
      (setV V n { V n with delivered := (V n).delivered ++ (V n).ce, ce := [], undo := none,
                           made := true }) net xnet

/-- The binding's last `MaxReads` of a node's read requests (`ReadAsked`, B 660: the oldest dropped). -/
def readsTrunc {α : Type} (q : List α) : List α := if q.length > AntCheck.maxReads then q.drop 1 else q

/-- The view's reads after a `readreq` of `p`: appended, the last `MaxReads` kept (as the binding's,
B 660). -/
def readsAsk (l : List (AntCheck.Str × Nat)) (p : AntCheck.Str × Nat) : List (AntCheck.Str × Nat) :=
  readsTrunc (l ++ [p])

/-- **`readreq`** (B 657-661): the reader's context, asked of a node between inputs, is reported
before `ReadIndex`; the view records it with the committed length known now, keeping the last
`MaxReads` requests as the binding does. -/
abbrev antSim_readreq.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (ctx : List w8),
    SimPre R dec S V net xnet evs G → (V n).Idle →
    SimStep R dec evs G (evReadReq (nodeId n) ctx)
      (setV V n { V n with reads := readsAsk (V n).reads (ctx, G.committed.length) }) net xnet

/-- **`read`** (B 663-667): the next read state of the node's `Ready` is reported; its index is at
least the committed length known when its context was asked (raft's read-index safety,
`ReadIndex.lean`'s `readStateRaw`). -/
abbrev antSim_read.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (rs : ReadStateM)
    (rest : List ReadStateM),
    SimPre R dec S V net xnet evs G → (V n).rpend = rs :: rest → Told (V n) →
    (∀ f, (rs.RequestCtx', f) ∈ (V n).reads → f ≤ uint.nat rs.Index') →
    SimStep R dec evs G (evRead (nodeId n) rs.RequestCtx' rs.Index')
      (setV V n { V n with rpend := rest,
                           reads := (V n).reads.filter (fun p => decide (p.1 ≠ rs.RequestCtx')) })
      net xnet

/-! ## The statements: async storage (parity B2) -/

/-- An announced in-memory state of a `Ready` (async), as its `mem` report says it. -/
def ReadyD.memRec (rd : ReadyD) (v : NodeView) : MemRec :=
  { role := rd.role, pre := rd.pre, term := rd.term, vote := rd.vote, commit := rd.commit,
    ents := rd.ents, snap := rd.snap, cause := v.cause, byE := v.byE }

/-- **`mem`** (async, B 450-459): a reported `Ready` whose write the storage goroutine makes later;
its in-memory state is queued. -/
abbrev antSim_mem.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (r₁ : RState)
    (rd : ReadyD),
    SimPre R dec S V net xnet evs G → R.md.async = true →
    Reach R dec (admOf G) net xnet n (V n) r₁ → ReadyOutP R n (V n) r₁ rd → Reported (V n) rd →
    Told (V n) → ReadyFacts G (nodeId n) r₁ → TermRoom (V n) →
    SimStep R dec evs G
      (evMem (nodeId n) (V n).byE (roleStr rd.pre rd.role) rd.term rd.vote rd.commit rd.ents rd.snap)
      (setV V n { (V n).drainOf r₁ rd with mems := (V n).mems ++ [rd.memRec (V n)] }) net xnet

/-- A disk after a queued state's write: its hard state, its entries from their first index. -/
def DurW.write (d : DurW) (m : MemRec) : DurW :=
  { term := m.term, vote := m.vote, commit := m.commit,
    log := match m.ents.head? with
      | none => d.log
      | some e0 => d.log.take (uint.nat e0.Index' - 1) ++ m.ents }

/-- **`write`** (async, B 462-470): the storage goroutine announces the oldest queued state's write. -/
abbrev antSim_write.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (m : MemRec)
    (rest : List MemRec),
    SimPre R dec S V net xnet evs G → R.md.async = true → (V n).mems = m :: rest →
    SimStep R dec evs G (evWrite (nodeId n) m.term m.vote m.commit m.ents m.snap)
      (setV V n { V n with dur := (V n).dur.write m, undo := some (V n).dur, made := false,
                           mems := rest }) net xnet

/-- **`wrote`** (B 502-504): the announced write is made; the messages after it may go. -/
abbrev antSim_wrote.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
    SimPre R dec S V net xnet evs G → R.md.async = true → (V n).undo ≠ none →
    SimStep R dec evs G (evWrote (nodeId n)) (setV V n { V n with undo := none, made := true }) net xnet

/-- **`flush`** (batch, B 474-478): the oldest queued `mem` joins the next batch write (`more` for
every one after the first of a flush). -/
abbrev antSim_flush.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (m : MemRec)
    (rest : List MemRec) (more : Bool),
    SimPre R dec S V net xnet evs G → R.drv.batch = true → (V n).mems = m :: rest →
    (more = true → (V n).undo ≠ none) →
    SimStep R dec evs G (evFlush (nodeId n) more)
      (setV V n { V n with dur := (V n).dur.write m, mems := rest,
                           undo := if more then (V n).undo else some (V n).dur,
                           made := if more then (V n).made else false }) net xnet

/-- **`net`** (batch, B 483-492): the batch's write, the union of the flushed states, is announced:
the disk's hard state and its entries from the lowest conflict (`first`). -/
abbrev antSim_net.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (d0 : DurW)
    (es : List EntryM),
    SimPre R dec S V net xnet evs G → R.drv.batch = true → (V n).undo = some d0 →
    (∀ e0 ∈ es.head?, (V n).dur.log = (V n).dur.log.take (uint.nat e0.Index' - 1) ++ es ∧
      ∀ e ∈ d0.log[uint.nat e0.Index' - 1]?, e.Term' ≠ e0.Term') →
    (es = [] → (V n).dur.log = d0.log) →
    SimStep R dec evs G (evNet (nodeId n) (V n).dur.term (V n).dur.vote (V n).dur.commit es) V net xnet

/-- **`made`** (batch, B 496-499): the batch's write is on disk. -/
abbrev antSim_made.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N),
    SimPre R dec S V net xnet evs G → R.drv.batch = true → (V n).undo ≠ none →
    SimStep R dec evs G (evMade (nodeId n)) (setV V n { V n with made := true }) net xnet

/-! ## The statements: snapshots and conf changes (parity B3) -/

/-- **`conf`** (B 614-630): `ApplyConfChange` of the entry at position `k` (index `k + 1`), committed
and handed out; the binding's configuration becomes raft's. -/
abbrev antSim_conf.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (k : Nat)
    (r' : RState),
    SimPre R dec S V net xnet evs G → k < (V n).delivered.length →
    ApplyConfEndR dec (admOf G) (R.k n) (nodeId n) (V n).r k r' [] →
    SimStep R dec evs G (evConf (nodeId n) (k + 1) (confView R.N r'.cfg))
      (setV V n { V n with r := r', conf := r'.cfg, confAt := k + 1 }) net xnet

/-- **`restore`** (B 634-643): a restored snapshot (`r.snap`) of the full prefix `fp` is handed to
the state machine; `G.snaps` certifies the prefix committed; the binding's configuration is the
prefix's. -/
abbrev antSim_restore.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (cs : CCState)
    (a : Bool),
    SimPre R dec S V net xnet evs G → (V n).r.snap = true →
    ((V n).r.fp.length, (V n).r.fp) ∈ G.snaps → cfgFold dec R.c0 (V n).r.fp = some cs →
    SimStep R dec evs G (evRestore (nodeId n) (V n).r.fp.length (confView R.N cs) a)
      (setV V n { V n with delivered := (V n).r.fp, conf := cs,
                           confAt := lastConfIdx (V n).r.fp (V n).r.fp.length }) net xnet

/-- **`snap`** (B 647-650): a snapshot taken at `k` (within the applied index, which is within the
commit), `t` the full log's term at `k`. -/
abbrev antSim_snap.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (evs : List AntCheck.Event) (G : RaftFacts) (n : Fin R.N) (k : Nat) (e : EntryM),
    SimPre R dec S V net xnet evs G → 1 ≤ k → k ≤ uint.nat (V n).r.applied →
    uint.nat (V n).r.applied ≤ uint.nat (V n).ps.commit → (V n).r.full[k - 1]? = some e →
    SimStep R dec evs G (evSnap (nodeId n) k e.Term') V net xnet

/-! ## `GC` -/

/-- **`GC`** (B 713-723, taken while due before each event, `Checker.next`'s `gcLoop`): the steps
end within `gcFuel` with no violation, and the relation holds after them. -/
abbrev antSim_gc.stmt : Prop :=
  ∀ (R : RunCfg) (dec : CCDec) (S : AntCheck.State) (V : Fin R.N → NodeView) (net : List Msg)
    (xnet : List XMsg) (G : RaftFacts),
    AntSim R dec S V net xnet → RaftLaws G → GlobalOk R S net G →
    ∃ S', AntCheck.gcLoop (AntCheck.gcFuel S) S = .ok (S', none) ∧ AntSim R dec S' V net xnet ∧
      GlobalOk R S' net G

end stmts

end AntSim
end EtcdGrove
end Perennial
