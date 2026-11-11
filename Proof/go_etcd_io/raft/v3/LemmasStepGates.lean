/-
Lean-first (no Rocq counterpart). **`raft.Step`'s gates** (2026-11-10, trace-check Q8 stage 1 slice 11,
`notes/decisions.md`, "Q8 stage 1 (slice 11)"): the spec (`Spec/go_etcd_io/raft/v3/raft__Step.lean`)
names them, and a spec file defines nothing but its spec (CLAUDE.md, "Package APIs", `--layout`).

`raft.Step` runs a fixed sequence of trace hooks per path: the receive hook first (`traceReceiveMessage`),
then the term preamble's step-down (`becomeFollower`) or a stale message's answer (`send`), then the type
switch: `hup`'s campaign, a vote request's answer (`send`), or the role's step function
(`stepFollower`, `stepCandidate`, `stepLeader`) with its own gates. Each hook's gate is the caller's,
from the caller's resources (`StepG`), as the callees' specs take them:
- `R.G` before the receive hook, `R.G0` after it;
- `R.G1` after the preamble, which the type switch starts from (`stepGates`' `"Hgpre"`: the step-down's
  gate when it runs, `PreBF`, an update otherwise);
- `R.GE` after the switch's (or a stale message's) last line: the step functions' `G'`;
- the step functions' intermediate resources (`R.Gf`, `R.Gb1`, `R.Gb2` of `stepCandidate`; `R.Gp1`,
  `R.Gp2`, `R.Gc` of `stepLeader`).
`Step` gives back one of them (`stepOut`), untagged: a caller that needs to know which puts the fact in
its resources.

The step functions' gates are bundled here (`followerGates`, `candidateGates`, `leaderGates`,
`hupGates`) as their specs state them (the same text, so that `Step`'s proof hands them over by
unfolding), at the state the step function is called in (`preState`: after the preamble's step-down,
whose `Progress` map the caller cannot name, so the bundles are under `∀ pvs`).
-/
module

public import Spec.go_etcd_io.raft.v3.stepLeader
public import Spec.go_etcd_io.raft.v3.stepCandidate
public import Spec.go_etcd_io.raft.v3.stepFollower
public import Spec.go_etcd_io.raft.v3.raft__hup
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Spec.go_etcd_io.raft.v3.raft__send
public import Spec.go_etcd_io.raft.v3.traceReceiveMessage
public import Proof.go_etcd_io.raft.v3.StepGhostMode
public import Proof.go_etcd_io.raft.v3.TracedSend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **`Step`'s term preamble steps down** (`becomeFollower(m.Term, lead)`): a message of a higher term
but a pre-vote request or a granted pre-vote response (a vote request inside a leader's lease returns
before it, which `Step`'s spec does not decide: the caller's gate is asked whenever it may run). -/
def PreBF (m : MessageM) (s : NState) : Prop :=
  uint.Z s.term < uint.Z m.Term' ∧ m.Type' ≠ MsgPreVote ∧ ¬ (m.Type' = MsgPreVoteResp ∧ m.Reject' = false)

instance PreBF.decidable (m : MessageM) (s : NState) : Decidable (PreBF m s) := by
  unfold PreBF; infer_instance

/-- The leader the preamble's step-down records: the sender of a leader's message. -/
def preLead (m : MessageM) : w64 :=
  if m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat ∨ m.Type' = MsgSnap then m.From' else W64 0

/-- The state after `Step`'s term preamble, with the step-down's `Progress` map `pvs`. -/
def preState (s : NState) (m : MessageM) (pvs : GMap w64 Progress) : NState :=
  if PreBF m s then { becomeFollower s m.Term' (preLead m) with prvals := pvs } else s

/-- A stale message's answer (`Step`'s `m.Term < r.Term` arm), of type `ty`: a stale leader message's
empty `MsgAppResp` at the node's term (check-quorum or pre-vote on), or a stale pre-vote request's
rejection. -/
def LowSend (id : w64) (s : NState) (m : MessageM) (ty : w32) (mm : Msg) : Prop :=
  (ty = MsgAppResp ∧ (s.cq = true ∨ s.prevote = true) ∧ (m.Type' = MsgHeartbeat ∨ m.Type' = MsgApp) ∧
    mm = absMsgFrom .appResp ⟨MsgAppResp, m.From', W64 0, W64 0, W64 0, W64 0, W64 0, W64 0, false, W64 0⟩
      id s.term []) ∨
  (ty = MsgPreVoteResp ∧ m.Type' = MsgPreVote ∧ mm = Msg.plain .preVoteResp id m.From' s.term true)

/-- A vote request's answer's type. -/
def vrespTyOf (m : MessageM) : w32 := if m.Type' = MsgVote then MsgVoteResp else MsgPreVoteResp

/-- A vote request's answer at the state `s1` after the preamble: granted at the request's term,
rejected at the node's. -/
def vrespMsgOf (id : w64) (s1 : NState) (m : MessageM) (rej : Bool) : Msg :=
  Msg.plain (if m.Type' = MsgVote then .voteResp else .preVoteResp) id m.From'
    (if rej then s1.term else m.Term') rej

/-- The campaign a `MsgHup` starts (`Step`'s `hup` call). -/
def hupType (s : NState) : CampaignType :=
  if s.prevote = true then campaignPreElection else campaignElection

/-- (2026-11-10, slice 12) **The local message a tick steps** (`tickElection`'s `MsgHup`,
`tickHeartbeat`'s `MsgCheckQuorum` and `MsgBeat`): `&pb.Message{From: new(r.id), Type: ty.Enum()}`,
every other field unset. The tick specs name it for `Step`'s gates. -/
def tickMsg (ty : w32) (id : w64) : MessageM := { (zero_val MessageM) with Type' := ty, From' := id }

@[simp] theorem tickMsg_Type' (ty : w32) (id : w64) : (tickMsg ty id).Type' = ty := rfl
@[simp] theorem tickMsg_From' (ty : w32) (id : w64) : (tickMsg ty id).From' = id := rfl
@[simp] theorem tickMsg_Term' (ty : w32) (id : w64) : (tickMsg ty id).Term' = W64 0 := rfl

/-! ### `Step`'s end state (2026-11-10, slice 13)

What the closing wand (`stepClose`) learns of the state `Step` returns, on the message types a traced
node steps (`StepEndTy`), in the gates' own states: the step function's result at the state after the
preamble (`preState`, as `stepFnGates`), a vote request's answer, a stale message's answer, `hup`'s.
Each is what the callee's spec gives (`FollowerStepResultC`, `CandidateStepResultC`,
`LeaderStepResultC`, `HupOkC`), so as exact as the code's specs: the messages a broadcast queues
(`ReplSends`' `ms`) are existential there (`notes/decisions.md`, "Q8 stage 1 (slice 13)"). -/

/-- The message types `StepEnd` describes: the six traced types and the four local ones a traced
node steps (`tickElection`'s `MsgHup`, `tickHeartbeat`'s `MsgBeat`, `Propose`'s `MsgProp`, and
(2026-11-11, slice 27n, Q27 (a)) `ReportUnreachable`'s `MsgUnreachable`, whose end state is `s` but
for `Progress` values of the same `Match`: `LeaderNonpropResultC`'s report case queues nothing). -/
def StepEndTy (ty : w32) : Prop :=
  ty = MsgApp ∨ ty = MsgAppResp ∨ ty = MsgHeartbeat ∨ ty = MsgHeartbeatResp ∨ ty = MsgVote ∨
    ty = MsgVoteResp ∨ ty = MsgHup ∨ ty = MsgBeat ∨ ty = MsgProp ∨ ty = MsgUnreachable

/-- (2026-11-11, slice 24b) **A candidate's vote response that decides its election**: a `MsgVoteResp`
of the candidate's term whose recorded tally is won (`JQuorum`) or lost (`JLost`) at `c`, so that
`stepCandidate` runs a gate past the preamble's resource (`"Hgbl"` or `"Hglost"`); its spec returns this
tag. The closing wand reads it (`stepOutG`): the resources before the decision are then not the
step's end (`notes/decisions.md`, "Q8 stage 1 (slice 24b)"). -/
def CandHooked (c : CfgM) (m : MessageM) (s : NState) : Prop :=
  m.Type' = MsgVoteResp ∧ m.Term' = s.term ∧ s.role = .candidate ∧
    (JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))) ∨
      JLost c (recordVote s.votes m.From' (!m.Reject')))

theorem CandHooked.of_ne {c : CfgM} {m : MessageM} {s : NState} (h : m.Type' ≠ MsgVoteResp) :
    ¬ CandHooked c m s := fun h' => h h'.1

/-- (2026-11-11, slice 30c, plan Q30 (a)) **A leader's accepted `MsgAppResp` of its term that reaches
`maybeCommit`** (`AppRespRan`, the code's own run condition at the sender's `Progress` before the step):
`stepLeader` then runs its `"Hgcommit"` gate, so the step ends past it (at `Gc`), never at `G0` or `G1`;
`stepLeader.spec`'s `G` arm says so (its guard), and the closing wand reads it (`stepOutG`). -/
def LeadRan (m : MessageM) (s : NState) : Prop :=
  m.Type' = MsgAppResp ∧ m.Reject' = false ∧ m.Term' = s.term ∧ s.role = .leader ∧
    AppRespRan s m.From' m.Index'

theorem LeadRan.of_ne {m : MessageM} {s : NState} (h : m.Type' ≠ MsgAppResp) : ¬ LeadRan m s :=
  fun h' => h h'.1

/-- A stale message (`Step`'s `m.Term < r.Term` arm). -/
def StaleMsg (s : NState) (m : MessageM) : Prop := m.Term' ≠ W64 0 ∧ uint.Z m.Term' < uint.Z s.term

/-- The role's step function's result at `s1` (the state after the preamble), as its spec states it. -/
def StepFnEnd (c : CfgM) (id : w64) (s1 : NState) (m : MessageM) (ents : List EntryM) (ctx : List w8)
    (s' : NState) : Prop :=
  (s1.role = .follower → ∃ (scfg : CSLists) (sv : SnapshotM) (d : Bool) (c' : CfgM),
      FollowerStepResultC c scfg id s1 m ents sv d s' c' ctx) ∧
  (s1.role = .candidate ∨ s1.role = .preCandidate → ∃ (scfg : CSLists) (sv : SnapshotM) (d : Bool) (c' : CfgM),
      CandidateStepResultC c scfg id s1 m ents sv d s' c' ctx) ∧
  (s1.role = .leader → ∃ d : Bool, LeaderStepResultC c id s1 m ents d s' ctx)

/-- Whether `Step` grants a vote request at `s1` (the state after the preamble): `canVote` and the
candidate's log up to date (`isUpToDate`). -/
def VoteGrant (s1 : NState) (m : MessageM) : Prop :=
  (s1.vote = m.From' ∨ (s1.vote = W64 0 ∧ s1.lead = W64 0) ∨
      (m.Type' = MsgPreVote ∧ uint.Z s1.term < uint.Z m.Term')) ∧
    plogUpToDate s1.logst.prev (s1.logst.sents ++ s1.logst.uents) (entryID.mk m.LogTerm' m.Index') = true

/-- A `MsgVote`'s answer at `s1`: granted, the answer queued and the vote recorded; declined, the
rejection queued. -/
def VoteEnd (id : w64) (s1 : NState) (m : MessageM) (s' : NState) : Prop :=
  (VoteGrant s1 m ∧ s' = { sendMsgs s1 [vrespMsgOf id s1 m false] with vote := m.From' }) ∨
  (¬ VoteGrant s1 m ∧ s' = sendMsgs s1 [vrespMsgOf id s1 m true])

/-- **`Step`'s end state** `s'` from `s` on `m` (see above); nothing on the other types. -/
def StepEnd (c : CfgM) (id : w64) (m : MessageM) (ents : List EntryM) (ctx : List w8) (s s' : NState) :
    Prop :=
  StepEndTy m.Type' →
  (StaleMsg s m → s' = s ∨ ∃ (ty : w32) (mm : Msg), LowSend id s m ty mm ∧ s' = sendMsgs s [mm]) ∧
  (¬ StaleMsg s m → m.Type' = MsgHup → HupOkC c id s s') ∧
  (¬ StaleMsg s m → m.Type' = MsgVote →
    (s.cq = true ∧ s' = s) ∨ ∃ pvs : GMap w64 Progress, VoteEnd id (preState s m pvs) m s') ∧
  (¬ StaleMsg s m → m.Type' ≠ MsgHup → m.Type' ≠ MsgVote →
    ∃ pvs : GMap w64 Progress, StepFnEnd c id (preState s m pvs) m ents ctx s')

/-- (2026-11-11, slice 30c; slice 28n's design) **The storage acknowledgements**, which `Advance` steps. -/
def AckTy (t : w32) : Prop := t = MsgStorageAppendResp ∨ t = MsgStorageApplyResp

/-- (2026-11-11, slice 30c; slice 28n's design) **A storage acknowledgement's end state** (traced): the
protocol reading unchanged (`stableTo`, `appliedTo`; no snapshot, no automatic leave at a traced node),
the outbox with it. `StepEnd` says nothing of these types; the closing wand learns this instead. -/
def AckEnd (m : MessageM) (s s' : NState) : Prop := AckTy m.Type' → toPState s' = toPState s

theorem AckEnd.of_ty {m : MessageM} {s s' : NState} (h : ¬ AckTy m.Type') : AckEnd m s s' :=
  fun h' => absurd h' h

theorem StepEnd.of_ty {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (h : ¬ StepEndTy m.Type') : StepEnd c id m ents ctx s s' :=
  fun h' => absurd h' h

theorem StepEnd.stale {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hst : StaleMsg s m)
    (h : s' = s ∨ ∃ (ty : w32) (mm : Msg), LowSend id s m ty mm ∧ s' = sendMsgs s [mm]) :
    StepEnd c id m ents ctx s s' :=
  fun _ => ⟨fun _ => h, fun h' => absurd hst h', fun h' => absurd hst h', fun h' => absurd hst h'⟩

theorem StepEnd.hup {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hty : m.Type' = MsgHup) (hns : ¬ StaleMsg s m) (h : HupOkC c id s s') :
    StepEnd c id m ents ctx s s' :=
  fun _ => ⟨fun h' => absurd h' hns, fun _ _ => h,
    fun _ h' => absurd (hty.symm.trans h') (by simp only [MsgHup, MsgVote, ne_eq]; first | exact of_decide_eq_true rfl | word), fun _ h' => absurd hty h'⟩

theorem StepEnd.vote {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hty : m.Type' = MsgVote) (hns : ¬ StaleMsg s m)
    (h : (s.cq = true ∧ s' = s) ∨ ∃ pvs : GMap w64 Progress, VoteEnd id (preState s m pvs) m s') :
    StepEnd c id m ents ctx s s' :=
  fun _ => ⟨fun h' => absurd h' hns, fun _ h' => absurd (hty.symm.trans h') (by simp only [MsgHup, MsgVote, ne_eq]; first | exact of_decide_eq_true rfl | word),
    fun _ _ => h, fun _ _ h' => absurd hty h'⟩

theorem StepEnd.fn {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hns : ¬ StaleMsg s m) (hh : m.Type' ≠ MsgHup) (hv : m.Type' ≠ MsgVote)
    (pvs : GMap w64 Progress) (h : StepFnEnd c id (preState s m pvs) m ents ctx s') :
    StepEnd c id m ents ctx s s' :=
  fun _ => ⟨fun h' => absurd h' hns, fun _ h' => absurd h' hh, fun _ h' => absurd h' hv,
    fun _ _ _ => ⟨pvs, h⟩⟩

theorem StepFnEnd.follower {c : CfgM} {id : w64} {s1 : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} {scfg : CSLists} {sv : SnapshotM} {d : Bool} {c' : CfgM}
    (hr : s1.role = .follower) (h : FollowerStepResultC c scfg id s1 m ents sv d s' c' ctx) :
    StepFnEnd c id s1 m ents ctx s' := by
  refine ⟨fun _ => ⟨scfg, sv, d, c', h⟩, ?_, ?_⟩
  · intro h'; rcases h' with h' | h' <;> rw [hr] at h' <;> cases h'
  · intro h'; rw [hr] at h'; cases h'

theorem StepFnEnd.candidate {c : CfgM} {id : w64} {s1 : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} {scfg : CSLists} {sv : SnapshotM} {d : Bool} {c' : CfgM}
    (hr : s1.role = .candidate ∨ s1.role = .preCandidate)
    (h : CandidateStepResultC c scfg id s1 m ents sv d s' c' ctx) :
    StepFnEnd c id s1 m ents ctx s' := by
  refine ⟨?_, fun _ => ⟨scfg, sv, d, c', h⟩, ?_⟩
  · intro h'; rcases hr with hr | hr <;> rw [hr] at h' <;> cases h'
  · intro h'; rcases hr with hr | hr <;> rw [hr] at h' <;> cases h'

theorem StepFnEnd.leader {c : CfgM} {id : w64} {s1 : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {s' : NState} {d : Bool}
    (hr : s1.role = .leader) (h : LeaderStepResultC c id s1 m ents d s' ctx) :
    StepFnEnd c id s1 m ents ctx s' := by
  refine ⟨?_, ?_, fun _ => ⟨d, h⟩⟩
  · intro h'; rw [hr] at h'; cases h'
  · intro h'; rcases h' with h' | h' <;> rw [hr] at h' <;> cases h'

/-- (2026-11-11, slice 27n, Q27 (a)) **`StepEnd` of a local report** (`MsgForgetLeader`,
`MsgUnreachable`, `MsgSnapStatus`, term zero, no preamble): the step function's result at `s` for
`MsgUnreachable`, the one of the three `StepEnd` describes. -/
theorem StepEnd.localRep {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState}
    (hty : m.Type' = MsgForgetLeader ∨ m.Type' = MsgUnreachable ∨ m.Type' = MsgSnapStatus)
    (hT0 : m.Term' = W64 0) (hnbf : ¬ PreBF m s)
    (h : m.Type' = MsgUnreachable → StepFnEnd c id s m ents ctx s') :
    StepEnd c id m ents ctx s s' := by
  by_cases hu : m.Type' = MsgUnreachable
  · have hpre : preState s m s.prvals = s := by simp [preState, hnbf]
    have hh : m.Type' ≠ MsgHup := fun e => absurd (hu.symm.trans e)
      (by simp only [MsgUnreachable, MsgHup, ne_eq]; first | exact of_decide_eq_true rfl | word)
    have hv : m.Type' ≠ MsgVote := fun e => absurd (hu.symm.trans e)
      (by simp only [MsgUnreachable, MsgVote, ne_eq]; first | exact of_decide_eq_true rfl | word)
    have hns : ¬ StaleMsg s m := fun h' => h'.1 hT0
    have hfn : StepFnEnd c id (preState s m s.prvals) m ents ctx s' := by rw [hpre]; exact h hu
    exact StepEnd.fn hns hh hv s.prvals hfn
  · apply StepEnd.of_ty
    have hnf : ¬ StepEndTy MsgForgetLeader := by unfold StepEndTy; decide
    have hns : ¬ StepEndTy MsgSnapStatus := by unfold StepEndTy; decide
    rcases hty with h' | h' | h'
    · rw [h']; exact hnf
    · exact absurd h' hu
    · rw [h']; exact hns

end pure

section gates
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The caller's resources through `Step`'s gates** (see the header). (2026-11-10, slice 14) Those
`Step` may end in, and those a broadcast goes through, are indexed by the outbox (`List Msg → IProp`:
the resource at the outbox the path has queued so far, `notes/decisions.md`, "Q8 stage 1 (slice
14)"); the others are at an outbox the gates name (`G` before the receive hook, `Gf`, `Gb1`, `Gb2`,
`Gp1` between two hooks that queue nothing). -/
structure StepG (GF : BundledGFunctors) where
  G : IProp GF
  G0 : List Msg → IProp GF
  G1 : List Msg → IProp GF
  GE : List Msg → IProp GF
  Gf : IProp GF
  Gb1 : IProp GF
  Gb2 : IProp GF
  Gp1 : IProp GF
  Gp2 : List Msg → IProp GF
  Gc : Bool → w64 → List Msg → IProp GF
  /-- (2026-11-11, slice 23a) **What `Step` lends a proposal's `Replicate` gate** (`leaderGates`'
  `"Hgprep"`), for the batch: set by `Step`'s side (`ghostIn`: `propLend`, the proposal's tickets and
  entries' data and the receipt `appendEntry` raises, traced only); a caller's own resources leave it
  `emp`, and no gate reads it but `"Hgprep"` (`notes/decisions.md`, "Q8 stage 1 (slice 23a)"). -/
  Tp : List EntryM → IProp GF := fun _ => iprop(emp)
  /-- (2026-11-11, slice 25b) **What `Step` lends a won vote's empty entry's `Replicate` gate**
  (`candidateGates`' `"Hgrep"`): set by `Step`'s side (`ghostIn`: `winLend`, the receipt covering the
  entry's index, traced only); a caller's own resources leave it `emp`, and no gate reads it but
  `"Hgrep"` (`notes/decisions.md`, "Q8 stage 1 (slice 25b)"). -/
  Tw : IProp GF := iprop(emp)

/-- What `Step` gives back of the caller's resources, at the outbox `o` it ended with. -/
def stepOut (R : StepG GF) (o : List Msg) : IProp GF :=
  iprop(R.G0 o ∨ R.G1 o ∨ R.GE o ∨ R.Gp2 o ∨ ∃ (b : Bool) (N : w64), R.Gc b N o)

/-- (2026-11-11, slice 24b) **What `Step` gives back, to the closing wand** (`stepClose`): `stepOut`
with the resources before the type switch's last gate (`G0`, `G1`) guarded by `¬ CandHooked`, the
outcome `stepCandidate` tags them with: on a candidate's deciding vote response the step ends past
`"Hgbl"` or `"Hglost"`, never at `G0` or `G1`. Only the close reads it; every other user has `stepOut`
(`stepOutG_stepOut`, `stepOutG_of_ne`). (2026-11-11, slice 30c, plan Q30 (a)) And by `¬ LeadRan`: on a
leader's accepted `MsgAppResp` that reaches `maybeCommit` the step ends past `"Hgcommit"`. -/
def stepOutG (c : CfgM) (m : MessageM) (s : NState) (R : StepG GF) (o : List Msg) : IProp GF :=
  iprop((⌜¬ CandHooked c m s ∧ ¬ LeadRan m s⌝ ∗ R.G0 o) ∨
    (⌜¬ CandHooked c m s ∧ ¬ LeadRan m s⌝ ∗ R.G1 o) ∨ R.GE o ∨ R.Gp2 o ∨
    ∃ (b : Bool) (N : w64), R.Gc b N o)

/-- (2026-11-10, slice 14) **What the callees ask of the indexed resources**: untraced, those reaching
`maybeSendAppend` ignore the outbox (`IdxFree`: its snapshot fallback queues through no gate); after a
campaign, the order (`PermInv`: `campaign`'s result orders its messages its own way). An untraced
caller's constant families have both (`StepGOk.const`). -/
def StepGOk (tr : Option GName) (R : StepG GF) : Prop :=
  PermInv R.GE ∧ IdxFree tr R.G1 ∧ IdxFree tr R.GE ∧ IdxFree tr R.Gp2 ∧ ∀ b N, IdxFree tr (R.Gc b N)

/-- `raft.hup.spec`'s gates (its `"Hgbc"`, `"#Hgsend"`), at `G0` and `G`; `"Hgbc"` given the
campaign's conditions (2026-11-10, slice 19a). -/
def hupGates (c : CfgM) (r : Loc) (id : w64) (s : NState) (t : CampaignType) (G0 : IProp GF)
    (G : List Msg → IProp GF) : IProp GF :=
  iprop(
      "Hgbc" ∷ (⌜HupCampaigns c id s⌝ -∗ G0 -∗ if t = campaignPreElection then iprop(|={⊤}=> G s.outbox)
        else HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c) (G s.outbox)) ∗
      "#Hgsend" ∷ □ (∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id { campRoleState id s (decide (t = campaignPreElection)) with prvals := pvs } c
            (if y = id then vrespW32 (decide (t = campaignPreElection))
             else vreqW32 (decide (t = campaignPreElection)))
            [campMsg (decide (t = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx t) y])
          (G (o ++ [campMsg (decide (t = campaignPreElection)) id (s.term + W64 1)
              (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents)) (transferCtx t) y]))))

/-- `stepFollower.spec`'s gates, at `G` and `G'` (2026-11-10, slice 14: indexed by the outbox). -/
def followerGates (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (cl : List w8) (G G' : List Msg → IProp GF) : IProp GF :=
  iprop(
      "Hgapp" ∷ (⌜m.Type' = MsgApp⌝ -∗ ∀ (s1 : NState) (mm : Msg),
        ⌜HandleAppResult id { s with lead := m.From' } m ents (sendMsgs s1 [mm])⌝ -∗
        G s.outbox -∗ HookGateOpt s.gh.tr r (sendOutGate id s1 c MsgAppResp [mm])
          (G' (sendMsgs s1 [mm]).outbox)) ∗
      -- a `MsgHeartbeat`: `handleHeartbeat`'s, at that state with the commit moved
      "Hghb" ∷ (⌜m.Type' = MsgHeartbeat⌝ -∗ G s.outbox -∗ HookGateOpt s.gh.tr r
        (sendOutGate id { ({ s with lead := m.From' } : NState) with
            logst := { s.logst with committed := plogCommitTo s.logst.committed m.Commit' } }
          c MsgHeartbeatResp [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }])
        (G' (s.outbox ++ [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }]))) ∗
      -- a forward to the leader: the send's gate, at no event (none of the three types is traced),
      -- whatever untraced messages it queues
      "Hgfwd" ∷ (⌜m.Type' = MsgProp ∨ m.Type' = MsgReadIndex ∨ m.Type' = MsgTransferLeader⌝ -∗
        ∀ out : List Msg, ⌜∀ x ∈ out, x.ty.traced = false⌝ -∗ G s.outbox -∗
        HookGateOpt s.gh.tr r none (G (s.outbox ++ out))) ∗
      -- a `MsgTimeoutNow`: `hup(campaignTransfer)`'s gates (the `BecomeCandidate` line, then each
      -- vote message, at the candidate's state)
      "Hgcamp" ∷ (⌜m.Type' = MsgTimeoutNow⌝ -∗ G s.outbox -∗
        HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id s) c) (G' s.outbox)) ∗
      "#Hgvote" ∷ □ (⌜m.Type' = MsgTimeoutNow⌝ -∗
        ∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ G' o -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id { becomeCandidate id s with prvals := pvs } c
            (if y = id then vrespW32 false else vreqW32 false)
            [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
              campaignTransfer y])
          (G' (o ++ [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
              campaignTransfer y]))))

/-- `stepCandidate.spec`'s gates, at `G`, `G'`, `Gf`, `G1`, `G2` (2026-11-10, slice 14: `G`, `G'` indexed
by the outbox). -/
def candidateGates (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (cl : List w8) (G G' : List Msg → IProp GF) (Gf G1 G2 : IProp GF) (Tw : IProp GF) : IProp GF :=
  iprop(
      "Hgbf" ∷ (⌜m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat⌝ -∗ G s.outbox -∗
        HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower s s.term m.From') c) Gf) ∗
      "Hgapp" ∷ (⌜m.Type' = MsgApp⌝ -∗ ∀ (pvs : GMap w64 Progress) (s1 : NState) (mm : Msg),
        ⌜HandleAppResult id { becomeFollower s s.term m.From' with prvals := pvs } m ents
          (sendMsgs s1 [mm])⌝ -∗
        Gf -∗ HookGateOpt s.gh.tr r (sendOutGate id s1 c MsgAppResp [mm]) (G' (sendMsgs s1 [mm]).outbox)) ∗
      "Hghb" ∷ (⌜m.Type' = MsgHeartbeat⌝ -∗ ∀ (pvs : GMap w64 Progress),
        Gf -∗ HookGateOpt s.gh.tr r
          (sendOutGate id { ({ becomeFollower s s.term m.From' with prvals := pvs } : NState) with
              logst := { s.logst with committed := plogCommitTo s.logst.committed m.Commit' } }
            c MsgHeartbeatResp [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }])
          (G' (s.outbox ++ [{ Msg.plain .heartbeatResp id m.From' s.term false with ctx := cl }]))) ∗
      "Hgbl" ∷ (⌜m.Type' = MsgVoteResp ∧ s.role = .candidate ∧
          JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))⌝ -∗ G s.outbox -∗
        HookGate s.gh.tr r (NodeEvOf (W64 3) id (becomeLeaderPre id { s with votes := recordVote s.votes m.From' (!m.Reject') }) c) G1) ∗
      -- (2026-11-11, slice 25b) with what `Step` lends it (`Tw`: `StepG.Tw`), on the win
      "Hgrep" ∷ (⌜m.Type' = MsgVoteResp ∧ s.role = .candidate ∧
          JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))⌝ -∗ Tw -∗
        G1 -∗ HookGateN s.gh.tr r (NodeEvOf (W64 5) id (becomeLeaderPre id { s with votes := recordVote s.votes m.From' (!m.Reject') }) c) 1 G2) ∗
      "Hgack" ∷ (G2 -∗ HookGateOpt s.gh.tr r (sendOutGate id (becomeLeaderLog id { s with votes := recordVote s.votes m.From' (!m.Reject') }) c MsgAppResp
          [selfAck id (becomeLeaderLog id { s with votes := recordVote s.votes m.From' (!m.Reject') })])
        (G' (s.outbox ++ [selfAck id (becomeLeaderLog id { s with votes := recordVote s.votes m.From' (!m.Reject') })]))) ∗
      "#Hgcast" ∷ □ (⌜m.Type' = MsgVoteResp ∧ s.role = .candidate ∧
          JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))⌝ -∗
        ∀ (pvs : GMap w64 Progress) (to : w64) (mm : Msg) (o : List Msg),
        ⌜to ≠ id ∧ to ∈ domSet ({ becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs } : NState).progress⌝ -∗
        ⌜AppOk id (toPState { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs }) mm ∧
          mm.commit = (toPState { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs }).commit ∧ mm.dst = to ∧
          uint.Z ((prvalsMatch pvs !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0⌝ -∗
        G' o -∗
        HookGateOpt s.gh.tr r (sendOutGate id { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs } c MsgApp [mm])
          (G' (o ++ [mm]))) ∗
      "#Hnosnap" ∷ TrNoSnap s.gh.tr s.logst ∗
      "Hgcamp" ∷ (⌜m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate ∧
          JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))⌝ -∗ G s.outbox -∗
        HookGate s.gh.tr r (NodeEvOf (W64 1) id (becomeCandidate id { s with votes := recordVote s.votes m.From' (!m.Reject') }) c) (G' s.outbox)) ∗
      "#Hgvote" ∷ □ (⌜m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate ∧
          JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))⌝ -∗
        ∀ (pvs : GMap w64 Progress) (y : w64) (o : List Msg), ⌜y ∈ c.voters⌝ -∗ G' o -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id { becomeCandidate id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs } c
            (if y = id then vrespW32 false else vreqW32 false)
            [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
              [] y])
          (G' (o ++ [campMsg false id (s.term + W64 1) (plogLast s.logst.prev (s.logst.sents ++ s.logst.uents))
              [] y]))) ∗
      "Hglost" ∷ (⌜(m.Type' = MsgVoteResp ∧ s.role = .candidate ∨
            m.Type' = MsgPreVoteResp ∧ s.role = .preCandidate) ∧
          JLost c (recordVote s.votes m.From' (!m.Reject'))⌝ -∗ G s.outbox -∗
        HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower { s with votes := recordVote s.votes m.From' (!m.Reject') } s.term (W64 0)) c) (G' s.outbox)))

/-- `stepLeader.spec`'s gates, at `G`, `G'`, `Gp1`, `Gp2`, `Gc` (2026-11-10, slice 14: all but `Gp1` indexed
by the outbox). -/
def leaderGates (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (Tp : IProp GF) (G G' : List Msg → IProp GF) (Gp1 : IProp GF) (Gp2 : List Msg → IProp GF)
    (Gc : Bool → w64 → List Msg → IProp GF) : IProp GF :=
  iprop(
      "#Hgbeat" ∷ □ (⌜m.Type' = MsgBeat⌝ -∗ ∀ (to cm : w64) (o : List Msg), ⌜to ≠ id ∧ to ∈ domSet s.progress⌝ -∗
          ⌜uint.Z cm = min (uint.Z s.logst.committed)
            (uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)))⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r (sendOutGate id s c MsgHeartbeat
          [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] (hbCtx s.rd.ro)])
          (G (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] (hbCtx s.rd.ro)]))) ∗
      "Hgriresp" ∷ (⌜m.Type' = MsgReadIndex⌝ -∗ ⌜CfgSingle c id⌝ -∗ ∀ (mm : Msg) (o : List Msg),
        ⌜mm.ty = .readIndexResp⌝ -∗ G o -∗ HookGateOpt s.gh.tr r none (G (o ++ [mm]))) ∗
      "#Hgrihb" ∷ □ (⌜m.Type' = MsgReadIndex⌝ -∗ ⌜¬ CfgSingle c id⌝ -∗
        ∀ (to cm : w64) (o : List Msg), ⌜to ≠ id ∧ to ∈ domSet s.progress⌝ -∗
          ⌜uint.Z cm = min (uint.Z s.logst.committed)
            (uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)))⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r (sendOutGate id (arriveState id s m ents) c MsgHeartbeat
          [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] []
            (hbCtx (readonlyAdd s.rd.ro (arriveReq s m ents)))])
          (G (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] []
            (hbCtx (readonlyAdd s.rd.ro (arriveReq s m ents)))]))) ∗
      "Hgtnow" ∷ (⌜m.Type' = MsgTransferLeader⌝ -∗ ∀ o : List Msg, G o -∗ HookGateOpt s.gh.tr r none (G o)) ∗
      "Hgxapp" ∷ (⌜m.Type' = MsgTransferLeader⌝ -∗ ∀ (mm : Msg) (o : List Msg),
          ⌜AppOk id (toPState s) mm ∧ mm.commit = (toPState s).commit ∧ mm.dst = m.From' ∧
            uint.Z ((prvalsMatch s.prvals !! m.From').getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r (sendOutGate id { s with lt := m.From' } c MsgApp [mm]) (G (o ++ [mm]))) ∗
      "#Hnosnap" ∷ TrNoSnap s.gh.tr s.logst ∗
      "Hgcq" ∷ (⌜m.Type' = MsgCheckQuorum⌝ -∗ G s.outbox -∗
        HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower s s.term (W64 0)) c) (G' s.outbox)) ∗
      -- (2026-11-11, slice 23a) with what `Step` lends it (`Tp`: `StepG.Tp`)
      "Hgprep" ∷ (⌜m.Type' = MsgProp⌝ -∗ ∀ cs, ccEntsOk ents cs -∗ Tp -∗ G s.outbox -∗
        HookGateN s.gh.tr r (NodeEvOf (W64 5) id s c)
          (normalCount (leaderPropConf s ents cs c.joint).1) Gp1) ∗
      "Hgpack" ∷ (⌜m.Type' = MsgProp⌝ -∗ ∀ cs, ccEntsOk ents cs -∗ Gp1 -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id (propAppended s (leaderPropConf s ents cs c.joint).1) c MsgAppResp
            [selfAck id (propAppended s (leaderPropConf s ents cs c.joint).1)])
          (Gp2 (s.outbox ++ [selfAck id (propAppended s (leaderPropConf s ents cs c.joint).1)]))) ∗
      "#Hgpapp" ∷ □ (⌜m.Type' = MsgProp⌝ -∗ ∀ cs (to : w64) (mm : Msg) (o : List Msg), ccEntsOk ents cs -∗
        ⌜to ≠ id ∧ to ∈ domSet s.progress⌝ -∗
        ⌜AppOk id (toPState (propAppended s (leaderPropConf s ents cs c.joint).1)) mm ∧
          mm.commit = s.logst.committed ∧ mm.dst = to ∧
          uint.Z ((prvalsMatch s.prvals !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0⌝ -∗ Gp2 o -∗
        HookGateOpt s.gh.tr r
          (sendOutGate id (propAppended s (leaderPropConf s ents cs c.joint).1) c MsgApp [mm]) (Gp2 (o ++ [mm]))) ∗
      "Hgsapp" ∷ (⌜m.Type' = MsgHeartbeatResp ∨ (m.Type' = MsgAppResp ∧ m.Reject' = true)⌝ -∗
        ∀ (mm : Msg) (o : List Msg), ⌜AppOk id (toPState s) mm ∧ mm.commit = s.logst.committed ∧
          mm.dst = m.From' ∧ uint.Z ((prvalsMatch s.prvals !! m.From').getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0⌝ -∗ G o -∗
        HookGateOpt s.gh.tr r (sendOutGate id s c MsgApp [mm]) (G (o ++ [mm]))) ∗
      "#Hghresp" ∷ □ (⌜m.Type' = MsgHeartbeatResp⌝ -∗ ∀ (mm : Msg) (o : List Msg),
        ⌜mm.ty = .readIndexResp⌝ -∗ G o -∗ HookGateOpt s.gh.tr r none (G (o ++ [mm]))) ∗
      "Hgcommit" ∷ (⌜m.Type' = MsgAppResp ∧ m.Reject' = false⌝ -∗ ⌜AppRespRan s m.From' m.Index'⌝ -∗
        ∀ (pvs : GMap w64 Progress) (b : Bool) (N : w64),
        ⌜prvalsMatch pvs = appRespMatch s m.From' m.Index'⌝ -∗
        ⌜maybeCommitOut c { s with prvals := pvs } b N⌝ -∗ £ 1 -∗ G s.outbox -∗
        HookGate s.gh.tr r (NodeEvOf rsmCommit id (commitAt s b N) c) (Gc b N s.outbox)) ∗
      "#Hgrlresp" ∷ □ (⌜m.Type' = MsgAppResp ∧ m.Reject' = false⌝ -∗ ∀ (N : w64) (mm : Msg) (o : List Msg),
        ⌜CfgSingle c id⌝ -∗ ⌜mm.ty = .readIndexResp⌝ -∗
        Gc true N o -∗ HookGateOpt s.gh.tr r none (Gc true N (o ++ [mm]))) ∗
      "#Hgrlhb" ∷ □ (⌜m.Type' = MsgAppResp ∧ m.Reject' = false⌝ -∗ ⌜¬ CfgSingle c id⌝ -∗
        ∀ (N : w64) (k : Nat) (to cm : w64) (o : List Msg), ⌜0 < k ∧ k ≤ s.rd.pend.length⌝ -∗
        ⌜to ≠ id ∧ to ∈ domSet s.progress⌝ -∗
        ⌜uint.Z cm = min (uint.Z N)
          (uint.Z ((appRespMatch s m.From' m.Index' !! to).getD (W64 0)))⌝ -∗ Gc true N o -∗
        HookGateOpt s.gh.tr r (sendOutGate id (commitAt s true N) c MsgHeartbeat
          [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] []
            (hbCtx (readonlyRelease s.rd.ro id N (s.rd.pend.take k)))])
          (Gc true N (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] []
            (hbCtx (readonlyRelease s.rd.ro id N (s.rd.pend.take k)))]))) ∗
      "#Hgaapp" ∷ □ (⌜m.Type' = MsgAppResp ∧ m.Reject' = false⌝ -∗
        ∀ (b : Bool) (N to : w64) (mm : Msg) (o : List Msg), ⌜to ≠ id ∧ to ∈ domSet s.progress⌝ -∗
        ⌜AppOk id (toPState (commitAt s b N)) mm ∧ mm.commit = (commitAt s b N).logst.committed ∧
          mm.dst = to ∧ uint.Z ((appRespMatch s m.From' m.Index' !! to).getD (W64 0)) ≤ uint.Z mm.index ∧ mm.rejecthint = W64 0⌝ -∗ Gc b N o -∗
        HookGateOpt s.gh.tr r (sendOutGate id (commitAt s b N) c MsgApp [mm]) (Gc b N (o ++ [mm]))) ∗
      "#Hgatnow" ∷ □ (⌜m.Type' = MsgAppResp ∧ m.Reject' = false⌝ -∗ ∀ (b : Bool) (N : w64) (o : List Msg),
        Gc b N o -∗ HookGateOpt s.gh.tr r none (Gc b N o)))

/-- The term preamble's gate, for a message not stale: the step-down's `BecomeFollower` line when it
runs (`PreBF`), else an update; `G0` to `G1`. -/
def preGate (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (G0 G1 : List Msg → IProp GF) :
    IProp GF :=
  iprop(⌜m.Term' = W64 0 ∨ uint.Z s.term ≤ uint.Z m.Term'⌝ -∗ G0 s.outbox -∗
    if PreBF m s then HookGate s.gh.tr r (NodeEvOf (W64 2) id (becomeFollower s m.Term' (preLead m)) c) (G1 s.outbox)
    else iprop(|={⊤}=> G1 s.outbox))

/-- The role's step function's gates, at the state after the preamble (its `Progress` map `pvs`). -/
def stepFnGates (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (ctx : List w8) (R : StepG GF) : IProp GF :=
  iprop(∀ pvs : GMap w64 Progress,
    (⌜(preState s m pvs).role = .follower⌝ -∗
      followerGates c r id (preState s m pvs) m ents ctx R.G1 R.GE) ∧
    (⌜(preState s m pvs).role = .candidate ∨ (preState s m pvs).role = .preCandidate⌝ -∗
      candidateGates c r id (preState s m pvs) m ents ctx R.G1 R.GE R.Gf R.Gb1 R.Gb2 R.Tw) ∧
    (⌜(preState s m pvs).role = .leader⌝ -∗
      leaderGates c r id (preState s m pvs) m ents (R.Tp ents) R.G1 R.GE R.Gp1 R.Gp2 R.Gc))

/-- **`raft.Step`'s gates** (see the header), at the caller's resources `R`. -/
def stepGates (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM) (ents : List EntryM)
    (sn : Option SnapshotM) (ctx : List w8) (rs : List Loc) (R : StepG GF) : IProp GF :=
  iprop(
      -- the receive hook, at `s`: the receipt's event (`recvGate`; none for a type not traced)
      "Hgrecv" ∷ (R.G -∗ HookGateOpt s.gh.tr r (recvGate id s c ⟨m, ents, sn, ctx, rs⟩) (R.G0 s.outbox)) ∗
      -- the term preamble of a message not stale: the step-down's `BecomeFollower` line when it runs
      -- (`PreBF`), else an update; the type switch starts from `G1`
      "Hgpre" ∷ preGate c r id s m R.G0 R.G1 ∗
      -- a stale message's answer, at `s`
      "Hglow" ∷ (⌜m.Term' ≠ W64 0 ∧ uint.Z m.Term' < uint.Z s.term⌝ -∗ ∀ (ty : w32) (mm : Msg),
        ⌜LowSend id s m ty mm⌝ -∗ R.G0 s.outbox -∗ HookGateOpt s.gh.tr r (sendOutGate id s c ty [mm])
          (R.GE (s.outbox ++ [mm]))) ∗
      -- a vote request's answer, at the state after the preamble
      "Hgvresp" ∷ (⌜m.Type' = MsgVote ∨ m.Type' = MsgPreVote⌝ -∗ ∀ (pvs : GMap w64 Progress) (rej : Bool),
        R.G1 s.outbox -∗ HookGateOpt s.gh.tr r
          (sendOutGate id (preState s m pvs) c (vrespTyOf m) [vrespMsgOf id (preState s m pvs) m rej])
          (R.GE (s.outbox ++ [vrespMsgOf id (preState s m pvs) m rej]))) ∗
      -- a `MsgHup`'s campaign (`hup`'s gates, at `s`)
      "Hghup" ∷ (⌜m.Type' = MsgHup⌝ -∗ hupGates c r id s (hupType s) (R.G1 s.outbox) R.GE) ∗
      -- the role's step function's gates, at the state after the preamble
      "Hgstep" ∷ stepFnGates c r id s m ents ctx R ∗
      -- (2026-11-10, slice 14) what the callees ask of the indexed resources
      "%Hgok" ∷ ⌜StepGOk s.gh.tr R⌝)

end gates

section outg
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] {GF : BundledGFunctors}

/-- (slice 24b) The guarded result is one. -/
theorem stepOutG_stepOut (c : CfgM) (m : MessageM) (s : NState) (R : StepG GF) {o : List Msg} :
    stepOutG c m s R o ⊢ stepOut R o := by
  unfold stepOutG
  iintro (⟨-, H⟩ | ⟨-, H⟩ | H | H | ⟨%b, %N, H⟩)
  · unfold stepOut; ileft; iexact H
  · unfold stepOut; iright; ileft; iexact H
  · unfold stepOut; iright; iright; ileft; iexact H
  · unfold stepOut; iright; iright; iright; ileft; iexact H
  · unfold stepOut; iright; iright; iright; iright; iexists b, N; iexact H

/-- (slice 24b) A result off a deciding vote response (slice 30c: and off a leader's accepted
`MsgAppResp` reaching `maybeCommit`) is a guarded one. -/
theorem stepOutG_of_not (c : CfgM) (m : MessageM) (s : NState) (R : StepG GF) {o : List Msg}
    (h : ¬ CandHooked c m s) (hl : ¬ LeadRan m s) : stepOut R o ⊢ stepOutG c m s R o := by
  unfold stepOut stepOutG
  iintro (H | H | H | H | ⟨%b, %N, H⟩)
  · ileft; iframe H; ipureintro; exact ⟨h, hl⟩
  · iright; ileft; iframe H; ipureintro; exact ⟨h, hl⟩
  · iright; iright; ileft; iexact H
  · iright; iright; iright; ileft; iexact H
  · iright; iright; iright; iright; iexists b, N; iexact H

theorem stepOutG_of_ne (c : CfgM) (m : MessageM) (s : NState) (R : StepG GF) {o : List Msg}
    (h : m.Type' ≠ MsgVoteResp) (ha : m.Type' ≠ MsgAppResp) : stepOut R o ⊢ stepOutG c m s R o :=
  stepOutG_of_not c m s R (CandHooked.of_ne h) (LeadRan.of_ne ha)

end outg

section closemid
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- (2026-11-11, slice 23a) **The end states the closing wand may give raft's ghost state back past `s`**
(`stepClose`'s second disjunct, `CloseMid`): on a leader's `MsgProp` of no configuration change, the
proposed state (`proposed id s ents`: the batch appended, the self-acknowledgement queued), the step's
end state past its append (its log the proposed state's); `Step` then steps the rest (the broadcast).
(2026-11-11, slice 25b) Or on a candidate's `MsgVoteResp` of its term, the won state (`becomeLeader`
after the tally: the empty entry appended, the self-acknowledgement queued, at a `Progress` map of
`reset`'s `Match` values), the step's end state past it (its log the won state's: the election won);
`Step` then steps the broadcast (`notes/decisions.md`, "Q8 stage 1 (slice 25b)"). (2026-11-11, slice 28c)
Or on a leader's accepted `MsgAppResp` of its term, the state after `maybeCommit` (the sender's `Match`
raised as `MaybeUpdate` raises it, at a `Progress` map `pvs` of `appRespMatch`'s `Match` values, then the
commit index at an outcome `(b, N)`), the step's end state past it (its log the committed state's: the
commit index the outcome's); `Step` then steps the release and the appends (`notes/decisions.md`, "Q8
stage 1 (slice 28c)"). -/
def CloseMid (id : w64) (m : MessageM) (ents : List EntryM) (s s1 s' : NState) : Prop :=
  (m.Type' = MsgProp ∧ s.role = .leader ∧ (∀ e ∈ ents, ¬ IsConfEnt e) ∧
    s1 = proposed id s ents ∧ s1.logst = s'.logst) ∨
  (m.Type' = MsgVoteResp ∧ s.role = .candidate ∧ m.Term' = s.term ∧
    ∃ pvs : GMap w64 Progress, prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals ∧
      s1 = { becomeLeader id { s with votes := recordVote s.votes m.From' (!m.Reject') } with prvals := pvs } ∧
      s1.logst = s'.logst) ∨
  (m.Type' = MsgAppResp ∧ s.role = .leader ∧ m.Term' = s.term ∧ m.Reject' = false ∧
    m.From' ∈ domSet s.progress ∧ ∃ (pvs : GMap w64 Progress) (b : Bool) (N : w64), prvalsMatch pvs = appRespMatch s m.From' m.Index' ∧
      s1 = commitAt { s with prvals := pvs } b N ∧ s1.logst = s'.logst)

theorem CloseMid.ty {id : w64} {m : MessageM} {ents : List EntryM} {s s1 s' : NState}
    (h : CloseMid id m ents s s1 s') :
    m.Type' = MsgProp ∨ m.Type' = MsgVoteResp ∨ m.Type' = MsgAppResp :=
  h.elim (fun h => .inl h.1) (fun h => h.elim (fun h => .inr (.inl h.1)) (fun h => .inr (.inr h.1)))

/-- (slice 25b) A close of another type than `MsgProp` and `MsgVoteResp` ((slice 28c) and `MsgAppResp`)
is none past `s`. -/
theorem CloseMid.not_of {id : w64} {m : MessageM} {ents : List EntryM} {s s1 s' : NState}
    (hnp : m.Type' ≠ MsgProp) (hnv : m.Type' ≠ MsgVoteResp) (hna : m.Type' ≠ MsgAppResp) :
    ¬ CloseMid id m ents s s1 s' :=
  fun h => h.ty.elim hnp (fun h => h.elim hnv hna)

/-- (slice 25b) A proposal's close past `s` (the `MsgProp` case). -/
theorem CloseMid.prop {id : w64} {m : MessageM} {ents : List EntryM} {s s1 s' : NState}
    (h : m.Type' = MsgProp ∧ s.role = .leader ∧ (∀ e ∈ ents, ¬ IsConfEnt e) ∧
      s1 = proposed id s ents ∧ s1.logst = s'.logst) : CloseMid id m ents s s1 s' := .inl h

end closemid

section close
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- (2026-11-11, slice 23a) **What `Step` lends a traced proposal's `Replicate` gate** (`StepG.Tp`,
`leaderGates`' `"Hgprep"`): the batch's tickets (`entTk`) and its entries' data (`propData`, from the
proposal's `isMessage`), and the receipt `appendEntry` raises before the line (`⧖`, one step per entry
past the log's last index's), which the propose ghost update (`ownRaftGhost_step_propose`) consumes:
a traced caller's family moves raft's ghost state to the proposed state inside the gate, before the lines
whose facts read the new entries' records. Nothing untraced: `Step` keeps them for its own single ghost
step. -/
def propLend (γ : RaftNames) (s : NState) (ents : List EntryM) : IProp GF :=
  if s.gh.tr.isSome then
    iprop(([∗list] e ∈ ents, propData γ e) ∗ ([∗list] e ∈ ents, entTk γ e) ∗
      ⧖ ((plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length + ents.length))
  else iprop(emp)

/-- (2026-11-11, slice 25b) **What `Step` lends a traced won vote's empty entry's `Replicate` gate**
(`StepG.Tw`, `candidateGates`' `"Hgrep"`): the receipt covering the entry's index (the log's last index
plus one), which `becomeLeader`'s `appendEntry` raises before the line; the win's last ghost phase
(`ownRaftGhost_step_win_entry`) consumes it there, before the broadcast's lines whose facts read the
entry's record. Nothing untraced. (2026-11-11, slice 27b) And the node's membership of its own
`Progress` map (`reset`'s `Match` values then a `LeaderMatchOk`, which the won state's ghost needs),
which `Step` knows from the tracker and the family does not. -/
def winLend (γ : RaftNames) (id : w64) (s : NState) : IProp GF :=
  if s.gh.tr.isSome then
    iprop(⌜id ∈ domSet s.prvals⌝ ∗ ⧖ ((plogLastIndexZ (toPState s).base (toPState s).log).toNat - γ.reBoot.length + 1))
  else iprop(emp)

/-- (2026-11-11, slice 23a) **The closing wand's ghost state back at `s`** (`stepClose`'s first
disjunct, `CloseAt`): on a traced leader's `MsgProp` of no configuration change, only when the batch was
not appended (`Step` lent the proposal's tickets to the `Replicate` gate, `propLend`, so it can step from
`s` only by the proposal's drop). Vacuous on any other type (`CloseAt.of_ne`) or untraced
(`CloseAt.of_none`). -/
def CloseAt (id : w64) (m : MessageM) (ents : List EntryM) (s s' : NState) : Prop :=
  s.gh.tr.isSome → m.Type' = MsgProp → s.role = .leader → (∀ e ∈ ents, ¬ IsConfEnt e) →
    (proposed id s ents).logst ≠ s'.logst

theorem CloseAt.of_ne {id : w64} {m : MessageM} {ents : List EntryM} {s s' : NState}
    (h : m.Type' ≠ MsgProp) : CloseAt id m ents s s' := fun _ h' => absurd h' h

theorem CloseAt.of_none {id : w64} {m : MessageM} {ents : List EntryM} {s s' : NState}
    (h : s.gh.tr = none) : CloseAt id m ents s s' := fun h' => by rw [h] at h'; cases h'

theorem CloseAt.of_notLeader {id : w64} {m : MessageM} {ents : List EntryM} {s s' : NState}
    (h : s.role ≠ .leader) : CloseAt id m ents s s' := fun _ _ h' => absurd h' h

/-- A message of a traced type is no proposal. -/
theorem CloseAt.of_traced {id : w64} {m : MessageM} {ents : List EntryM} {s s' : NState} {ty : MsgType}
    (h : mtypeOf m.Type' = some ty) (ht : ty.traced = true) : CloseAt id m ents s s' := by
  intro _ hp
  rw [hp] at h
  have : mtypeOf MsgProp = some .propose := rfl
  rw [this] at h
  cases h
  cases ht

/-- The caller's resources with raft's ghost state put into the first (the receive hook's gate's
argument): `raft.Step.spec`'s gates take the ghost state from `Step` there. -/
def ghostIn (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (s : NState) (R : StepG GF) : StepG GF :=
  { R with G := iprop(ownStepGhost γ md c id s ∗ R.G), Tp := propLend γ s, Tw := winLend γ id s }

/-- **Raft's ghost state, given back to `Step`** by the caller from whichever resource the path ended
in (`stepOut R`), with the caller's own `Gout` at the step's end state `s'` (2026-11-10, slice 12: the
state `Step` returns, so that a caller's resources can follow it), and (traced) the step's new
messages' numbers (`OutTrStep`, `NsLink`'s `OutTr`), for any end state of a step from `s` in the model
(`StepCD`) that is (traced; 2026-11-10, slice 13) the code's end state on the message's path
(`StepEnd`, on the types a traced node steps: what the gates' resources predicted). (2026-11-11, slice
23a) Raft's ghost state comes back at `s` (`CloseAt`: on a traced leader's proposal, only if it was
not appended), or past it (`CloseMid`: on a leader's `MsgProp`, at the proposed state, which a traced
family reaches inside the `Replicate` gate with what `Step` lends it, `propLend`); `Step` then steps from
there. A close site of any other type gives the first (`CloseAt.of_ne`) and `Step` refutes the second
by the type (`CloseMid.ty`). -/
def stepClose (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM) (ents : List EntryM)
    (ctx : List w8) (s : NState) (R : StepG GF) (Gout : NState → IProp GF) : IProp GF :=
  iprop(∀ (s' : NState) (B : Int) (recv : List Msg),
    ⌜s.gh.tr.isSome → StepCD c id B m s recv s'⌝ -∗ ⌜s.gh.tr.isSome → StepEnd c id m ents ctx s s'⌝ -∗
    ⌜s.gh.tr.isSome → AckEnd m s s'⌝ -∗
    stepOutG c m s R s'.outbox -∗
    |={⊤}=> ((⌜CloseAt id m ents s s'⌝ ∗ ownStepGhost γ md c id s) ∨
        ∃ s1, ⌜CloseMid id m ents s s1 s'⌝ ∗ ownStepGhost γ md c id s1) ∗
      Gout s' ∗ ⌜OutTrStep s s'⌝)

/-- (2026-11-11, slice 23a) **A close giving raft's ghost state back at `s`** (`stepClose` before slice
23a): what a path of another type than `MsgProp` proves; `stepClose_of_at` turns it into `stepClose`. -/
def stepCloseAt (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM) (ents : List EntryM)
    (ctx : List w8) (s : NState) (R : StepG GF) (Gout : NState → IProp GF) : IProp GF :=
  iprop(∀ (s' : NState) (B : Int) (recv : List Msg),
    ⌜s.gh.tr.isSome → StepCD c id B m s recv s'⌝ -∗ ⌜s.gh.tr.isSome → StepEnd c id m ents ctx s s'⌝ -∗
    ⌜s.gh.tr.isSome → AckEnd m s s'⌝ -∗
    stepOut R s'.outbox -∗
    |={⊤}=> ownStepGhost γ md c id s ∗ Gout s' ∗ ⌜OutTrStep s s'⌝)

/-- A close site of another path than a traced leader's proposal (slice 23a's mechanical change): its
close at `s` (`h`: `CloseAt.of_ne`, `CloseAt.of_notLeader`, `CloseAt.of_traced`). -/
theorem stepClose_of_at (γ : RaftNames) (md : GMode) (c : CfgM) (id : w64) (m : MessageM)
    (ents : List EntryM) (ctx : List w8) (s : NState) (R : StepG GF) (Gout : NState → IProp GF)
    (h : ∀ s', CloseAt id m ents s s') :
    stepCloseAt γ md c id m ents ctx s R Gout ⊢ stepClose γ md c id m ents ctx s R Gout := by
  iintro H
  unfold stepClose stepCloseAt
  iintro %s' %B %recv %h1 %h2 %h3 Hout
  ihave Hout := stepOutG_stepOut c m s R $$ Hout
  imod H $$ %s' %B %recv %h1 %h2 %h3 Hout with ⟨Hg, HG, %Hot⟩
  imodintro
  iframe HG
  isplitl [Hg]
  · ileft; iframe Hg; ipureintro; exact h s'
  ipureintro; exact Hot

end close

end EtcdGrove
end Perennial
