/-
Lean-first (no Rocq counterpart). Q8 stage 1, slice 2 (2026-11-09): the S5 Draft's traced hook
statements (`TracedHooksDraft.lean`, frozen at tag `trace-check-frozen`) from the hooks' specs, which
are one spec for both modes (the gate `trOwn`, `TraceFire` at the node's mode): each `X.tracedSpec`
follows from `X.spec` by putting raft's state under the gate and taking it back (`trOwn_split`;
`traceInitState`'s lending form by `trOwn_wand`). (Slice 3, 2026-11-09) `traceCommit.tracedSpec`, stated on
the capability `trCapB`: from `traceCommit.spec` and the law `trCap_fire_any`, the `Commit` line's phase
step from the specification's `AdvanceCommitIndex` (`phaseStepB_commit`, `lineEffect_commit`). Not here:
`raft.maybeCommit.tracedSpec` (its `Commit` line's facts are proved inside it, which needs
`QuorumLogInv` at the raised commit: the Draft's blocker; `raft.maybeCommit.spec` takes them from its
caller), the message hooks and `raft.send` (Q9, and `send`'s accessor), and `traceConfChangeEvent` (its
spec is the untraced one still).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedHooksDraft
public import Spec.go_etcd_io.raft.v3.traceSendMessage
public import Spec.go_etcd_io.raft.v3.traceReceiveMessage
public import Spec.go_etcd_io.raft.v3.traceInitState
public import Proof.go_etcd_io.raft.v3.TracedHooksGlobal
public import Spec.go_etcd_io.raft.v3.raft__becomeCandidate
public import Spec.go_etcd_io.raft.v3.raft__becomeFollower
public import Proof.go_etcd_io.raft.v3.TracedMsg
public import Proof.go_etcd_io.raft.v3.TracedSend
public import Spec.go_etcd_io.raft.v3.raft__appendEntry
public import Spec.go_etcd_io.raft.v3.raft__becomeLeader

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

theorem traceNodeEvent.tracedSpec_of_spec (h : traceNodeEvent.spec (GF := GF) (hG := hG)) :
    traceNodeEvent.tracedSpec (GF := GF) (hG := hG) := by
  intro evt c r id s tl Q Hevt
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h evt c r id s tl Q Hevt $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceBecomeFollower.tracedSpec_of_spec (h : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    traceBecomeFollower.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceBecomeCandidate.tracedSpec_of_spec (h : traceBecomeCandidate.spec (GF := GF) (hG := hG)) :
    traceBecomeCandidate.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceBecomeLeader.tracedSpec_of_spec (h : traceBecomeLeader.spec (GF := GF) (hG := hG)) :
    traceBecomeLeader.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceReady.tracedSpec_of_spec (h : traceReady.spec (GF := GF) (hG := hG)) :
    traceReady.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl Q $$ [$Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

theorem traceReplicate.tracedSpec_of_spec (h : traceReplicate.spec (GF := GF) (hG := hG)) :
    traceReplicate.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s es dq ents tl Q
  iintro %Φ ⟨#Hpkg, Hes, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s es dq ents tl Q $$ [$Hes $Hpkg $Htl $Hown $Hfire]
  inext
  iintro ⟨Hes, Hown, HQ⟩
  iapply HΦ
  iframe Hes HQ
  iapply Hback $$ Hown

theorem traceInitState.tracedSpec_of_spec (h : traceInitState.spec (GF := GF) (hG := hG)) :
    traceInitState.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s tl Q
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hfire⟩ HΦ
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h r tl s.gh.tr (NodeEvOf (W64 0) id s c) Q (ownRaftPhysCV c c.voters r id s)
    $$ [$Hpkg $Htl Hown $Hfire]
  · iapply trOwn_wand
    iframe Hown
    iintro Hp
    iexists c, id, s
    iframe Hp
    isplitr
    · ipureintro; exact ⟨rfl, fun _ h => h⟩
    iintro Hp; iexact Hp
  inext
  iintro ⟨Hown, HQ⟩
  iapply HΦ
  iframe HQ
  iapply Hback $$ Hown

/-! ### (Q8 stage 1, slice 4) The message hooks -/

/-- A struct's logger field, untraced: nil. -/
theorem traceLogger_none_ok (c : CfgM) (r : Loc) (id : w64) (s : NState) (tl : GoInterface) :
    (r.[raft, go!"traceLogger"] ↦□ tl ∗ ownRaftPhysCV c c.voters r id s : IProp GF) ⊢
      ⌜s.gh.tr = none → TraceLoggerOk tl⌝ ∗ ownRaftPhysCV c c.voters r id s := by
  cases htr : s.gh.tr with
  | some _ =>
    iintro ⟨-, Hphys⟩
    iframe Hphys
    ipureintro; intro h; cases h
  | none =>
    iintro ⟨#Htl, Hphys⟩
    icases ownRaftPhysC_traceLogger c r id s htr $$ Hphys with ⟨%tl', #Htl', %Hok, Hphys⟩
    icombine Htl Htl' gives %Heq
    iframe Hphys
    ipureintro; intro _; rw [Heq]; exact Hok

/-- **`traceSendMessage.tracedSpec`** (the Draft's, frozen) from `traceSendMessage.spec`: raft's state
and the message held apart, lent out of their conjunction (`raftLend_sep`, `msgLend_sep`); untraced,
the gate is `emp` and the struct's logger nil. -/
theorem traceSendMessage.tracedSpec_of_spec (h : traceSendMessage.spec (GF := GF) (hG := hG)) :
    traceSendMessage.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s ml dq ms tl Q Hns
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hm, Hfire⟩ HΦ
  icases traceLogger_none_ok c r id s tl $$ [$Htl $Hphys] with ⟨%Hok, Hphys⟩
  revert Hns Hok
  cases htr : s.gh.tr with
  | none =>
    intro _ Hok
    iapply h r ml tl none (sendGate id s c ms) Q iprop(emp) $$ [$Hpkg $Htl $Hfire]
    · isplitr
      · ipureintro; exact Hok
      iapply trOwn_none_intro
    inext
    iintro ⟨-, HQ⟩
    iapply HΦ
    iframe Hphys Hm HQ
  | some γd =>
    intro Hns Hok
    iapply h r ml tl (some γd) (sendGate id s c ms) Q
      iprop(ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms) $$ [$Hpkg $Htl Hphys Hm $Hfire]
    · isplitr
      · ipureintro; exact Hok
      iapply (trOwn_some γd _).2
      iexists c, id, s, iprop(ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms),
        ⟨dq, DFrac.discard, false, ms⟩
      iframe Hphys Hm
      isplitr
      · iapply raftLend_sep
      isplitr
      · iapply msgLend_sep_some iprop(ownRaftPhysCV c c.voters r id s) ml
          ⟨dq, DFrac.discard, false, ms⟩
      isplitr
      · ipureintro; exact ⟨Hns rfl, rfl⟩
      iintro H; iexact H
    inext
    iintro ⟨Hown, HQ⟩
    iapply HΦ
    iframe HQ
    iapply (trOwn_some γd _).1
    iexact Hown

/-- **`traceReceiveMessage.tracedSpec`** (the Draft's, frozen) from `traceReceiveMessage.spec`: raft's state
and the message held apart, lent out of their conjunction (`raftLend_sep`, `msgLend_sep`); untraced,
the gate is `emp` and the struct's logger nil. -/
theorem traceReceiveMessage.tracedSpec_of_spec (h : traceReceiveMessage.spec (GF := GF) (hG := hG)) :
    traceReceiveMessage.tracedSpec (GF := GF) (hG := hG) := by
  intro c r id s ml dq ms tl Q Hns
  iintro %Φ ⟨#Hpkg, #Htl, Hphys, Hm, Hfire⟩ HΦ
  icases traceLogger_none_ok c r id s tl $$ [$Htl $Hphys] with ⟨%Hok, Hphys⟩
  revert Hns Hok
  cases htr : s.gh.tr with
  | none =>
    intro _ Hok
    iapply h r ml tl none (recvGate id s c ms) Q iprop(emp) $$ [$Hpkg $Htl $Hfire]
    · isplitr
      · ipureintro; exact Hok
      iapply trOwn_none_intro
    inext
    iintro ⟨-, HQ⟩
    iapply HΦ
    iframe Hphys Hm HQ
  | some γd =>
    intro Hns Hok
    iapply h r ml tl (some γd) (recvGate id s c ms) Q
      iprop(ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms) $$ [$Hpkg $Htl Hphys Hm $Hfire]
    · isplitr
      · ipureintro; exact Hok
      iapply (trOwn_some γd _).2
      iexists c, id, s, iprop(ownRaftPhysCV c c.voters r id s ∗ msgOwn ml dq ms),
        ⟨dq, DFrac.discard, false, ms⟩
      iframe Hphys Hm
      isplitr
      · iapply raftLend_sep
      isplitr
      · iapply msgLend_sep_some iprop(ownRaftPhysCV c c.voters r id s) ml
          ⟨dq, DFrac.discard, false, ms⟩
      isplitr
      · ipureintro; exact ⟨Hns rfl, rfl⟩
      iintro H; iexact H
    inext
    iintro ⟨Hown, HQ⟩
    iapply HΦ
    iframe HQ
    iapply (trOwn_some γd _).1
    iexact Hown

/-! ### (Q8 stage 1, slice 3) The `Commit` line's phase step -/

/-- `SimServerR` reads a server only through `toC` at the voters. -/
theorem simServerR_toC {C : List w64} {bl : Nat} {p : PState} {x y : Etcdraft.Server}
    (h : toC (confAbs C) x = toC (confAbs C) y) (hx : SimServerR C bl p x) : SimServerR C bl p y := by
  have ht : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  have hs : x.state = y.state := congrArg ServerC.state h
  have hv : x.votedFor = y.votedFor := congrArg ServerC.votedFor h
  have hl : x.lead = y.lead := congrArg ServerC.lead h
  have hg : x.log = y.log := congrArg ServerC.log h
  have hc : x.commitIndex = y.commitIndex := congrArg ServerC.commitIndex h
  have hr : x.votesResponded = y.votesResponded := congrArg ServerC.votesResponded h
  have hgr : x.votesGranted = y.votesGranted := congrArg ServerC.votesGranted h
  have hm : (confAbs C).map x.matchIndex = (confAbs C).map y.matchIndex := congrArg ServerC.matchIndex h
  have hp : x.pendingConfChangeIndex = y.pendingConfChangeIndex := congrArg ServerC.pendingConfChangeIndex h
  have hf : x.config = y.config := congrArg ServerC.config h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hx
  refine ⟨by rw [← ht]; exact h1, by rw [← hs]; exact h2, by rw [← hv]; exact h3, by rw [← hl]; exact h4,
    h5, by rw [← hg]; exact h6, by rw [← hc]; exact h7, by rw [← hf]; exact h8, by rw [← hp]; exact h9, ?_, ?_⟩
  · intro hrole
    obtain ⟨a, b⟩ := h10 hrole
    exact ⟨by rw [← hr]; exact a, by rw [← hgr]; exact b⟩
  · intro hrole j hj
    rw [← List.map_eq_map_iff.1 hm (idAbs j) ((mem_confAbs C j).2 hj)]
    exact h11 hrole j hj

/-- `AdvancesTo` reads a server only through `toC` at its configuration. -/
theorem advancesTo_toC {C : List w64} {x y : Etcdraft.Server} {n : Int}
    (h : toC (confAbs C) x = toC (confAbs C) y) (hcfg : x.config.incoming = confAbs C)
    (hx : AdvancesTo x n) : AdvancesTo y n := by
  have hs : x.state = y.state := congrArg ServerC.state h
  have ht : x.currentTerm = y.currentTerm := congrArg ServerC.currentTerm h
  have hg : x.log = y.log := congrArg ServerC.log h
  have hc : x.commitIndex = y.commitIndex := congrArg ServerC.commitIndex h
  have hm : (confAbs C).map x.matchIndex = (confAbs C).map y.matchIndex := congrArg ServerC.matchIndex h
  have hf : x.config = y.config := congrArg ServerC.config h
  have hfil : ∀ k : Nat, (confAbs C).filter (fun j => decide (y.matchIndex j ≥ (k : Int))) =
      (confAbs C).filter (fun j => decide (x.matchIndex j ≥ (k : Int))) := by
    intro k
    apply List.filter_congr
    intro j hj
    rw [List.map_eq_map_iff.1 hm j hj]
  intro st i hst
  have h0 := hx (st.upd i (fun _ => x)) i (by simp [Etcdraft.State.upd])
  unfold Etcdraft.State.advanceCommitIndex Etcdraft.State.getConfig at h0 ⊢
  simp only [Etcdraft.State.upd, ↓reduceIte, hcfg] at h0
  simp only [hst, ← hs, ← ht, ← hg, ← hc, ← hf, hcfg, hfil]
  revert h0
  split
  · intro h0; cases h0
  · intro h0
    have h1 := congrArg (fun o => o.map (fun st' => (st'.s i).commitIndex)) h0
    simp only [Option.map_some, Etcdraft.State.commitTo, Etcdraft.State.upd, ↓reduceIte] at h1
    have h2 := Option.some.inj h1
    congr 1
    unfold Etcdraft.State.commitTo Etcdraft.State.upd
    congr 1
    funext j
    split
    · rename_i hj; subst hj; simp only [hst, ← hc, h2]
    · rfl

/-- The committed server's `toC`. -/
theorem toC_commitIndex (srv : Etcdraft.SetIds) (a : Etcdraft.Server) (v : Int) :
    toC srv { a with commitIndex := v } = { toC srv a with commitIndex := v } := rfl

/-- **The `Commit` line's phase step** (`traceCommit.tracedSpec`'s phases): from a leader whose
`AdvanceCommitIndex` commits to `n`, the server so committed idle-related to `s`, the line's effect
(`lineEffect_commit`) at every server the share stands for, into the idle relation. -/
theorem phaseStepB_commit (id : w64) (c : CfgM) (s : NState) :
    PhaseStepB id c (NodeEvOf rsmCommit id s c)
      (fun C cs P => ∃ (a : Etcdraft.Server) (n : Int),
        toC (confAbs C) a = cs ∧ a.state = Etcdraft.leader ∧ AdvancesTo a n ∧
        SimIdle C s (toC (confAbs C) { a with commitIndex := max a.commitIndex n }) P)
      (fun C => SimIdle C s) := by
  intro C cs P hΦ hc e he
  obtain ⟨a0, n, hcs, hlead, hadv, a'', ha'', hR, hs, hP, bt, bc, bl⟩ := hΦ
  obtain ⟨hin, hout, hC⟩ := hc
  refine ⟨he.2.1, by rw [nodeEvOf_name_commit he]; decide, ?_⟩
  intro a ha
  have heq : toC (confAbs C) a0 = toC (confAbs C) a := hcs.trans ha.symm
  have hci : a0.commitIndex = a.commitIndex := congrArg ServerC.commitIndex heq
  have hc' : toC (confAbs C) { a0 with commitIndex := max a0.commitIndex n } =
      toC (confAbs C) { a with commitIndex := max a.commitIndex n } := by
    rw [toC_commitIndex, toC_commitIndex, heq, hci]
    try rfl
  have hcf : a''.config = a0.config := congrArg ServerC.config ha''
  have hcfg : a0.config.incoming = confAbs C := by rw [← hcf, hR.2.2.2.2.2.2.2.1]
  have hR' : SimServerR C C.length (toPState s) { a with commitIndex := max a.commitIndex n } :=
    simServerR_toC (ha''.trans hc') hR
  have hlead' : a.state = Etcdraft.leader := (congrArg ServerC.state heq).symm.trans hlead
  have hrole : s.role = .leader := by
    have h2 := hR'.2.1
    simp only at h2
    rw [hlead'] at h2
    cases hr : s.role <;> simp [toPState, proleRole, roleAbs, hr] at h2 <;> first | rfl | exact absurd h2 (by decide)
  refine ⟨{ a with commitIndex := max a.commitIndex n }, [], ?_, by simp, ?_⟩
  · rw [List.append_nil, ← hc']
    exact ⟨a'', ha'', hR, hs, hP, bt, bc, bl⟩
  · exact lineEffect_commit C e id s c a n _ he hin hout hC hlead' (advancesTo_toC heq hcfg hadv)
      hR' hs hrole bt bc bl

/-- **`traceCommit.tracedSpec`** (the Draft's, frozen) from `traceCommit.spec`: the hook's gate from the
capability by the law `trCap_fire_any` (traced) or from the struct's nil logger (untraced),
`trCapB_hookGate`, the `Commit` line's phase step `phaseStepB_commit`, the caller's facts without an
update. -/
theorem traceCommit.tracedSpec_of_spec (h : traceCommit.spec (GF := GF) (hG := hG)) :
    traceCommit.tracedSpec (GF := GF) (hG := hG) := by
  intro c γ r id s b Λ Λ' hΛ hOk
  iintro %Φ ⟨#Hpkg, Hphys, Hcap, Hfx⟩ HΦ
  icases trCapB_logger0 c c.voters r id s γ b _ Λ $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok, Hphys, Hcap⟩
  ihave Hfx := fxPresT_upd _ _ _ _ _ _ $$ Hfx
  ihave Hgate := trCapB_hookGate s.gh.tr γ r id c tl0 _ b _ (fun C => SimIdle C s) Λ Λ' iprop(emp)
    (phaseStepB_commit id c s) (fun _ e he => by rw [nodeEvOf_name_commit he]; rfl) hΛ hOk Hok
    $$ [$Htl0 $Hcap $Hfx]
  iunfold HookGate at Hgate
  imod Hgate with ⟨%tl, #Htl, Hfire⟩
  icases trOwn_split s.gh.tr _ $$ Hphys with ⟨Hown, Hback⟩
  iapply h c r id s tl iprop(trCapB s.gh.tr γ r id c true (fun C => SimIdle C s) Λ' ∗ emp)
    $$ [$Hpkg $Htl $Hown Hfire]
  · iapply traceFire_mono_E s.gh.tr tl (NodeEvOf rsmCommit id s c) (NodeEvOf (W64 4) id s c) _
      (fun e he => he) $$ Hfire
  inext
  iintro ⟨Hown, Hcap, -⟩
  iapply HΦ
  iframe Hcap
  iapply Hback $$ Hown

/-! ### (Q8 stage 1, slice 3) The hooks' callers on the capability

Each caller's one spec takes the hook's gate (`HookGate`); with the capability, the line's phase step
and facts it is the Draft's shape (`trCapB` in, `trCapB` in the next phase out), by `trCapB_hookGate`
(`trCapB_hookGate_bf`). These are the statements a traced caller (`raft.Step`'s handlers, holding the
node's ghost) uses. -/

/-- **`r.becomeCandidate()` on the capability**: the `BecomeCandidate` line, by `trCap_fire_any`. -/
theorem raft.becomeCandidate.traced (h : raft.becomeCandidate.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (γ : RaftNames) (b : Bool)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop) (R' : IProp GF)
    (hrole : s.role ≠ .leader) (hnw : uint.Z s.term + 1 < 2 ^ 64) (hid : id ∈ c.voters)
    (hps : PhaseStepB id c (NodeEvOf (W64 1) id (becomeCandidate id s) c) Φ Φ')
    (hΛ : ∀ e, NodeEvOf (W64 1) id (becomeCandidate id s) c e → Λ' (some e))
    (hOk : s.gh.tr.isSome → ∀ e, NodeEvOf (W64 1) id (becomeCandidate id s) c e →
      TraceEv.Ok (elements c.incoming).length e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        trCapB s.gh.tr γ r id c b Φ Λ ∗
        FxPresUT s.gh.tr γ id (NodeEvOf (W64 1) id (becomeCandidate id s) c) Φ Φ' R' }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeCandidate")) (Val #()))
    {{ (pvs : GMap w64 Progress), RET #();
        ownRaftPhysCV c c.voters r id { becomeCandidate id s with prvals := pvs } ∗
        trCapB s.gh.tr γ r id c true Φ' Λ' ∗ R' }} := by
  iintro %Ψ ⟨#Hpkg, Hphys, Hcap, Hfx⟩ HΨ
  icases trCapB_logger0 c c.voters r id s γ b Φ Λ $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok, Hphys, Hcap⟩
  iapply h c r id s _ hrole hnw hid $$ [Hphys Hcap Hfx]
  · iframe Hpkg Hphys
    iapply trCapB_hookGate s.gh.tr γ r id c tl0 _ b Φ Φ' Λ Λ' R' hps
      (fun _ e he => by rw [nodeEvOf_name_candidate he]; rfl) hΛ hOk Hok
    iframe Htl0 Hcap Hfx
  inext
  iintro %pvs ⟨Hphys, HQ⟩
  iapply HΨ $$ %pvs
  iframe Hphys HQ

/-- **`r.becomeFollower(term, lead)` on the capability**: the `BecomeFollower` line, a bootstrap line
before the node's segment is over (`b = false`, `trCap_fire_boot`), a step-down or a skip after it
(`trCap_fire_bf`, the caller's `PhaseStepBF` and `FxPresBF`). (Amendment A1, 2026-11-09; Q13 review
rounds 2-4's C) The capability is at the voters' configuration `cC`, raft's struct and the event at
raft's own `c`: apart during the node's bootstrap, where raft's is still empty (`newRaft`'s and
`Bootstrap`'s `becomeFollower`), one after it (`b = true → cC = c`); the bootstrap event's bound is
the capability's (`nodeEvOf_okBoot` at `n = |cC|`, raft's configuration within the voters'). -/
theorem raft.becomeFollower.traced (h : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (c cC : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) (term lead : w64) (γ : RaftNames)
    (b : Bool) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop)
    (hle : uint.Z s.term ≤ uint.Z term) (hV : s.gh.tr ≠ none → V = c.voters)
    (hcC : b = true → cC = c) (hout : b = false → c.outgoing = ∅)
    (hbf : b = true → PhaseStepBF id c (becomeFollower s term lead) Φ Φ' Λ)
    (hb0 : b = false → ∀ C cs P, Φ C cs P → Φ' C cs P)
    (hΛ : ∀ e, NodeEvOf (W64 2) id (becomeFollower s term lead) c e → Λ' (some e))
    (hOk : s.gh.tr.isSome →
      (b = true → ∀ e, NodeEvOf (W64 2) id (becomeFollower s term lead) c e → TraceEv.Ok (elements c.incoming).length e) ∧
      (b = false → ∀ e, NodeEvOf (W64 2) id (becomeFollower s term lead) c e → TraceEv.OkBoot (elements cC.incoming).length e)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s ∗
        trCapB s.gh.tr γ r id cC b Φ Λ ∗ trOwn s.gh.tr (if b then FxPresBF γ id Φ else iprop(emp)) }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeFollower"))
        (Val #term)) (Val #lead))
    {{ (pvs : GMap w64 Progress), RET #();
        ownRaftPhysCV c V r id { becomeFollower s term lead with prvals := pvs } ∗
        trCapB s.gh.tr γ r id cC b Φ' Λ' }} := by
  iintro %Ψ ⟨#Hpkg, Hphys, Hcap, Hfx⟩ HΨ
  icases trCapB_logger0 c V r id s γ b Φ Λ cC $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok, Hphys, Hcap⟩
  iapply h c r id s term lead _ hle hV $$ [Hphys Hcap Hfx]
  · iframe Hpkg Hphys
    iapply trCapB_hookGate_bf s.gh.tr γ r id c cC tl0 _ b Φ Φ' Λ Λ' hcC hout hbf hb0 hΛ hOk Hok
    iframe Htl0 Hcap Hfx
  inext
  iintro %pvs ⟨Hphys, HQ⟩
  iapply HΨ $$ %pvs
  iframe Hphys HQ

/-- **`r.maybeCommit()` on the capability**: the deferred `Commit` line, by `trCap_fire_any`, at the
outcome; the line's facts come through an update at `⊤` once the outcome is known (where the caller
creates the new commit's `isCommitted`). -/
theorem raft.maybeCommit.traced (h : raft.maybeCommit.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (γ : RaftNames) (b0 : Bool)
    (Φ : List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Φ' : Bool → w64 → List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ Λ' : Option TraceEv → Prop) (R' : Bool → w64 → IProp GF)
    (hlead : s.role = .leader)
    (hps : ∀ b N, maybeCommitOut c s b N →
      PhaseStepB id c (NodeEvOf rsmCommit id
        (if b then { s with logst := { s.logst with committed := N } } else s) c) Φ (Φ' b N))
    (hΛ : ∀ b N, maybeCommitOut c s b N → ∀ e, NodeEvOf rsmCommit id
        (if b then { s with logst := { s.logst with committed := N } } else s) c e → Λ' (some e))
    (hOk : s.gh.tr.isSome → ∀ b N, maybeCommitOut c s b N → ∀ e, NodeEvOf rsmCommit id
        (if b then { s with logst := { s.logst with committed := N } } else s) c e → TraceEv.Ok (elements c.incoming).length e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        trCapB s.gh.tr γ r id c b0 Φ Λ ∗
        (∀ b N, ⌜maybeCommitOut c s b N⌝ ={⊤}=∗ FxPresUT s.gh.tr γ id (NodeEvOf rsmCommit id
          (if b then { s with logst := { s.logst with committed := N } } else s) c) Φ (Φ' b N) (R' b N)) }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeCommit")) (Val #()))
    {{ (b : Bool) (N : w64), RET #b;
        ⌜maybeCommitOut c s b N⌝ ∗
        ownRaftPhysCV c c.voters r id
          (if b then { s with logst := { s.logst with committed := N } } else s) ∗
        ⌜b = true → CommitOkC c (toPState s) N⌝ ∗ trCapB s.gh.tr γ r id c true (Φ' b N) Λ' ∗ R' b N }} := by
  iintro %Ψ ⟨#Hpkg, Hphys, Hcap, Hfx⟩ HΨ
  icases trCapB_logger0 c c.voters r id s γ b0 Φ Λ $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok, Hphys, Hcap⟩
  iapply h c r id s _ hlead $$ [Hphys Hcap Hfx]
  · iframe Hpkg Hphys
    iintro %b %N %Hout
    iapply hookGate_fupd
    imod Hfx $$ %b %N %Hout with Hfx
    imodintro
    iapply trCapB_hookGate s.gh.tr γ r id c tl0 _ b0 Φ (Φ' b N) Λ Λ' (R' b N) (hps b N Hout)
      (fun _ e he => by rw [nodeEvOf_name_commit he]; rfl) (hΛ b N Hout)
      (fun h' => hOk h' b N Hout) Hok
    iframe Htl0 Hcap Hfx
  inext
  iintro %b %N ⟨%Hout, Hphys, %HN, HQ⟩
  iapply HΨ $$ %b %N
  iframe Hphys HQ
  isplitr
  · ipureintro; exact Hout
  ipureintro; exact HN

/-! ### (Q8 stage 1, slice 5) `raft.send` on the capability -/

/-- A traced type's send queues exactly one message the model describes (`SendOk`'s clauses (a),
(b), (d)); the others (a snapshot, a transfer message, a forwarded proposal or read index) are not
traced (`sendEvt`). -/
theorem sendOk_traced_single {id : w64} {s : NState} {m : MessageM} {ents : List EntryM}
    {ctx : List w8} {out : List Msg} {evt : w64} (Hok : SendOk id s m ents ctx out)
    (hev : (mtypeOf m.Type').bind sendEvt = some evt) : ∃ mm, out = [mm] := by
  unfold SendOk at Hok
  rcases Hok with ⟨_, _, _, _, _, _, _, rfl⟩ | ⟨_, _, _, _, _, _, rfl⟩ |
    (⟨HSnap, _⟩ | ⟨Htt, _⟩) | ⟨_, _, _, _, rfl⟩ | (⟨HProp, _⟩ | ⟨HRI, _⟩)
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · rw [HSnap, show (mtypeOf MsgSnap).bind sendEvt = none from rfl] at hev; cases hev
  · rcases Htt with h | h
    · rw [h, show (mtypeOf MsgTimeoutNow).bind sendEvt = none from rfl] at hev; cases hev
    · rw [h, show (mtypeOf MsgTransferLeader).bind sendEvt = none from rfl] at hev; cases hev
  · exact ⟨_, rfl⟩
  · rw [HProp, show (mtypeOf MsgProp).bind sendEvt = none from rfl] at hev; cases hev
  · rw [HRI, show (mtypeOf MsgReadIndex).bind sendEvt = none from rfl] at hev; cases hev

/-- **`raft.send.tracedSpec`** (the Draft's, frozen) from `raft.send.spec`: the hook's gate from the
capability. For a traced type the send line (`out`'s one message), by the laws `trCap_fire` (the node's
segment not over) and `trCap_fire_booted`, the line's facts (`FxPresT`, no ghost update:
`fxPres_upd`); for another type the capability with its phase weakened (`trCapB_mono`). Untraced, the
gate is the struct's nil logger (`trCapB_logger0`). -/
theorem raft.send.tracedSpec_of_spec (h : raft.send.spec (GF := GF) (hG := hG)) :
    raft.send.tracedSpec (GF := GF) (hG := hG) := by
  intro c γ r id s ml m ents sn ctx rs out Φ Φ' b Λ Λ' Hfrom Hok Hsn Hsh Hrs Hsnap Hps HΛ HOkK
  have Hsnap' : s.gh.tr ≠ none → mtypeOf m.Type' ≠ some .snap :=
    fun h' => Hsnap (Option.isSome_iff_ne_none.2 h')
  revert Hps HΛ
  cases hev : (mtypeOf m.Type').bind sendEvt with
  | none =>
    intro Hps _
    simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    iintro %Ψ ⟨#Hpkg, Hphys, Hm, #Hsrc, Hcap, -⟩ HΨ
    icases trCapB_logger0 c c.voters r id s γ b Φ Λ $$ [$Hphys $Hcap]
      with ⟨%tl0, #Htl0, %Htlok, Hphys, Hcap⟩
    iapply h c r id s ml m ents sn ctx rs out (trCapB s.gh.tr γ r id c b Φ' Λ) Hfrom Hok Hsn Hsh Hrs
      Hsnap' $$ [Hphys Hm Hcap]
    · iframe Hpkg Hphys Hm Hsrc
      unfold sendOutGate
      rw [hev]
      iunfold HookGateOpt
      imodintro
      iexists tl0
      iframe Htl0
      isplitr
      · ipureintro; exact Htlok
      simp only [Option.map_none, TraceFireOpt]
      iapply trCapB_mono s.gh.tr γ r id c b Φ Φ' Λ Hps $$ Hcap
    inext
    iintro ⟨Hphys, HQ⟩
    iapply HΨ
    iframe Hphys HQ
  | some evt =>
    intro Hps HΛ
    obtain ⟨mm, rfl⟩ := sendOk_traced_single Hok hev
    have Hps1 := Hps mm (List.mem_singleton_self _)
    have HΛ1 := HΛ evt rfl mm (List.mem_singleton_self _)
    simp only [Option.isSome_some, List.isEmpty_cons, Bool.not_false, Bool.and_self, ↓reduceIte]
    iintro %Ψ ⟨#Hpkg, Hphys, Hm, #Hsrc, Hcap, Hfx⟩ HΨ
    ihave Hfx : FxPresT s.gh.tr γ id (SendEvOf evt id s c mm) Φ Φ' $$ [Hfx]
    · iapply (BigSepL.bigSepL_singleton (Φ := fun _ x => FxPresT (GF := GF) s.gh.tr γ id
        (SendEvOf evt id s c x) Φ Φ')).1 $$ Hfx
    icases trCapB_logger0 c c.voters r id s γ b Φ Λ $$ [$Hphys $Hcap]
      with ⟨%tl0, #Htl0, %Htlok, Hphys, Hcap⟩
    iapply h c r id s ml m ents sn ctx rs [mm] (trCapB s.gh.tr γ r id c true Φ' Λ') Hfrom Hok Hsn
      Hsh Hrs Hsnap' $$ [Hphys Hm Hcap Hfx]
    · iframe Hpkg Hphys Hm Hsrc
      have hE : (fun e => ∃ x ∈ [mm], SendEvOf evt id s c x e) = SendEvOf evt id s c mm := by
        funext e; simp
      unfold sendOutGate
      rw [hev]
      simp only [Option.map_some, TraceFireOpt]
      rw [hE]
      iunfold HookGateOpt
      simp only [TraceFireOpt]
      imodintro
      iexists tl0
      iframe Htl0
      isplitr
      · ipureintro; exact Htlok
      revert Htlok
      cases htr : s.gh.tr with
      | none =>
        intro Htlok
        simp only [TraceFire, trCapB]
        isplitr
        · ipureintro; exact Htlok rfl
        iempintro
      | some γd =>
        intro _
        have HOk1 := HOkK (by rw [htr]; rfl) evt hev mm (List.mem_singleton_self _)
        simp only [FxPresT]
        ihave Hfx := fxPres_upd γ id _ Φ Φ' $$ Hfx
        iapply traceFire_mono (some γd) tl0 _ iprop(trCapB (some γd) γ r id c true Φ' Λ' ∗ emp)
        isplitr
        · iintro ⟨H, -⟩; iexact H
        cases b with
        | false =>
          iapply trCap_fire γd γ r id c tl0 _ Φ Φ' Λ Λ' iprop(emp) Hps1 HΛ1 HOk1
          iframe Htl0 Hfx
          iapply trCapB_trCap
          iexact Hcap
        | true =>
          iapply trCap_fire_booted γd γ r id c tl0 _ Φ Φ' Λ Λ' iprop(emp)
            (fun C cs P hΦ hc e he => by
              obtain ⟨h1, h2, h3⟩ := Hps1 C cs P hΦ hc e he
              exact ⟨h1, isBootstrapName_bf _ h2, h3⟩) HΛ1 HOk1
          iframe Hcap Htl0 Hfx
    inext
    iintro ⟨Hphys, HQ⟩
    iapply HΨ
    iframe Hphys HQ

/-! ### (Q8 stage 1, slice 7) `appendEntry` and `becomeLeader` on the capability

The leader's lines: `BecomeLeader`, then one `Replicate` per normal entry (`traceReplicate`'s loop,
`TraceFireN`), then the self-acknowledgement's `SendAppendEntriesResponse` (`appendEntry`'s `send`).
Each line is one law (`trCap_fire_any`), its facts the caller's (`FxPresUT`), chained: a line's facts
take the previous line's resource (`R1 -∗ FxPresUT … R2`), so that the `BecomeLeader` line's update
can create the new leader's term log and each `Replicate` line's the record of its entry, which the
next lines' facts read (`notes/decisions.md`, "Q8 stage 1 (slice 7)"). -/

/-- The event names that are not a bootstrap line's (`InitState` 0, `BecomeFollower` 2,
`ApplyConfChange` 7). -/
theorem evtNames_notBoot : ∀ k : Fin evtNames.length, k.val ≠ 0 → k.val ≠ 2 → k.val ≠ 7 →
    Etcdraft.isBootstrapName (TraceSim.gsStr evtNames[k]) = false := by
  decide

/-- An event named by `evtNames` at an index other than a bootstrap line's is not a bootstrap line. -/
theorem evtName_notBoot {k : Nat} {n : GoString} (h : evtNames[k]? = some n) (h0 : k ≠ 0) (h2 : k ≠ 2)
    (h7 : k ≠ 7) : Etcdraft.isBootstrapName (TraceSim.gsStr n) = false := by
  obtain ⟨hk, hn⟩ := List.getElem?_eq_some_iff.1 h
  have := evtNames_notBoot ⟨k, hk⟩ h0 h2 h7
  simp only [Fin.getElem_fin] at this
  rw [hn] at this
  exact this

/-- A node event at a non-bootstrap index is not a bootstrap line. -/
theorem nodeEvOf_notBoot {evt id : w64} {s : NState} {c : CfgM} {e : TraceEv} (h : NodeEvOf evt id s c e)
    (h0 : uint.nat evt ≠ 0) (h2 : uint.nat evt ≠ 2) (h7 : uint.nat evt ≠ 7) :
    Etcdraft.isBootstrapName (TraceSim.gsStr e.name) = false :=
  evtName_notBoot h.1 h0 h2 h7

/-- A send or receive event is not a bootstrap line. -/
theorem sendEvOf_notBoot {evt id : w64} {s : NState} {c : CfgM} {m : Msg} {e : TraceEv}
    (h : SendEvOf evt id s c m e) (h0 : uint.nat evt ≠ 0) (h2 : uint.nat evt ≠ 2) (h7 : uint.nat evt ≠ 7) :
    Etcdraft.isBootstrapName (TraceSim.gsStr e.name) = false :=
  evtName_notBoot h.1 h0 h2 h7

/-- `TraceFireN`'s monotonicity. -/
theorem traceFireN_mono (tr : Option GName) (tl : GoInterface) (E : TraceEv → Prop) :
    ∀ (n : Nat) (Q Q' : IProp GF), iprop((Q -∗ Q') ∗ TraceFireN tr tl E n Q) ⊢ TraceFireN tr tl E n Q'
  | 0, Q, Q' => by simp only [TraceFireN]; exact traceFireOpt_mono tr tl none Q Q'
  | n + 1, Q, Q' => by
    simp only [TraceFireN]
    iintro ⟨HW, H⟩
    iapply traceFire_mono tr tl E (TraceFireN tr tl E n Q) (TraceFireN tr tl E n Q')
    iframe H
    iintro H
    iapply traceFireN_mono tr tl E n Q Q'
    iframe HW H

/-- `HookGateN`'s monotonicity. -/
theorem hookGateN_mono (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (n : Nat) (Q Q' : IProp GF) :
    iprop((Q -∗ Q') ∗ HookGateN tr r E n Q) ⊢ HookGateN tr r E n Q' := by
  iintro ⟨HW, H⟩
  iunfold HookGateN at H
  iunfold HookGateN
  imod H with ⟨%tl, #Htl, H⟩
  imodintro
  iexists tl
  iframe Htl
  iapply traceFireN_mono tr tl E n Q Q'
  iframe HW H

/-- `HookGate`'s monotonicity. -/
theorem hookGate_mono (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (Q Q' : IProp GF) :
    iprop((Q -∗ Q') ∗ HookGate tr r E Q) ⊢ HookGate tr r E Q' := by
  iintro ⟨HW, H⟩
  iunfold HookGate at H
  iunfold HookGate
  imod H with ⟨%tl, #Htl, H⟩
  imodintro
  iexists tl
  iframe Htl
  iapply traceFire_mono tr tl E Q Q'
  iframe HW H

/-- `HookGate` is `HookGateN` at one event. -/
theorem hookGate_n1 (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (Q : IProp GF) :
    HookGate tr r E Q ⊢ HookGateN tr r E 1 Q := by
  iintro H
  iunfold HookGate at H
  iunfold HookGateN
  imod H with ⟨%tl, #Htl, H⟩
  imodintro
  iexists tl
  iframe Htl
  simp only [TraceFireN, TraceFireOpt]
  iexact H

/-- `HookGate` gives the optional gate at `some E` (the untraced nil logger from `TraceFire`'s). -/
theorem hookGate_opt (tr : Option GName) (r : Loc) (E : TraceEv → Prop) (Q : IProp GF) :
    HookGate tr r E Q ⊢ HookGateOpt tr r (some E) Q := by
  iintro H
  iunfold HookGate at H
  iunfold HookGateOpt
  imod H with ⟨%tl, #Htl, H⟩
  imodintro
  iexists tl
  iframe Htl
  simp only [TraceFireOpt]
  cases tr with
  | none =>
    simp only [TraceFire]
    icases H with ⟨%Hok, HQ⟩
    iframe HQ
    isplitr
    · ipureintro; intro _; exact Hok
    ipureintro; exact Hok
  | some γd =>
    iframe H
    ipureintro; intro h; cases h

/-- The chain of the untraced lines' updates: `Rs j` to `Rs (j + n)`. -/
theorem fxChain_none (γ : RaftNames) (id : w64) (E : TraceEv → Prop)
    (Φs : Nat → List w64 → ServerC → List Etcdraft.Msg → Prop) (Rs : Nat → IProp GF) :
    ∀ (n j : Nat), iprop(Rs j ∗ [∗list] k ∈ List.range' j n,
        (Rs k -∗ FxPresUT none γ id E (Φs k) (Φs (k + 1)) (Rs (k + 1)))) ⊢ |==> Rs (j + n)
  | 0, j => by
    iintro ⟨HR, -⟩
    imodintro
    iexact HR
  | n + 1, j => by
    rw [List.range'_succ]
    iintro ⟨HR, H, Hrest⟩
    simp only [FxPresUT]
    imod H $$ HR with HR
    have h := fxChain_none γ id E Φs Rs n (j + 1)
    rw [show j + 1 + n = j + (n + 1) by omega] at h
    simp only [FxPresUT] at h
    iapply h
    iframe HR Hrest

/-- The traced lines in a row: `n` laws (`trCap_fire_any`), from the phase `Φs j` to `Φs (j + n)`,
each line's facts taking the previous one's resource. -/
theorem trCap_fireN (γd : GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM) (tl : GoInterface)
    (E : TraceEv → Prop) (Φs : Nat → List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Λ' : Option TraceEv → Prop) (Rs : Nat → IProp GF) (N : Nat)
    (hps : ∀ k < N, PhaseStepB id c E (Φs k) (Φs (k + 1)))
    (hnb : ∀ e, E e → Etcdraft.isBootstrapName (TraceSim.gsStr e.name) = false)
    (hΛ : ∀ e, E e → Λ' (some e)) (hOk : ∀ e, E e → TraceEv.Ok (elements c.incoming).length e) :
    ∀ (n j : Nat) (b : Bool) (Λ : Option TraceEv → Prop), j + n ≤ N →
      iprop(trCapB (some γd) γ r id c b (Φs j) Λ ∗ r.[raft, go!"traceLogger"] ↦□ tl ∗ Rs j ∗
        [∗list] k ∈ List.range' j n,
          (Rs k -∗ FxPresUT (some γd) γ id E (Φs k) (Φs (k + 1)) (Rs (k + 1)))) ⊢
      TraceFireN (some γd) tl E n
        iprop(trCapB (some γd) γ r id c (if n = 0 then b else true) (Φs (j + n))
          (if n = 0 then Λ else Λ') ∗ Rs (j + n))
  | 0, j, b, Λ, _ => by
    simp only [TraceFireN, TraceFireOpt, ↓reduceIte, Nat.add_zero]
    iintro ⟨Hcap, -, HR, -⟩
    iframe Hcap HR
  | n + 1, j, b, Λ, hle => by
    rw [List.range'_succ]
    simp only [TraceFireN, Nat.add_one_ne_zero, ↓reduceIte]
    iintro ⟨Hcap, #Htl, HR, H, Hrest⟩
    simp only [FxPresUT]
    ihave Hfx := H $$ HR
    iapply traceFire_mono (some γd) tl E iprop(trCapB (some γd) γ r id c true (Φs (j + 1)) Λ' ∗ Rs (j + 1))
    isplitl [Hrest]
    · iintro ⟨Hcap, HR⟩
      have h := trCap_fireN γd γ r id c tl E Φs Λ' Rs N hps hnb hΛ hOk n (j + 1) true Λ' (by omega)
      rw [show j + 1 + n = j + (n + 1) by omega] at h
      simp only [ite_self, FxPresUT] at h
      iapply h
      iframe Hcap Htl HR Hrest
    iapply trCap_fire_any γd γ r id c tl E b (Φs j) (Φs (j + 1)) Λ Λ' (Rs (j + 1)) (hps j (by omega))
      (fun _ => hnb) hΛ hOk
    iframe Hcap Htl Hfx

/-- **`n` lines in a row, either mode** (`traceReplicate`'s gate, `HookGateN`): the logger `tl0` (nil
when untraced), the capability in phase `Φs 0`, the resource `Rs 0` and the lines' chained facts give
the gate, whose updates leave the capability in phase `Φs n` (booted once a line has fired) and
`Rs n`. -/
theorem trCapB_hookGateN (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (tl0 : GoInterface) (E : TraceEv → Prop) (b : Bool)
    (Φs : Nat → List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop)
    (Rs : Nat → IProp GF) (n : Nat)
    (hps : ∀ k < n, PhaseStepB id c E (Φs k) (Φs (k + 1)))
    (hnb : ∀ e, E e → Etcdraft.isBootstrapName (TraceSim.gsStr e.name) = false)
    (hΛ : ∀ e, E e → Λ' (some e)) (hOk : tr.isSome → ∀ e, E e → TraceEv.Ok (elements c.incoming).length e)
    (hok : tr = none → TraceLoggerOk tl0) :
    (r.[raft, go!"traceLogger"] ↦□ tl0 ∗ trCapB tr γ r id c b (Φs 0) Λ ∗ Rs 0 ∗
        ([∗list] k ∈ List.range n, (Rs k -∗ FxPresUT tr γ id E (Φs k) (Φs (k + 1)) (Rs (k + 1)))) :
        IProp GF) ⊢
      HookGateN tr r E n iprop(trCapB tr γ r id c (if n = 0 then b else true) (Φs n)
        (if n = 0 then Λ else Λ') ∗ Rs n) := by
  rw [List.range_eq_range']
  cases tr with
  | none =>
    simp only [trCapB]
    iintro ⟨#Hl, -, HR, Hch⟩
    iunfold HookGateN
    have h := fxChain_none γ id E Φs Rs n 0
    rw [Nat.zero_add] at h
    imod h $$ [$HR $Hch] with HR
    imodintro
    iexists tl0
    iframe Hl
    iapply traceFireN_of_none rfl tl0 E (hok rfl) _ n
    iframe HR
  | some γd =>
    iintro ⟨-, Hcap, HR, Hch⟩
    icases trCapB_logger γd γ r id c b (Φs 0) Λ $$ Hcap with ⟨%tl, #Htl, Hcap⟩
    iunfold HookGateN
    imodintro
    iexists tl
    iframe Htl
    have h := trCap_fireN γd γ r id c tl E Φs Λ' Rs n hps hnb hΛ (hOk rfl) n 0 b Λ (by omega)
    rw [Nat.zero_add] at h
    iapply h
    iframe Hcap Htl HR Hch

/-- **A message line, either mode** (`send`'s gate at a traced type, `HookGateOpt` at `some E`): as
`trCapB_hookGate`, the line not a bootstrap line whatever the `booted` flag. -/
theorem trCapB_hookGateOpt (tr : Option GName) (γ : RaftNames) (r : Loc) (id : w64) (c : CfgM)
    (tl0 : GoInterface) (E : TraceEv → Prop) (b : Bool)
    (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop) (R' : IProp GF)
    (hps : PhaseStepB id c E Φ Φ')
    (hnb : ∀ e, E e → Etcdraft.isBootstrapName (TraceSim.gsStr e.name) = false)
    (hΛ : ∀ e, E e → Λ' (some e)) (hOk : tr.isSome → ∀ e, E e → TraceEv.Ok (elements c.incoming).length e)
    (hok : tr = none → TraceLoggerOk tl0) :
    (r.[raft, go!"traceLogger"] ↦□ tl0 ∗ trCapB tr γ r id c b Φ Λ ∗ FxPresUT tr γ id E Φ Φ' R' : IProp GF) ⊢
      HookGateOpt tr r (some E) iprop(trCapB tr γ r id c true Φ' Λ' ∗ R') := by
  iintro H
  iapply hookGate_opt
  iapply trCapB_hookGate tr γ r id c tl0 E b Φ Φ' Λ Λ' R' hps (fun _ => hnb) hΛ hOk hok $$ H

/-- The self-acknowledgement's gate (`send`'s, at `MsgAppResp`): its one `SendAppendEntriesResponse`
event. -/
theorem sendOutGate_selfAck (id : w64) (s : NState) (c : CfgM) :
    sendOutGate id s c MsgAppResp [selfAck id s] = some (SendEvOf (W64 11) id s c (selfAck id s)) := by
  unfold sendOutGate
  have h : (mtypeOf MsgAppResp).bind sendEvt = some (W64 11) := rfl
  rw [h]
  simp only [Option.map_some, List.mem_singleton, exists_eq_left]

/-- **`r.appendEntry(es...)` on the capability** (the accept path): one `Replicate` line per normal
entry of the batch (`normalCount ents`, the phases `Φs 0` to `Φs n`, each line's facts taking the
previous one's resource: the caller's update creating the entry records, round 6's F1), then the
self-acknowledgement's `SendAppendEntriesResponse` line (phase `Φs n` to `Φ'`, at the state with the
batch appended). On the reject path nothing is traced and everything comes back. -/
theorem raft.appendEntry.traced (h : raft.appendEntry.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (es : GoSlice) (ents : List EntryM) (dq : DFrac)
    (m : Nat) (γ : RaftNames) (b : Bool) (Φs : Nat → List w64 → ServerC → List Etcdraft.Msg → Prop)
    (Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' ΛA : Option TraceEv → Prop)
    (Rs : Nat → IProp GF) (R' : IProp GF)
    (hsmall : (ents.length : Int) < 2^61) (hterm : s.term ≠ W64 0)
    (hps : ∀ k < normalCount ents, PhaseStepB id c (NodeEvOf (W64 5) id s c) (Φs k) (Φs (k + 1)))
    (hΛ : ∀ e, NodeEvOf (W64 5) id s c e → Λ' (some e))
    (hOk : s.gh.tr.isSome → ∀ e, NodeEvOf (W64 5) id s c e → TraceEv.Ok (elements c.incoming).length e)
    (hpsA : PhaseStepB id c (SendEvOf (W64 11) id
        { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) } c
        (selfAck id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }))
        (Φs (normalCount ents)) Φ')
    (hΛA : ∀ e, SendEvOf (W64 11) id
        { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) } c
        (selfAck id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }) e →
        ΛA (some e))
    (hOkA : s.gh.tr.isSome → ∀ e, SendEvOf (W64 11) id
        { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) } c
        (selfAck id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }) e →
        TraceEv.Ok (elements c.incoming).length e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        entsPts es dq ents ∗ ⧖ m ∗ trCapB s.gh.tr γ r id c b (Φs 0) Λ ∗ Rs 0 ∗
        ([∗list] k ∈ List.range (normalCount ents),
          (Rs k -∗ FxPresUT s.gh.tr γ id (NodeEvOf (W64 5) id s c) (Φs k) (Φs (k + 1)) (Rs (k + 1)))) ∗
        (Rs (normalCount ents) -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id
          { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) } c
          (selfAck id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }))
          (Φs (normalCount ents)) Φ' R') }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"appendEntry")) (Val #es))
    {{ (accepted : Bool), RET #accepted;
        ⧖ (m + ents.length) ∗ ⌜(∀ e ∈ ents, e.Data' = []) → accepted = true⌝ ∗ entsPts es dq ents ∗
        if accepted then
          ownRaftPhysCV c c.voters r id
            (sendMsgs
              { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }
              [selfAck id
                { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }]) ∗
            trCapB s.gh.tr γ r id c true Φ' ΛA ∗ R'
        else
          ownRaftPhysCV c c.voters r id s ∗ trCapB s.gh.tr γ r id c b (Φs 0) Λ ∗ Rs 0 ∗
            ([∗list] k ∈ List.range (normalCount ents),
              (Rs k -∗ FxPresUT s.gh.tr γ id (NodeEvOf (W64 5) id s c) (Φs k) (Φs (k + 1)) (Rs (k + 1)))) ∗
            (Rs (normalCount ents) -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id
              { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) } c
              (selfAck id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }))
              (Φs (normalCount ents)) Φ' R') }} := by
  iintro %Ψ ⟨#Hpkg, Hphys, Hes, #Hrc, Hcap, HR0, Hch, HfxA⟩ HΨ
  icases trCapB_logger0 c c.voters r id s γ b (Φs 0) Λ $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok0, Hphys, Hcap⟩
  iapply h c r id s es ents dq m
    iprop(trCapB s.gh.tr γ r id c b (Φs 0) Λ ∗ Rs 0 ∗
      ([∗list] k ∈ List.range (normalCount ents),
        (Rs k -∗ FxPresUT s.gh.tr γ id (NodeEvOf (W64 5) id s c) (Φs k) (Φs (k + 1)) (Rs (k + 1)))) ∗
      (Rs (normalCount ents) -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) } c (selfAck id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }))
        (Φs (normalCount ents)) Φ' R'))
    iprop((trCapB s.gh.tr γ r id c (if normalCount ents = 0 then b else true) (Φs (normalCount ents))
        (if normalCount ents = 0 then Λ else Λ') ∗ Rs (normalCount ents)) ∗
      (Rs (normalCount ents) -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) } c (selfAck id { s with logst := logAppend s.logst (ents.mapIdx (stamp s.term (logLast s.logst))) }))
        (Φs (normalCount ents)) Φ' R'))
    iprop(trCapB s.gh.tr γ r id c true Φ' ΛA ∗ R') hsmall hterm $$ [Hphys Hes Hcap HR0 Hch HfxA]
  · iframe Hpkg Hphys Hes Hrc
    isplitl [Hcap HR0 Hch HfxA]
    · iapply to_named
      iframe Hcap HR0 Hch HfxA
    isplitr
    · iintro - ⟨Hcap, HR0, Hch, HfxA⟩
      iapply hookGateN_mono s.gh.tr r _ _
        iprop(trCapB s.gh.tr γ r id c (if normalCount ents = 0 then b else true) (Φs (normalCount ents))
          (if normalCount ents = 0 then Λ else Λ') ∗ Rs (normalCount ents))
      isplitl [HfxA]
      · iintro HG1
        iframe HG1 HfxA
      iapply trCapB_hookGateN s.gh.tr γ r id c tl0 _ b Φs Λ Λ' Rs (normalCount ents) hps
        (fun e he => nodeEvOf_notBoot he (by decide) (by decide) (by decide)) hΛ hOk Hok0
      iframe Htl0 Hcap HR0 Hch
    · iintro ⟨⟨Hcap, HRn⟩, HfxA⟩
      ihave HfxA := HfxA $$ HRn
      rw [sendOutGate_selfAck]
      iapply trCapB_hookGateOpt s.gh.tr γ r id c tl0 _ _ (Φs (normalCount ents)) Φ' _ ΛA R' hpsA
        (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide)) hΛA hOkA Hok0
      iframe Htl0 Hcap HfxA
  inext
  iintro %acc ⟨Hrc', %Hemp, Hes, Hif⟩
  iapply HΨ $$ %acc
  iframe Hrc' Hes
  isplitr
  · ipureintro; exact Hemp
  cases acc with
  | true =>
    simp only [↓reduceIte]
    icases Hif with ⟨Hphys, Hcap, HR⟩
    iframe Hphys Hcap HR
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hif with ⟨Hphys, Hcap, HR0, Hch, HfxA⟩
    iframe Hphys Hcap HR0 Hch HfxA

/-- **`r.becomeLeader()` on the capability**: the `BecomeLeader` line (of `becomeLeaderPre`; its facts'
update is where the new leader's term log is created, round 5's E1), the empty entry's `Replicate`
line (its facts taking the term log: where the entry's record is created, round 6's F1) and the
self-acknowledgement's `SendAppendEntriesResponse` (at `becomeLeaderLog`), each by its law, the
facts chained `R1`, `R2`, `R'`. -/
theorem raft.becomeLeader.traced (h : raft.becomeLeader.spec (GF := GF) (hG := hG))
    (c : CfgM) (r : Loc) (id : w64) (s : NState) (γ : RaftNames) (b : Bool)
    (Φ Φ1 Φ2 Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ1 Λ2 Λ' : Option TraceEv → Prop)
    (R1 R2 R' : IProp GF)
    (hrole : s.role ≠ .follower) (hnl : s.role ≠ .leader) (hterm : s.term ≠ W64 0)
    (hps1 : PhaseStepB id c (NodeEvOf (W64 3) id (becomeLeaderPre id s) c) Φ Φ1)
    (hΛ1 : ∀ e, NodeEvOf (W64 3) id (becomeLeaderPre id s) c e → Λ1 (some e))
    (hOk1 : s.gh.tr.isSome → ∀ e, NodeEvOf (W64 3) id (becomeLeaderPre id s) c e →
      TraceEv.Ok (elements c.incoming).length e)
    (hps2 : PhaseStepB id c (NodeEvOf (W64 5) id (becomeLeaderPre id s) c) Φ1 Φ2)
    (hΛ2 : ∀ e, NodeEvOf (W64 5) id (becomeLeaderPre id s) c e → Λ2 (some e))
    (hOk2 : s.gh.tr.isSome → ∀ e, NodeEvOf (W64 5) id (becomeLeaderPre id s) c e →
      TraceEv.Ok (elements c.incoming).length e)
    (hps3 : PhaseStepB id c (SendEvOf (W64 11) id (becomeLeaderLog id s) c
      (selfAck id (becomeLeaderLog id s))) Φ2 Φ')
    (hΛ3 : ∀ e, SendEvOf (W64 11) id (becomeLeaderLog id s) c (selfAck id (becomeLeaderLog id s)) e →
      Λ' (some e))
    (hOk3 : s.gh.tr.isSome → ∀ e, SendEvOf (W64 11) id (becomeLeaderLog id s) c
      (selfAck id (becomeLeaderLog id s)) e → TraceEv.Ok (elements c.incoming).length e) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c c.voters r id s ∗
        trCapB s.gh.tr γ r id c b Φ Λ ∗
        FxPresUT s.gh.tr γ id (NodeEvOf (W64 3) id (becomeLeaderPre id s) c) Φ Φ1 R1 ∗
        (R1 -∗ FxPresUT s.gh.tr γ id (NodeEvOf (W64 5) id (becomeLeaderPre id s) c) Φ1 Φ2 R2) ∗
        (R2 -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id (becomeLeaderLog id s) c
          (selfAck id (becomeLeaderLog id s))) Φ2 Φ' R') }}
      (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeLeader")) (Val #()))
    {{ (pvs : GMap w64 Progress), RET #();
        ownRaftPhysCV c c.voters r id { becomeLeader id s with prvals := pvs } ∗
        ⌜prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals⌝ ∗
        trCapB s.gh.tr γ r id c true Φ' Λ' ∗ R' }} := by
  iintro %Ψ ⟨#Hpkg, Hphys, Hcap, Hfx1, Hfx2, Hfx3⟩ HΨ
  icases trCapB_logger0 c c.voters r id s γ b Φ Λ $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok0, Hphys, Hcap⟩
  iapply h c r id s
    iprop(trCapB s.gh.tr γ r id c b Φ Λ ∗
      FxPresUT s.gh.tr γ id (NodeEvOf (W64 3) id (becomeLeaderPre id s) c) Φ Φ1 R1 ∗
      (R1 -∗ FxPresUT s.gh.tr γ id (NodeEvOf (W64 5) id (becomeLeaderPre id s) c) Φ1 Φ2 R2) ∗
      (R2 -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id (becomeLeaderLog id s) c
        (selfAck id (becomeLeaderLog id s))) Φ2 Φ' R'))
    iprop((trCapB s.gh.tr γ r id c true Φ1 Λ1 ∗ R1) ∗
      (R1 -∗ FxPresUT s.gh.tr γ id (NodeEvOf (W64 5) id (becomeLeaderPre id s) c) Φ1 Φ2 R2) ∗
      (R2 -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id (becomeLeaderLog id s) c
        (selfAck id (becomeLeaderLog id s))) Φ2 Φ' R'))
    iprop((trCapB s.gh.tr γ r id c true Φ2 Λ2 ∗ R2) ∗
      (R2 -∗ FxPresUT s.gh.tr γ id (SendEvOf (W64 11) id (becomeLeaderLog id s) c
        (selfAck id (becomeLeaderLog id s))) Φ2 Φ' R'))
    iprop(trCapB s.gh.tr γ r id c true Φ' Λ' ∗ R')
    hrole hnl hterm $$ [Hphys Hcap Hfx1 Hfx2 Hfx3]
  · iframe Hpkg Hphys
    isplitl [Hcap Hfx1 Hfx2 Hfx3]
    · iapply to_named
      iframe Hcap Hfx1 Hfx2 Hfx3
    isplitr
    · iintro ⟨Hcap, Hfx1, Hfx2, Hfx3⟩
      iapply hookGate_mono s.gh.tr r _ iprop(trCapB s.gh.tr γ r id c true Φ1 Λ1 ∗ R1)
      isplitl [Hfx2 Hfx3]
      · iintro HG1
        iframe HG1 Hfx2 Hfx3
      iapply trCapB_hookGate s.gh.tr γ r id c tl0 _ b Φ Φ1 Λ Λ1 R1 hps1
        (fun _ e he => nodeEvOf_notBoot he (by decide) (by decide) (by decide)) hΛ1 hOk1 Hok0
      iframe Htl0 Hcap Hfx1
    isplitr
    · iintro ⟨⟨Hcap, HR1⟩, Hfx2, Hfx3⟩
      ihave Hfx2 := Hfx2 $$ HR1
      iapply hookGateN_mono s.gh.tr r _ 1 iprop(trCapB s.gh.tr γ r id c true Φ2 Λ2 ∗ R2)
      isplitl [Hfx3]
      · iintro HG2
        iframe HG2 Hfx3
      iapply hookGate_n1
      iapply trCapB_hookGate s.gh.tr γ r id c tl0 _ true Φ1 Φ2 Λ1 Λ2 R2 hps2
        (fun _ e he => nodeEvOf_notBoot he (by decide) (by decide) (by decide)) hΛ2 hOk2 Hok0
      iframe Htl0 Hcap Hfx2
    · iintro ⟨⟨Hcap, HR2⟩, Hfx3⟩
      ihave Hfx3 := Hfx3 $$ HR2
      rw [sendOutGate_selfAck]
      iapply trCapB_hookGateOpt s.gh.tr γ r id c tl0 _ true Φ2 Φ' Λ2 Λ' R' hps3
        (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide)) hΛ3 hOk3 Hok0
      iframe Htl0 Hcap Hfx3
  inext
  iintro %pvs ⟨Hphys, %Hm, Hcap, HR⟩
  iapply HΨ $$ %pvs
  iframe Hphys Hcap HR
  ipureintro; exact Hm

end ghost

end EtcdGrove
end Perennial
