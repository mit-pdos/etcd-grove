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
  intro c γ r id s b Λ Λ' K hΛ hOk
  iintro %Φ ⟨#Hpkg, Hphys, Hcap, Hfx⟩ HΦ
  icases trCapB_logger0 c c.voters r id s γ b _ Λ $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok, Hphys, Hcap⟩
  ihave Hfx := fxPresT_upd _ _ _ _ _ _ $$ Hfx
  ihave Hgate := trCapB_hookGate s.gh.tr γ r id c tl0 _ b _ (fun C => SimIdle C s) Λ Λ' iprop(emp)
    (phaseStepB_commit id c s) (fun _ e he => by rw [nodeEvOf_name_commit he]; rfl) hΛ K hOk Hok
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
    (hΛ : ∀ e, NodeEvOf (W64 1) id (becomeCandidate id s) c e → Λ' (some e)) (K : Nat)
    (hOk : s.gh.tr.isSome → K ≤ 2 ^ 61 ∧ ∀ e, NodeEvOf (W64 1) id (becomeCandidate id s) c e → TraceEv.Ok K e) :
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
      (fun _ e he => by rw [nodeEvOf_name_candidate he]; rfl) hΛ K hOk Hok
    iframe Htl0 Hcap Hfx
  inext
  iintro %pvs ⟨Hphys, HQ⟩
  iapply HΨ $$ %pvs
  iframe Hphys HQ

/-- **`r.becomeFollower(term, lead)` on the capability**: the `BecomeFollower` line, a bootstrap line
before the node's segment is over (`b = false`, `trCap_fire_boot`), a step-down or a skip after it
(`trCap_fire_bf`, the caller's `PhaseStepBF` and `FxPresBF`). -/
theorem raft.becomeFollower.traced (h : raft.becomeFollower.spec (GF := GF) (hG := hG))
    (c : CfgM) {V : GSet w64} (r : Loc) (id : w64) (s : NState) (term lead : w64) (γ : RaftNames)
    (b : Bool) (Φ Φ' : List w64 → ServerC → List Etcdraft.Msg → Prop) (Λ Λ' : Option TraceEv → Prop)
    (hle : uint.Z s.term ≤ uint.Z term) (hV : s.gh.tr ≠ none → V = c.voters)
    (hbf : b = true → PhaseStepBF id c (becomeFollower s term lead) Φ Φ' Λ)
    (hb0 : b = false → ∀ C cs P, Φ C cs P → Φ' C cs P)
    (hΛ : ∀ e, NodeEvOf (W64 2) id (becomeFollower s term lead) c e → Λ' (some e)) (K : Nat)
    (hOk : s.gh.tr.isSome → K ≤ 2 ^ 61 ∧
      (b = true → ∀ e, NodeEvOf (W64 2) id (becomeFollower s term lead) c e → TraceEv.Ok K e) ∧
      (b = false → ∀ e, NodeEvOf (W64 2) id (becomeFollower s term lead) c e → TraceEv.OkBoot K e)) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftPhysCV c V r id s ∗
        trCapB s.gh.tr γ r id c b Φ Λ ∗ trOwn s.gh.tr (if b then FxPresBF γ id Φ else iprop(emp)) }}
      (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"becomeFollower"))
        (Val #term)) (Val #lead))
    {{ (pvs : GMap w64 Progress), RET #();
        ownRaftPhysCV c V r id { becomeFollower s term lead with prvals := pvs } ∗
        trCapB s.gh.tr γ r id c b Φ' Λ' }} := by
  iintro %Ψ ⟨#Hpkg, Hphys, Hcap, Hfx⟩ HΨ
  icases trCapB_logger0 c V r id s γ b Φ Λ $$ [$Hphys $Hcap]
    with ⟨%tl0, #Htl0, %Hok, Hphys, Hcap⟩
  iapply h c r id s term lead _ hle hV $$ [Hphys Hcap Hfx]
  · iframe Hpkg Hphys
    iapply trCapB_hookGate_bf s.gh.tr γ r id c tl0 _ b Φ Φ' Λ Λ' hbf hb0 hΛ K hOk Hok
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
        (if b then { s with logst := { s.logst with committed := N } } else s) c e → Λ' (some e)) (K : Nat)
    (hOk : s.gh.tr.isSome → K ≤ 2 ^ 61 ∧ ∀ b N, maybeCommitOut c s b N → ∀ e, NodeEvOf rsmCommit id
        (if b then { s with logst := { s.logst with committed := N } } else s) c e → TraceEv.Ok K e) :
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
      K (fun h' => ⟨(hOk h').1, (hOk h').2 b N Hout⟩) Hok
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
  intro c γ r id s ml m ents sn ctx rs out Φ Φ' b Λ Λ' K Hfrom Hok Hsn Hsh Hrs Hsnap Hps HΛ HOkK
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
        obtain ⟨hK, HOk1⟩ := HOkK (by rw [htr]; rfl)
        have HOk1 := HOk1 evt hev mm (List.mem_singleton_self _)
        simp only [FxPresT]
        ihave Hfx := fxPres_upd γ id _ Φ Φ' $$ Hfx
        iapply traceFire_mono (some γd) tl0 _ iprop(trCapB (some γd) γ r id c true Φ' Λ' ∗ emp)
        isplitr
        · iintro ⟨H, -⟩; iexact H
        cases b with
        | false =>
          iapply trCap_fire γd γ r id c tl0 K _ Φ Φ' Λ Λ' iprop(emp) Hps1 HΛ1 hK HOk1
          iframe Htl0 Hfx
          iapply trCapB_trCap
          iexact Hcap
        | true =>
          iapply trCap_fire_booted γd γ r id c tl0 K _ Φ Φ' Λ Λ' iprop(emp)
            (fun C cs P hΦ hc e he => by
              obtain ⟨h1, h2, h3⟩ := Hps1 C cs P hΦ hc e he
              exact ⟨h1, isBootstrapName_bf _ h2, h3⟩) HΛ1 hK HOk1
          iframe Hcap Htl0 Hfx
    inext
    iintro ⟨Hphys, HQ⟩
    iapply HΨ
    iframe Hphys HQ

end ghost

end EtcdGrove
end Perennial
