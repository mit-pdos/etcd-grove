/-
Lean-first (no Rocq counterpart). **A leader's accepted `MsgAppResp` of its term: the gates past the
receive line** (2026-11-11, trace-check Q8 stage 1 slice 29c, `notes/decisions.md`, "Q8 stage 1 (slice
29c)").

- **The family past `maybeCommit`** (`leadAccGc b N`): the outcome's `Progress` values (`pvs`, of
  `appRespMatch`'s `Match` values) and its witness, and the local family `lineF` at the state after the
  commit (`commitAt { s with prvals := pvs } b N`), raft's ghost state there.
- **`"Hgcommit"`** (`leadAccGate_commit`): the response's index within the log (`ackIn`), the leader's
  term non-zero, raft's ghost state moved past the commit (`ghost_stepAppCommit`, `"Hgcommit"`'s credit),
  raft's facts there (its log's records and commit certificate, its leadership, its full log:
  `ownRaftGhost_leadFull`), then the `Commit` line (`phaseStepB_commitPin`, `fxPres_commit`) from the
  receive line's result (`AccPin`) by the bridge `advancesTo_of_out` (every `Match` within the log:
  `appRespMatch_le`, raft's `PrvalsOk` and the response's index).
- **The sends after it**: `"#Hgaapp"` (`leadAccGate_app`, `lineF_app` at the committed state, the gate's
  state agreeing in the header, `sendOutGate_hdr`, `appOk_hdr`), `"#Hgrlhb"` (`leadAccGate_hb`,
  `lineF_heartbeat`), `"#Hgrlresp"` (`lineF_untraced`), `"#Hgatnow"` (`lineF_none`: no message).
- **The end state** (`leadAcc_end`): `stepLeader`'s accepted result, its idle server the one at the
  outcome's commit index and `Match` values; `maybeCommitOut`'s outcome unique (`maybeCommitOut_unique`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadAccCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext] [GoSemanticsFunctions]

/-- **A leader's accepted `MsgAppResp` of its term** from a peer it tracks, its `PrvalsOk` (every `Match`
within the log, `ownRaftPhys`'s): the path premise, all read off before the call (`RawNode.Step` refuses a
response from an untracked peer, `ErrStepPeerNotFound`; the tracker's `Progress` records are indexed by
its map's peers, `ownTrackerC_prvals_dom`). -/
def LeadAcc (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgAppResp ∧ m.Reject' = false ∧ m.Term' = s.term ∧ s.role = .leader ∧
    m.From' ∈ domSet s.progress ∧ m.From' ∈ domSet s.prvals ∧ PrvalsOk s

theorem lookup_prvalsMatch (pvs : GMap w64 Progress) (v : w64) :
    prvalsMatch pvs !! v = (pvs !! v).map Progress.matched := by
  simp only [prvalsMatch, GMap.fmap_eq, GMap.lookup_fmap]

theorem prvalsMatch_some_of_dom {pvs : GMap w64 Progress} {v : w64} (h : v ∈ domSet pvs) :
    ∃ x, prvalsMatch pvs !! v = some x := by
  rw [GMap.elem_of_dom] at h
  obtain ⟨p, hp⟩ := h
  exact ⟨p.matched, by rw [lookup_prvalsMatch, hp]; rfl⟩

/-- **Every `Match` after the response within the log** (`L` the log's last index): the others' by
`PrvalsOk`, the sender's by the response's index. -/
theorem appRespMatch_le (s : NState) (src idx : w64) (L : Int) (hrole : s.role = .leader)
    (hpok : PrvalsOk s) (hL : uint.Z (logLast s.logst) = L) (hidx : uint.Z idx ≤ L) :
    ∀ v x, appRespMatch s src idx !! v = some x → uint.Z x ≤ L := by
  have hold : ∀ v x, prvalsMatch s.prvals !! v = some x → uint.Z x ≤ L := by
    intro v x h
    rw [lookup_prvalsMatch] at h
    cases E : s.prvals !! v with
    | none => rw [E] at h; cases h
    | some p =>
      rw [E] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      have := (hpok hrole v p E).1.2.2.1
      omega
  intro v x h
  unfold appRespMatch at h
  cases hs : prvalsMatch s.prvals !! src with
  | none => rw [hs] at h; exact hold v x h
  | some xs =>
    rw [hs] at h
    by_cases hv : src = v
    · subst hv
      rw [GMap.lookup_insert_eq] at h
      simp only [Option.some.injEq] at h
      subst h
      split
      · exact hidx
      · exact hold src xs hs
    · rw [GMap.lookup_insert_ne _ _ hv] at h
      exact hold v x h

theorem isQuorumIndex_unique {S : GSet w64} {f : w64 → w64} {N N' : w64}
    (h : IsQuorumIndex S f N) (h' : IsQuorumIndex S f N') : N = N' := by
  rcases Int.lt_trichotomy (uint.Z N) (uint.Z N') with hl | he | hl
  · exact absurd h'.2.1 (h.2.2 N' hl)
  · word
  · exact absurd h.2.1 (h'.2.2 N hl)

theorem majIdx_unique {S : GSet w64} {f : w64 → w64} {N N' : w64}
    (h : MajIdx S f N) (h' : MajIdx S f N') : N = N' := by
  by_cases hS : S = ∅
  · rw [h.1 hS, h'.1 hS]
  · exact isQuorumIndex_unique (h.2 hS) (h'.2 hS)

theorem jCommittedIdx_unique {s0 s1 : GSet w64} {f : w64 → w64} {N N' : w64}
    (h : JCommittedIdx s0 s1 f N) (h' : JCommittedIdx s0 s1 f N') : N = N' := by
  obtain ⟨N0, N1, H0, H1, HN⟩ := h
  obtain ⟨N0', N1', H0', H1', HN'⟩ := h'
  rw [HN, HN', majIdx_unique H0 H0', majIdx_unique H1 H1']

/-- **`maybeCommit`'s outcome is unique** at `Progress` maps of the same `Match` values. -/
theorem maybeCommitOut_unique {c : CfgM} {s : NState} {pvs pvs' : GMap w64 Progress} {b b' : Bool} {N N' : w64}
    (h : maybeCommitOut c { s with prvals := pvs } b N) (h' : maybeCommitOut c { s with prvals := pvs' } b' N')
    (hm : prvalsMatch pvs' = prvalsMatch pvs) : b = b' ∧ N = N' := by
  have he : pvsMatchAt pvs' = pvsMatchAt pvs := by
    funext v
    unfold pvsMatchAt pvsAcked
    have := congrArg (fun g => g !! v) hm
    simp only [lookup_prvalsMatch] at this
    change ((pvs' !! v).map Progress.matched).getD (W64 0) = ((pvs !! v).map Progress.matched).getD (W64 0)
    rw [this]
  obtain ⟨hJ, hb⟩ := h
  obtain ⟨hJ', hb'⟩ := h'
  simp only at hJ hJ' hb hb'
  rw [he] at hJ'
  have hN := jCommittedIdx_unique hJ hJ'
  subst hN
  refine ⟨?_, rfl⟩
  cases b <;> cases b' <;> simp_all

/-- The state after the outcome, its `Progress` map aside: the commit index the outcome's. -/
theorem commitAt_prvals (s : NState) (pvs : GMap w64 Progress) (b : Bool) (N : w64) :
    commitAt { s with prvals := pvs } b N = { commitAt s b N with prvals := pvs } := by
  cases b <;> rfl

/-- The idle server's part reads the `Progress` values only through their `Match` values. -/
theorem simIdleS_prvalsEq (C : List w64) (s : NState) (pvs pvs' : GMap w64 Progress)
    (h : prvalsMatch pvs = prvalsMatch pvs') :
    SimIdleS C { s with prvals := pvs } = SimIdleS C { s with prvals := pvs' } := by
  have : toPState { s with prvals := pvs } = toPState { s with prvals := pvs' } := by
    simp only [toPState, h]
  unfold SimIdleS
  rw [this]

/-- **The idle relation past the commit**: the server's commit index raised to the outcome's. -/
theorem simServerR_commitAt (C : List w64) (bl : Nat) (Y : NState) (a : Etcdraft.Server) (b : Bool) (N : w64)
    (hR : SimServerR C bl (toPState Y) a)
    (hle : uint.Z Y.logst.committed ≤ uint.Z (commitAt Y b N).logst.committed) :
    SimServerR C bl (toPState (commitAt Y b N))
      { a with commitIndex := max a.commitIndex (uint.Z (commitAt Y b N).logst.committed) } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := hR
  have h7c : a.commitIndex = uint.Z Y.logst.committed := h7
  have h7' : max a.commitIndex (uint.Z (commitAt Y b N).logst.committed) =
      uint.Z (commitAt Y b N).logst.committed := by omega
  cases b
  · exact ⟨h1, h2, h3, h4, h5, h6, h7', h8, h9, h10, h11⟩
  · exact ⟨h1, h2, h3, h4, h5, h6, h7', h8, h9, h10, h11⟩

theorem toPState_prvalsEq (s : NState) (pvs pvs' : GMap w64 Progress) (h : prvalsMatch pvs = prvalsMatch pvs') :
    toPState { s with prvals := pvs } = toPState { s with prvals := pvs' } := by
  simp only [toPState, h]

/-- **The end state of an accepted append response of the leader's term** (`stepLeader`'s
`AppRespAcceptedC`): the commit index `n` (the outcome's when `maybeCommit` ran, else unchanged), the
`Progress` values at `appRespMatch`'s `Match` values, the log otherwise unchanged, the idle server's part
the one of `s` at those. -/
theorem leadAcc_end {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hp : LeadAcc s m) (h : StepFnEnd c id s m ents ctx s') :
    ∃ (pvs : GMap w64 Progress) (n : w64), prvalsMatch pvs = appRespMatch s m.From' m.Index' ∧
      (AppRespRan s m.From' m.Index' → ∃ (b : Bool) (N : w64),
        maybeCommitOut c { s with prvals := pvs } b N ∧ n = (commitAt s b N).logst.committed) ∧
      (¬ AppRespRan s m.From' m.Index' → n = s.logst.committed) ∧
      s'.logst = { s.logst with committed := n } ∧
      ∀ C, SimIdleS C s' = SimIdleS C { s with logst := { s.logst with committed := n }, prvals := pvs } := by
  obtain ⟨ht, hrej, -, hr, hfp, -, -⟩ := hp
  obtain ⟨d, hres⟩ := h.2.2 hr
  unfold LeaderStepResultC LeaderNonpropResultC at hres
  rw [ht] at hres
  simp [MsgAppResp, MsgVoteResp, MsgProp, MsgBeat, MsgHeartbeatResp, MsgReadIndex, MsgForgetLeader,
    MsgTimeoutNow, MsgUnreachable, MsgSnapStatus, MsgTransferLeader, MsgCheckQuorum, MsgApp, MsgHeartbeat,
    MsgPreVoteResp, MsgReadIndexResp, hrej, hfp] at hres
  obtain ⟨-, x, pvs, n, hb, ms, hx, hpm, -, hran, hnran, -, hend⟩ := hres
  have hpm' : prvalsMatch pvs = appRespMatch s m.From' m.Index' := by
    rw [appRespMatch_of_some s _ _ x hx]; exact hpm
  refine ⟨pvs, n, hpm', hran, hnran, ?_, ?_⟩
  · split at hend
    · obtain ⟨-, rfl⟩ := hend; rfl
    · rcases hend with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · rfl
      · obtain ⟨o, r, he⟩ := readRespondAll_eq id
          { s with logst := { s.logst with committed := n }, rd := { s.rd with pend := [] } }
          (pendReqs { s with logst := { s.logst with committed := n } })
        show (sendMsgs (readRespondAll id _ _) ms).logst = _
        rw [he]; rfl
  · intro C
    split at hend
    · obtain ⟨-, rfl⟩ := hend; rfl
    · rcases hend with ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩
      · rfl
      · obtain ⟨o, r, he⟩ := readRespondAll_eq id
          { s with logst := { s.logst with committed := n }, rd := { s.rd with pend := [] } }
          (pendReqs { s with logst := { s.logst with committed := n } })
        show SimIdleS C { sendMsgs (readRespondAll id _ _) ms with prvals := pvs } = _
        rw [he]; rfl

end pure

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **A leader's full log of its term is its log** (uncompacted; `ownLogGhost_lead_full`). -/
theorem ownRaftGhost_leadFull (γ : RaftNames) (id : w64) (s : PState) {md : Bool}
    (hr : s.role = .leader) (hb : s.base = base0) :
    ownRaftGhost (GF := GF) γ id s md ⊢ leadFull γ s.term s.log ∗ ownRaftGhost γ id s md := by
  iintro Hg
  ihave #Hl := ownRaftGhost_isLeader γ id s hr $$ Hg
  iunfold ownRaftGhost at Hg
  icases Hg with ⟨%γs, %V, %πc, %kl, H⟩
  iNamed H
  icases ownLogGhost_lead_full γ id s kl (virt V πc) hr $$ Hl Hlg with ⟨⟨%fp, #Hp, #Hpf, -⟩, Hlg⟩
  ihave ⟨-, %Hfp⟩ := lpfull_fp γ id s.term s.base s.log fp $$ Hpf
  have hfp : fp = [] := by
    have h := Hfp.1.1; rw [hb, base0_index] at h; exact List.eq_nil_of_length_eq_zero (by omega)
  subst hfp
  ihave #Hf := leadFull_intro γ id s.term s.base s.log [] $$ Hp Hpf
  rw [List.nil_append]
  isplitr [Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd]
  · iexact Hf
  iunfold ownRaftGhost
  iexists γs, V, πc, kl
  iframe Hslot Hvirt Hpend Hout Htally Hlead Hlg Hlcm Hrd
  ipureintro; exact ⟨Hsname, Hfresh, Hidnz, Hhist, Hlead_ok, Hfollower_votes, Hrole_ok, Hmode⟩

/-- **The family past `maybeCommit`** (see the header). -/
def leadAccGc (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (Λ : Option TraceEv → Prop) (b : Bool) (N : w64) (o : List Msg) : IProp GF :=
  iprop(∃ pvs : GMap w64 Progress, ⌜prvalsMatch pvs = appRespMatch s m.From' m.Index' ∧
      maybeCommitOut c { s with prvals := pvs } b N ∧ AppRespRan s m.From' m.Index' ∧ c.outgoing = ∅⌝ ∗
    lineF γ md c r id (commitAt { s with prvals := pvs } b N)
      (fun C => SimIdleS C (commitAt { s with prvals := pvs } b N)) (stepLastEv Λ) o)

/-- **A local family's gate with no message** (`"#Hgatnow"`: a `MsgTimeoutNow` to a transferee, untraced
and not queued here). -/
theorem lineF_none (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (X : NState)
    (Φs : List w64 → ServerC → Prop) (Λ : Option TraceEv → Prop) (o : List Msg) (htr : X.gh.tr = some γd) :
    lineF (GF := GF) γ md c r id X Φs Λ o ⊢ HookGateOpt X.gh.tr r none (lineF γ md c r id X Φs Λ o) := by
  unfold lineF
  rw [htr]
  iintro ⟨Hgh, ⟨%b, Hf⟩, %Hok⟩
  unfold trFam
  iapply hookGateOpt_mono (some γd) r none
    iprop((ownStepGhost γ md c id X ∗ ⌜OutOk X o⌝) ∗ trCapB (some γd) γ r id c b (PhaseAt Φs o) Λ)
  isplitr
  · iintro ⟨⟨Hgh, %Hok'⟩, Hc⟩
    iframe Hgh
    isplitl [Hc]
    · iexists b; iexact Hc
    ipureintro; exact Hok'
  iapply trCapB_gateNone γd γ r id c b _ _ Λ _ (fun _ _ _ h => h)
  iframe Hgh Hf
  ipureintro; exact Hok

/-- **`"Hgcommit"` on the accepted response's family** (see the header): from the receive line's result
(`AccPin`) and raft's ghost state at `s`, raft's ghost state moved past the commit and the `Commit` line,
into the family past `maybeCommit`. -/
theorem leadAccGate_commit (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64)
    (s : NState) (m : MessageM) (ents : List EntryM) (Λ : Option TraceEv → Prop) (C0 : List w64)
    (cs1 : ServerC) (P0 : List Etcdraft.Msg) (pvs : GMap w64 Progress) (b : Bool) (N : w64)
    (htr : s.gh.tr = some γd) (hp : LeadAcc s m) (hto : m.To' = id) (hran : AppRespRan s m.From' m.Index')
    (hpvs : prvalsMatch pvs = appRespMatch s m.From' m.Index')
    (hout : maybeCommitOut c { s with prvals := pvs } b N)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (£ 1 ∗ isMessage γ (absMsg .appResp m ents) ∗ ownStepGhost γ md c id s ∗
      trCapB (some γd) γ r id c true (AccPin s C0 cs1 P0 m.From' m.Index') (fun o => o.isSome = true) :
      IProp GF) ⊢
      HookGate (some γd) r (NodeEvOf rsmCommit id (commitAt s b N) c)
        (leadAccGc γ md c r id s m Λ b N s.outbox) := by
  obtain ⟨hty, hrej, hterm, hrole, -, -, hpok⟩ := hp
  have hlp : (toPState s).role = .leader := by rw [toPState_role, hrole]; rfl
  have hx : ∃ x, prvalsMatch s.prvals !! m.From' = some x := by
    obtain ⟨p, hp, -⟩ := hran
    exact ⟨p.matched, by rw [lookup_prvalsMatch, hp]; rfl⟩
  have hev : NodeEvOf rsmCommit id (commitAt { s with prvals := pvs } b N) c =
      NodeEvOf rsmCommit id (commitAt s b N) c := by
    rw [commitAt_prvals]; exact nodeEvOf_prvals _ _ _ _ _
  rw [← hev]
  iintro ⟨Hlc, #Hm, Hgh, Hc⟩
  iapply hookGate_fupd
  -- the response's index within the log, the leader's term non-zero (at `s`)
  ihave #Hai := isMessage_appResp_ackIn γ (absMsg .appResp m ents) rfl hrej $$ Hm
  ihave Hai' := ackIn_cast γ (show (absMsg .appResp m ents).term = (toPState s).term from hterm)
    (show (absMsg .appResp m ents).index = m.Index' from rfl) $$ Hai
  iunfold ownStepGhost at Hgh
  icases Hgh with ⟨Hg, Hrest⟩
  icases ownRaftGhost_ackIn_le γ id (toPState s) m.Index' hlp $$ Hg Hai' with ⟨%Hidx, Hg⟩
  ihave %HT0 := ownRaftGhost_term_nz γ id (toPState s) (by rw [hlp]; decide) $$ Hg
  ihave Hgh : ownStepGhost γ md c id s $$ [Hg Hrest]
  · iunfold ownStepGhost; iframe Hg Hrest
  -- raft's ghost state past the commit
  imod ghost_stepAppCommit γ md c id s m ents pvs b N hty hto hterm hrole hrej hx hpvs hout $$ Hlc Hm Hgh
    with Hgh
  imod ownStepGhost_traceBound (GF := GF) γ md c id (commitAt { s with prvals := pvs } b N) hfit $$ Hgh
    with ⟨%Hb, Hgh⟩
  -- the capability's pin, the voters
  icases trCapB_out γd γ r id c true _ _ $$ Hc with ⟨%Hout0, Hc⟩
  icases trCapB_pinMem γd γ r id c true _ _ $$ Hc with ⟨%C1, %cs2, %P1, %HΦ, Hc⟩
  icases trCapB_pinPerm γd γ r id c true _ _ C1 (fun _ _ _ h => h.1) $$ Hc with ⟨%hperm, Hc⟩
  obtain ⟨⟨hC1, hcs2, hP1', ⟨pvsA, hpvsA, a1, ha1, hR1, hs1, hP1, bt, bc, bl⟩, -⟩, hidC⟩ := HΦ
  subst hC1 hcs2 hP1'
  have hnd : C1.Nodup := hperm.nodup_iff.1 (GMap.NoDup_elements _)
  have hin : c.incoming = GMap.listToSet C1 := gset_eq_listToSet hperm
  have hne : C1 ≠ [] := List.ne_nil_of_mem hidC
  have hYp : toPState { s with prvals := pvsA } = toPState { s with prvals := pvs } :=
    toPState_prvalsEq s pvsA pvs (hpvsA.trans hpvs.symm)
  have hRY : SimServerR C1 C1.length (toPState { s with prvals := pvs }) a1 := by rw [← hYp]; exact hR1
  have hsY : LogShapeOk C1.length (toPState { s with prvals := pvs }) := by rw [← hYp]; exact hs1
  have hs0 : LogShapeOk C1.length (toPState s) := hs1
  have hb00 : uint.Z (toPState s).base.index' = 0 := by rw [hs0.1]; rfl
  have hL : uint.Z (logLast s.logst) = ((toPState s).log.length : Int) := by
    rw [logLast_eq_plastIndex]; exact plastIndex_length C1.length (toPState s) hs0
  have hidxL : uint.Z m.Index' ≤ ((toPState s).log.length : Int) := by
    simp only [plogLastIndexZ] at Hidx; omega
  have hm : ∀ v x, prvalsMatch ({ s with prvals := pvs } : NState).prvals !! v = some x →
      uint.Z x ≤ (toPState { s with prvals := pvs }).log.length := fun v x h =>
    appRespMatch_le s _ _ _ hrole hpok hL hidxL v x (by rw [← hpvs]; exact h)
  have hadv := advancesTo_of_out C1 hnd c { s with prvals := pvs } a1 b N hRY hrole hsY hin Hout0 hne HT0 hm hout
  -- the state after the commit
  have hXr : (commitAt { s with prvals := pvs } b N).role = .leader := by cases b <;> exact hrole
  have hXlp : (toPState (commitAt { s with prvals := pvs } b N)).role = .leader := by
    rw [toPState_role, hXr]; rfl
  have hbX : (toPState (commitAt { s with prvals := pvs } b N)).base = base0 := by cases b <;> exact hs1.1
  have hlenX : (toPState (commitAt { s with prvals := pvs } b N)).log.length = (toPState s).log.length := by
    cases b <;> rfl
  have hle : uint.Z ({ s with prvals := pvs } : NState).logst.committed ≤
      uint.Z (commitAt { s with prvals := pvs } b N).logst.committed := by
    cases b
    · exact Int.le_refl _
    · exact Int.le_of_lt (hout.2.1 rfl).2.1
  -- raft's facts of the log after the commit
  iunfold ownStepGhost at Hgh
  icases Hgh with ⟨Hg, Hrest⟩
  ihave %Hok := ownRaftGhost_logOk γ id (toPState (commitAt { s with prvals := pvs } b N)) $$ Hg
  icases ownRaftGhost_logFacts γ id (toPState (commitAt { s with prvals := pvs } b N)) hbX $$ Hg
    with ⟨Hg, ⟨#Hr, #Hcm, #Hci⟩, -⟩
  ihave #Hl := ownRaftGhost_isLeader γ id (toPState (commitAt { s with prvals := pvs } b N)) hXlp $$ Hg
  icases ownRaftGhost_leadFull γ id (toPState (commitAt { s with prvals := pvs } b N)) hXlp hbX $$ Hg
    with ⟨#Hf, Hg⟩
  ihave Hgh : ownStepGhost γ md c id (commitAt { s with prvals := pvs } b N) $$ [Hg Hrest]
  · iunfold ownStepGhost; iframe Hg Hrest
  have hLX : plogLastIndexZ (toPState (commitAt { s with prvals := pvs } b N)).base
      (toPState (commitAt { s with prvals := pvs } b N)).log =
      (toPState (commitAt { s with prvals := pvs } b N)).log.length := by
    unfold plogLastIndexZ; rw [hbX, base0_index]; simp
  have hcl : uint.Z (commitAt { s with prvals := pvs } b N).logst.committed ≤
      (toPState (commitAt { s with prvals := pvs } b N)).log.length := by
    have := Hok.2.2; rw [hLX] at this; exact this
  rw [show (toPState (commitAt { s with prvals := pvs } b N)).commit =
      (commitAt { s with prvals := pvs } b N).logst.committed from rfl,
    show (toPState (commitAt { s with prvals := pvs } b N)).term =
      (commitAt { s with prvals := pvs } b N).term from rfl]
  -- the line's source phase, from the receive line's result
  have hlen63 : ((toPState s).log.length : Int) < 2 ^ 63 := by
    have := plastIndex_length _ _ hs0
    have hbl : uint.Z (plastIndex (toPState s)) < 2 ^ 63 := bl
    omega
  have hsrcP : CommitSrc (commitAt { s with prvals := pvs } b N) C1 cs2 P1
      (uint.Z (commitAt { s with prvals := pvs } b N).logst.committed) C1 cs2 P1 := by
    refine ⟨rfl, rfl, rfl, a1, ha1, ?_, hadv, _, rfl,
      simServerR_commitAt C1 C1.length _ a1 b N hRY hle, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hRY.2.1]; simp [toPState, hrole, proleRole, roleAbs]
    · cases b <;> exact hs1
    · cases b <;> exact hP1
    · cases b <;> exact bt
    · rw [hlenX] at hcl; omega
    · cases b <;> exact bl
  have hTn : uint.nat (commitAt { s with prvals := pvs } b N).term < traceNumBound := by
    have : (commitAt { s with prvals := pvs } b N).term = s.term := by cases b <;> rfl
    rw [this]; word
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  ihave Hc := trCapB_mono (some γd) γ r id c true _
    (CommitSrc (commitAt { s with prvals := pvs } b N) C1 cs2 P1
      (uint.Z (commitAt { s with prvals := pvs } b N).logst.committed)) _
    (fun C cs P h => by obtain ⟨rfl, rfl, rfl, -⟩ := h; exact hsrcP) $$ Hc
  ihave Hfx := fxPres_commit (GF := GF) γ id (NodeEvOf rsmCommit id (commitAt { s with prvals := pvs } b N) c)
    (commitAt { s with prvals := pvs } b N) C1 cs2 P1 (uint.Z (commitAt { s with prvals := pvs } b N).logst.committed)
    hidC hXr hcl $$ [$Hr $Hcm $Hci $Hl $Hf]
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGate_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true
      (CommitTgt (commitAt { s with prvals := pvs } b N) C1 cs2 P1
        (uint.Z (commitAt { s with prvals := pvs } b N).logst.committed)) (stepLastEv Λ) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    unfold leadAccGc
    iexists pvs
    isplitr
    · ipureintro; exact ⟨hpvs, hout, hran, Hout0⟩
    unfold lineF trFam
    have hXtr : (commitAt { s with prvals := pvs } b N).gh.tr = some γd := by rw [commitAt_gh]; exact htr
    rw [hXtr]
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun C cs P h => by
        have := simIdle_phaseAt C _ cs P h.2.2.2
        cases b <;> exact this) $$ Hc
    ipureintro; cases b <;> exact outOk_self _
  iapply trCapB_hookGate (some γd) γ r id c tl _ true _ _ (fun o => o.isSome = true) (stepLastEv Λ) iprop(emp)
    (phaseStepB_commitPin id c (commitAt { s with prvals := pvs } b N) C1 cs2 P1
      (uint.Z (commitAt { s with prvals := pvs } b N).logst.committed))
    (fun h => by cases h) (fun _ _ => .inr rfl)
    (fun _ e he => nodeEvOf_ok rsmCommit id _ c e _ he (by unfold rsmCommit; decide) hTn Hb.1 Hb.2 (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hc Hfx

/-- The state after the outcome agrees with the gates' (`commitAt s b N`) in the header a send reads. -/
theorem commitAt_hdr (s : NState) (pvs : GMap w64 Progress) (b : Bool) (N : w64) :
    (commitAt { s with prvals := pvs } b N).term = (commitAt s b N).term ∧
    (commitAt { s with prvals := pvs } b N).vote = (commitAt s b N).vote ∧
    (commitAt { s with prvals := pvs } b N).logst = (commitAt s b N).logst ∧
    (commitAt { s with prvals := pvs } b N).role = (commitAt s b N).role := by
  cases b <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- **`"#Hgaapp"` on the family past `maybeCommit`**: `lineF_app` at the state after the outcome. -/
theorem leadAccGate_app (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (Λ : Option TraceEv → Prop) (b : Bool) (N to : w64) (mm : Msg) (o : List Msg)
    (htr : s.gh.tr = some γd) (hrole : s.role = .leader) (hlrn : c.learners = ∅)
    (hdomc : domSet s.progress ⊆ c.voters ∪ c.learners)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound)
    (hto : to ≠ id ∧ to ∈ domSet s.progress)
    (happ : AppOk id (toPState (commitAt s b N)) mm ∧ mm.commit = (commitAt s b N).logst.committed ∧
      mm.dst = to ∧ uint.Z ((appRespMatch s m.From' m.Index' !! to).getD (W64 0)) ≤ uint.Z mm.index ∧
      mm.rejecthint = W64 0) :
    leadAccGc (GF := GF) γ md c r id s m Λ b N o ⊢
      HookGateOpt s.gh.tr r (sendOutGate id (commitAt s b N) c MsgApp [mm])
        (leadAccGc γ md c r id s m Λ b N (o ++ [mm])) := by
  obtain ⟨hok, hcm, hdst, hmatch, hrh⟩ := happ
  unfold leadAccGc
  iintro ⟨%pvs, %Hp, HF⟩
  obtain ⟨hpvs, hout, hran, hout0⟩ := Hp
  obtain ⟨h1, h2, h3, h4⟩ := commitAt_hdr s pvs b N
  have hXtr : (commitAt { s with prvals := pvs } b N).gh.tr = some γd := by rw [commitAt_gh]; exact htr
  have hXT : (commitAt { s with prvals := pvs } b N).term = s.term := by cases b <;> rfl
  have hXp : (commitAt { s with prvals := pvs } b N).prvals = pvs := by cases b <;> rfl
  rw [← sendOutGate_hdr id _ _ c MsgApp [mm] h1 h2 h3 h4, htr, ← hXtr]
  iapply hookGateOpt_mono _ r _
    (lineF γ md c r id (commitAt { s with prvals := pvs } b N)
      (fun C => SimIdleS C (commitAt { s with prvals := pvs } b N)) (stepLastEv Λ) (o ++ [mm]))
  isplitr
  · iintro H
    iexists pvs
    iframe H
    ipureintro; exact ⟨hpvs, hout, hran, hout0⟩
  iapply lineF_app γd γ md c r id (commitAt { s with prvals := pvs } b N) Λ mm o hXtr
    (by cases b <;> exact hrole) (by rw [hXT]; exact hT) hfit
    (by rw [hdst]; exact mem_incoming_of c to hlrn hout0 ((GMap.elem_of_subseteq _ _).1 hdomc _ hto.2))
    ((appOk_hdr id _ _ mm h1 h3).2 hok) (by rw [hcm, h3]) (by rw [hXp, hpvs, hdst]; exact hmatch) hrh
  iexact HF

/-- **`"#Hgrlhb"` on the family past a committing `maybeCommit`**: `lineF_heartbeat` at the committed
state. -/
theorem leadAccGate_hb (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (Λ : Option TraceEv → Prop) (N to cm : w64) (cl : List w8) (o : List Msg)
    (htr : s.gh.tr = some γd) (hrole : s.role = .leader) (hlrn : c.learners = ∅)
    (hdomc : domSet s.progress ⊆ c.voters ∪ c.learners)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound)
    (hto : to ≠ id ∧ to ∈ domSet s.progress)
    (hcm : uint.Z cm = min (uint.Z N) (uint.Z ((appRespMatch s m.From' m.Index' !! to).getD (W64 0)))) :
    leadAccGc (GF := GF) γ md c r id s m Λ true N o ⊢
      HookGateOpt s.gh.tr r
        (sendOutGate id (commitAt s true N) c MsgHeartbeat
          [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])
        (leadAccGc γ md c r id s m Λ true N
          (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl])) := by
  unfold leadAccGc
  iintro ⟨%pvs, %Hp, HF⟩
  obtain ⟨hpvs, hout, hran, hout0⟩ := Hp
  obtain ⟨h1, h2, h3, h4⟩ := commitAt_hdr s pvs true N
  have hXtr : (commitAt { s with prvals := pvs } true N).gh.tr = some γd := by rw [commitAt_gh]; exact htr
  have hXT : (commitAt { s with prvals := pvs } true N).term = s.term := rfl
  rw [← sendOutGate_hdr id _ _ c MsgHeartbeat _ h1 h2 h3 h4, htr, ← hXtr]
  iapply hookGateOpt_mono _ r _
    (lineF γ md c r id (commitAt { s with prvals := pvs } true N)
      (fun C => SimIdleS C (commitAt { s with prvals := pvs } true N)) (stepLastEv Λ)
      (o ++ [Msg.mkV .heartbeat id to s.term false (W64 0) (W64 0) cm (W64 0) [] [] cl]))
  isplitr
  · iintro H
    iexists pvs
    iframe H
    ipureintro; exact ⟨hpvs, hout, hran, hout0⟩
  have H := lineF_heartbeat (GF := GF) γd γ md c r id (commitAt { s with prvals := pvs } true N) Λ to cm cl o
    hXtr hrole hto.1 ((GMap.elem_of_subseteq _ _).1 hdomc _ hto.2) hlrn
    (by show uint.Z cm = min (uint.Z N) (uint.Z ((prvalsMatch pvs !! to).getD (W64 0))); rw [hpvs]; exact hcm)
    hT hfit
  rw [hXT] at H
  iapply H
  iexact HF

/-- **`"#Hgrlresp"` on the family past a committing `maybeCommit`**: an untraced read-index response. -/
theorem leadAccGate_resp (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (Λ : Option TraceEv → Prop) (b : Bool) (N : w64) (mm : Msg) (o : List Msg)
    (htr : s.gh.tr = some γd) (hmm : mm.ty = .readIndexResp) :
    leadAccGc (GF := GF) γ md c r id s m Λ b N o ⊢
      HookGateOpt s.gh.tr r none (leadAccGc γ md c r id s m Λ b N (o ++ [mm])) := by
  unfold leadAccGc
  iintro ⟨%pvs, %Hp, HF⟩
  have hXtr : (commitAt { s with prvals := pvs } b N).gh.tr = some γd := by rw [commitAt_gh]; exact htr
  rw [htr, ← hXtr]
  iapply hookGateOpt_mono _ r _
    (lineF γ md c r id (commitAt { s with prvals := pvs } b N)
      (fun C => SimIdleS C (commitAt { s with prvals := pvs } b N)) (stepLastEv Λ) (o ++ [mm]))
  isplitr
  · iintro H
    iexists pvs
    iframe H
    ipureintro; exact Hp
  iapply lineF_untraced γd γ md c r id _ _ _ mm o hXtr (by rw [hmm]; rfl) $$ HF

/-- **`"#Hgatnow"` on the family past `maybeCommit`**: no message. -/
theorem leadAccGate_tnow (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (Λ : Option TraceEv → Prop) (b : Bool) (N : w64) (o : List Msg)
    (htr : s.gh.tr = some γd) :
    leadAccGc (GF := GF) γ md c r id s m Λ b N o ⊢
      HookGateOpt s.gh.tr r none (leadAccGc γ md c r id s m Λ b N o) := by
  unfold leadAccGc
  iintro ⟨%pvs, %Hp, HF⟩
  have hXtr : (commitAt { s with prvals := pvs } b N).gh.tr = some γd := by rw [commitAt_gh]; exact htr
  rw [htr, ← hXtr]
  iapply hookGateOpt_mono _ r _
    (lineF γ md c r id (commitAt { s with prvals := pvs } b N)
      (fun C => SimIdleS C (commitAt { s with prvals := pvs } b N)) (stepLastEv Λ) o)
  isplitr
  · iintro H
    iexists pvs
    iframe H
    ipureintro; exact Hp
  iapply lineF_none γd γ md c r id _ _ _ o hXtr $$ HF

end ghost

end EtcdGrove
end Perennial
