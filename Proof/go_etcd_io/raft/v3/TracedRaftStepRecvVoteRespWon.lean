/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a candidate's `MsgVoteResp` of its
term that wins the election** (2026-11-11, trace-check Q8 stage 1 slice 27b, `notes/decisions.md`,
"Q8 stage 1 (slice 27b)").

Raft records the vote (`poll`'s `RecordVote`), finds the election won (`JQuorum` at the step's
configuration) and becomes leader (`becomeLeader`): its `BecomeLeader` line (after `reset`), the empty
entry's `Replicate` line (`appendEntry`, before the append), the self-acknowledgement's
`SendAppendEntriesResponse` line, then `bcastAppend`'s `SendAppendEntriesRequest` lines. The family
(`vrWonR`) follows `candidateGates`' won gates:

- the receive line (`"Hgrecv"`): `HandleRequestVoteResponse` (amendment A3), its result phase carrying
  the won tally's quorum (`phaseStepR_voteRespWon`, amendment A6's premises);
- `"Hgbl"` (`wonGate_bl`): raft's facts of the candidate's log read, the win's registration
  (`ghost_stepWin_reg`), then the `BecomeLeader` line (`phaseStepB_becomeLeader`), its facts allocating
  the term log (`fxPresU_becomeLeader`);
- `"Hgrep"` (`wonGate_rep`): with what `Step` lends (`winLend`: the receipt of the entry's index and the
  node's membership of its own `Progress` map) the win's last ghost phase (`ghost_stepWin_entry`), then
  the empty entry's `Replicate` line (`phaseStepB_replicateB`, `fxPres_replicateW`);
- `"Hgack"` (`wonGate_ack`): the self-acknowledgement's line (`phaseStepB_selfAck`, `fxPres_selfAck`) at
  the appended state with `reset`'s `Match` values (`wonLg`), the share unpinned into the family `wonGE`
  indexed by the outbox;
- `"#Hgcast"` (`wonGate_app`): each append request's line (`phaseStepB_msgApp_pin`, `fxPres_app`,
  `app_lead`, the request's facts from raft's ghost state at the won state, `msgFacts_app_of_log`);
- the close (`wonClose`): `StepEnd`'s won outcome (`wonEnd`: the outbox grew), raft's ghost state given
  back at the won state (`CloseMid`'s second case, at `wonPvs`, `reset`'s `Match` values), the idle
  capability at the end state (`trFam_idle`; the idle relation reads the `Progress` values only through
  their `Match` values).

The bundle `stepBundle_traced_candVoteRespWon` is over `stepBundle_traced.onC` (the path reads the
step's configuration, `JQuorum`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvVoteRespWonFx

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- **A candidate's vote response of its term that wins the election**: the recorded tally a joint
quorum of grants at the step's configuration (`poll`'s `VoteWon`). -/
def CandVoteRespWon (c : CfgM) (s : NState) (m : MessageM) : Prop :=
  m.Type' = MsgVoteResp ∧ m.Term' = s.term ∧ s.role = .candidate ∧
  JQuorum c (granted (recordVote s.votes m.From' (!m.Reject')))

/-- **The idle server at the won end state** is the appended state's at `reset`'s `Match` values: the
idle relation reads neither the outbox nor the `Progress` values beyond their `Match` values. -/
theorem simIdleS_wonEnd (C : List w64) (id : w64) (s : NState) (m : MessageM) (ms : List Msg)
    (pvs : GMap w64 Progress) (hid : id ∈ domSet s.prvals)
    (hpm : prvalsMatch pvs = resetMatched id (logLast s.logst) s.prvals) :
    SimIdleS C (wonLg id s m) = SimIdleS C { sendMsgs (becomeLeader id (votedState s m)) ms with prvals := pvs } := by
  have h := simIdleS_prvals C (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)) ms pvs
    (by show prvalsMatch pvs = prvalsMatch (wonPvs id (logLast s.logst) s.prvals)
        rw [hpm, wonPvs_reset _ _ _ hid])
  exact h.symm

/-- The appended state's self-acknowledgement is `becomeLeader`'s. -/
theorem selfAck_wonLg (id : w64) (s : NState) (m : MessageM) :
    selfAck id (wonLg id s m) = selfAck id (becomeLeaderLog id (votedState s m)) := rfl

theorem sendEvOf_wonLg (evt id : w64) (s : NState) (m : MessageM) (c : CfgM) (mm : Msg) :
    SendEvOf evt id (wonLg id s m) c mm = SendEvOf evt id (becomeLeaderLog id (votedState s m)) c mm := rfl

theorem sendEvOf_wonLg_bl (evt id : w64) (s : NState) (m : MessageM) (c : CfgM) (mm : Msg)
    (pvs : GMap w64 Progress) :
    SendEvOf evt id (wonLg id s m) c mm =
      SendEvOf evt id ({ becomeLeader id (votedState s m) with prvals := pvs } : NState) c mm := rfl

/-- The appended state's last index: the candidate's log and the empty entry. -/
theorem logLast_wonLg (id : w64) (s : NState) (m : MessageM) (hb0 : s.logst.prev = base0)
    (hlen : (toPState s).log.length + 1 < 2 ^ 64) :
    uint.Z (logLast (wonLg id s m).logst) = (toPState s).log.length + 1 := by
  have h0 : uint.Z s.logst.prev.index' = 0 := by rw [hb0]; rfl
  simp only [toPState, List.length_append] at hlen ⊢
  simp only [wonLg, becomeLeaderLog, becomeLeaderPre, resetTo, resetTo0, logLast, logAppend, List.length_append,
    List.length_singleton]
  rw [h0]
  push_cast
  word

end pure

section families
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **After the `BecomeLeader` line**: the win pending its last phase (`winGhost`), raft's facts of the
candidate's log and its registration, the term's full log, the numbers the next lines read, the
capability at the leader's pinned phase. -/
def wonB1 (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (γd : GName) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) : IProp GF :=
  iprop(winGhost γ md c id s m ∗ leadFull γ s.term (toPState s).log ∗ isLeader γ id s.term ∗
    isCamp γ id s.term (toPState s).log ∗ logRecs γ base0 (toPState s).log ∗
    isCommitted γ ((toPState s).log.take (uint.Z s.logst.committed).toNat) ∗
    commitIn γ (toPState s).log s.logst.committed s.term ∗
    ⌜uint.Z s.logst.committed ≤ (toPState s).log.length ∧ C0.length ≤ (toPState s).log.length ∧
      γ.reBoot.length ≤ (toPState s).log.length ∧ s.logst.prev = base0⌝ ∗
    trCapB (some γd) γ r id c true (PinAt (wonL id s m) C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 s.outbox)
      (fun o => o.isSome = true))

/-- **After the empty entry's `Replicate` line**: raft's ghost state at the won state (`reset`'s `Match`
values, no broadcast yet), the node in its own `Progress` map, the capability pinned after the line. -/
def wonB2 (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (γd : GName) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) : IProp GF :=
  iprop(⌜id ∈ domSet s.prvals⌝ ∗ ownStepGhost γ md c id (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)) ∗
    trCapB (some γd) γ r id c true
      (RepPin (wonL id s m) [zero_val EntryM] s.outbox C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 1)
      (fun o => o.isSome = true))

/-- **After the self-acknowledgement, at the outbox `o`**: the outbox grown, raft's ghost state at the
won state, the traced family at the appended state's idle server, the new messages' numbers. -/
def wonGE (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (m : MessageM)
    (γd : GName) : List Msg → IProp GF := fun o =>
  iprop(⌜s.outbox.length < o.length⌝ ∗ ⌜id ∈ domSet s.prvals⌝ ∗
    ownStepGhost γ md c id (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)) ∗
    (∃ b : Bool, trFam (some γd) γ r id c b (fun C => SimIdleS C (wonLg id s m)) (fun o => o.isSome = true) o) ∗
    ⌜OutOk s o⌝)

theorem wonGE_permInv (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (γd : GName) : PermInv (wonGE (GF := GF) γ md c r id s m γd) := by
  intro o o' h
  unfold wonGE trFam
  rw [phaseAt_permInv _ o o' h, outOk_perm s h, h.length_eq]

/-- **A won election's resources** (see the header). -/
def vrWonR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (γd : GName) (tn : TraceNames) (cs0 cs1 : ServerC) (P0 : List Etcdraft.Msg)
    (Λ : Option TraceEv → Prop) (k : Nat) (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (WonRecvPin (votedState s m) tn.voters cs1 P0) (fun o => o.isSome = true))
  G1 := fun _ => iprop(ownStepGhost γ md c id s ∗
    trCapB (some γd) γ r id c true (WonRecvPin (votedState s m) tn.voters cs1 P0) (fun o => o.isSome = true))
  GE := wonGE γ md c r id s m γd
  Gf := iprop(⌜False⌝)
  Gb1 := wonB1 γ md c r id s m γd tn.voters cs1 P0
  Gb2 := wonB2 γ md c r id s m γd tn.voters cs1 P0
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **`"Hgbl"` on the won family**: raft's facts of the candidate's log (uncompacted), the win's
registration (`ghost_stepWin_reg`), the `BecomeLeader` line (`phaseStepB_becomeLeader`, its facts and the
term log's allocation `fxPresU_becomeLeader`). -/
theorem wonGate_bl (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg)
    (hto : m.To' = id) (hterm : m.Term' = s.term) (hrole : s.role = .candidate)
    (hq : JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))))
    (hb0 : s.logst.prev = base0) (hidC : id ∈ C0) (hfitC : C0.length ≤ γ.reBoot.length)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (isMessage γ (absMsg .voteResp m ents) ∗ ownStepGhost γ md c id s ∗
        trCapB (some γd) γ r id c true (WonRecvPin (votedState s m) C0 cs1 P0) (fun o => o.isSome = true) :
        IProp GF) ⊢
      HookGate (some γd) r (NodeEvOf (W64 3) id (becomeLeaderPre id (votedState s m)) c)
        (wonB1 γ md c r id s m γd C0 cs1 P0) := by
  iintro ⟨#Hm, Hgh, Hc⟩
  iapply hookGate_fupd
  imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
  -- raft's facts of the candidate's log
  iunfold ownStepGhost at Hgh
  icases Hgh with ⟨Hg, Hrest⟩
  ihave %Hok := ownRaftGhost_logOk γ id (toPState s) $$ Hg
  icases ownRaftGhost_logFacts γ id (toPState s) hb0 $$ Hg with ⟨Hg, ⟨#Hr0, #Hcm, #Hci⟩, -⟩
  rw [show (toPState s).commit = s.logst.committed from rfl, show (toPState s).term = s.term from rfl]
  ihave Hgh : ownStepGhost γ md c id s $$ [Hg Hrest]
  · iunfold ownStepGhost; iframe Hg Hrest
  -- the registration
  imod ghost_stepWin_reg γ md c id s m ents hto hterm hrole hq $$ Hm Hgh
    with ⟨#Hl, %fp, %Hfp, #Hcp, -, %γm, %terms, %Hfree, Ha, Hw⟩
  have hfp : fp = [] := by
    have h := Hfp.1; rw [show (toPState s).base = base0 from hb0, base0_index] at h
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hfp
  rw [List.nil_append]
  icases isCamp_boot γ id s.term (toPState s).log $$ Hcp with %Hbt
  have hbb : γ.reBoot.length ≤ (toPState s).log.length := Hbt.1.length_le
  have hboot : γ.reBoot ≠ [] :=
    List.ne_nil_of_length_pos (Nat.lt_of_lt_of_le (List.length_pos_of_mem hidC) hfitC)
  have hL : plogLastIndexZ (toPState s).base (toPState s).log = (toPState s).log.length := by
    unfold plogLastIndexZ; rw [show (toPState s).base = base0 from hb0, base0_index]; simp
  have hcl : uint.Z s.logst.committed ≤ (toPState s).log.length := by
    have := Hok.2.2; rw [hL] at this; exact this
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  imodintro
  iapply hookGate_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true (PinAt (wonL id s m) C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 s.outbox)
      (fun o => o.isSome = true) ∗ (leadFull γ s.term (toPState s).log ∗ winGhost γ md c id s m))
  isplitr
  · iintro ⟨Hc, #Hf, Hwg⟩
    unfold wonB1
    iframe Hwg Hf Hl Hcp Hr0 Hcm Hci Hc
    ipureintro; exact ⟨hcl, Nat.le_trans hfitC hbb, hbb, hb0⟩
  have ht1 : uint.nat (becomeLeaderPre id (votedState s m)).term < traceNumBound := by
    show uint.nat s.term < traceNumBound; word
  have hc1 : uint.nat (becomeLeaderPre id (votedState s m)).logst.committed < traceNumBound := Hb.2
  have hl1 : uint.nat (plastIndex (toPState (becomeLeaderPre id (votedState s m)))) < traceNumBound := Hb.1
  iapply trCapB_hookGate (some γd) γ r id c tl _ true _ _ (fun o => o.isSome = true) (fun o => o.isSome = true)
    iprop(leadFull γ s.term (toPState s).log ∗ winGhost γ md c id s m)
    (phaseStepB_becomeLeader id c s m C0 cs1 P0 hrole) (fun h => by cases h) (fun _ _ => rfl)
    (fun _ e he => nodeEvOf_ok (W64 3) id _ c e _ he (by decide) ht1 hc1 hl1 (Nat.le_refl _))
    (fun h => by cases h)
  iframe Htl Hc
  simp only [FxPresUT]
  iapply fxPresU_becomeLeader γ id _ s m C0 cs1 P0 hidC hrole hcl hboot γm terms Hfree.1 Hfree.2
    (winGhost γ md c id s m)
  iframe Hl Hcp Hr0 Hcm Hci Ha Hw

/-- **`"Hgrep"` on the won family**: with `Step`'s loan (`winLend`) the win's last phase
(`ghost_stepWin_entry`, at `wonPvs`), then the empty entry's `Replicate` line (`phaseStepB_replicateB`,
`fxPres_replicateW`). -/
theorem wonGate_rep (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (ents : List EntryM) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg)
    (htr : s.gh.tr = some γd) (hTy : m.Type' = MsgVoteResp) (hto : m.To' = id) (hterm : m.Term' = s.term)
    (hrole : s.role = .candidate) (hq : JQuorum c (granted (recordVote s.votes m.From' (!m.Reject'))))
    (hidC : id ∈ C0) (hT : uint.Z s.term + 1 < traceNumBound)
    (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    (winLend γ id s ∗ isMessage γ (absMsg .voteResp m ents) ∗ wonB1 γ md c r id s m γd C0 cs1 P0 : IProp GF) ⊢
      HookGateN (some γd) r (NodeEvOf (W64 5) id (becomeLeaderPre id (votedState s m)) c) 1
        (wonB2 γ md c r id s m γd C0 cs1 P0) := by
  unfold winLend wonB1
  rw [htr]
  simp only [Option.isSome_some, ↓reduceIte]
  iintro ⟨⟨%Hid, #Hrc⟩, #Hm, Hwg, #Hf, #Hl, #Hcp, #Hr, #Hcm, #Hci, %Hp, Hc⟩
  obtain ⟨hcl, hbl0, hbb, hb0⟩ := Hp
  ihave %Hlt := preceipt_lt _ $$ Hrc
  have hL : plogLastIndexZ (toPState s).base (toPState s).log = (toPState s).log.length := by
    unfold plogLastIndexZ; rw [show (toPState s).base = base0 from hb0, base0_index]; simp
  have hb : traceNumBound = 2 ^ 61 := rfl
  have hLn : (toPState s).log.length + 1 < traceNumBound := by
    rw [hL] at Hlt; simp only [Int.toNat_natCast] at Hlt; omega
  have Hnw : plogLastIndexZ (toPState s).base (toPState s).log + 1 < 2 ^ 64 := by rw [hL]; omega
  have hll := logLast_wonLg id s m hb0 (by omega)
  have hsa : MsgTrOk γ (selfAck id (becomeLeaderLog id (votedState s m))) := fun _ => by
    rw [← selfAck_wonLg]
    exact selfAck_trOk id _ (by show uint.Z s.term < traceNumBound; omega) (by rw [hll]; omega)
  iapply hookGateN_fupd
  imod ghost_stepWin_entry γ md c id s m ents (wonPvs id (logLast s.logst) s.prvals) hTy hto hterm hrole Hid hq
    (wonPvs_reset _ _ _ Hid) Hnw hsa $$ Hm Hrc Hwg with Hgh
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  ihave Hc := trCapB_mono (some γd) γ r id c true _
    (RepPin (wonL id s m) [zero_val EntryM] s.outbox C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 0) _
    (fun C cs P h => by simp only [RepPin, propK_zero, repCN]; exact h) $$ Hc
  ihave Hfx := fxPres_replicateW (GF := GF) γ id (NodeEvOf (W64 5) id (wonL id s m) c) s m s.outbox C0
    (leaderC (confAbs C0) (idAbs id) cs1) P0 hidC hbl0 hcl (by omega) $$ []
  · iframe Hf Hl Hcp Hr Hcm Hci
  imodintro
  rw [show NodeEvOf (W64 5) id (becomeLeaderPre id (votedState s m)) c = NodeEvOf (W64 5) id (wonL id s m) c
    from rfl]
  iapply hookGateN_mono (some γd) r _ _
    iprop(trCapB (some γd) γ r id c (if 1 = 0 then true else true)
      (RepPin (wonL id s m) [zero_val EntryM] s.outbox C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 1)
      (if 1 = 0 then (fun o => o.isSome = true) else (fun o => o.isSome = true)) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    unfold wonB2
    simp only [Nat.one_ne_zero, ↓reduceIte]
    iframe Hgh Hc
    ipureintro; exact Hid
  have hbnd : plogLastIndexZ (toPState (wonL id s m)).base (toPState (wonL id s m)).log +
      ([zero_val EntryM] : List EntryM).length < 2 ^ 63 := by
    show plogLastIndexZ (toPState s).base (toPState s).log + 1 < 2 ^ 63
    rw [hL]; omega
  have ht1 : uint.nat (wonL id s m).term < traceNumBound := by show uint.nat s.term < traceNumBound; word
  have hc1 : uint.nat (wonL id s m).logst.committed < traceNumBound := by
    show uint.nat s.logst.committed < traceNumBound
    have : uint.Z s.logst.committed < traceNumBound := by omega
    word
  have hl1 : uint.nat (plastIndex (toPState (wonL id s m))) < traceNumBound := by
    show uint.nat (plastIndex (toPState s)) < traceNumBound
    have h1 : uint.Z (plastIndex (toPState s)) = plogLastIndexZ (toPState s).base (toPState s).log := by
      unfold plastIndex; rw [hL]
      have : ((toPState s).log.length : Int) < 2 ^ 64 := by omega
      word
    rw [hL] at h1
    have : uint.Z (plastIndex (toPState s)) < traceNumBound := by omega
    word
  iapply trCapB_hookGateN (some γd) γ r id c tl _ true
    (fun k => RepPin (wonL id s m) [zero_val EntryM] s.outbox C0 (leaderC (confAbs C0) (idAbs id) cs1) P0 k)
    (fun o => o.isSome = true) (fun o => o.isSome = true) (fun _ => iprop(emp)) 1
    (fun k hk => by
      obtain rfl : k = 0 := by omega
      exact phaseStepB_replicateB id c (wonL id s m) [zero_val EntryM] s.outbox C0 _ P0 0 (zero_val EntryM) rfl
        rfl hbl0 hbnd)
    (fun e he => nodeEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun _ _ => rfl)
    (fun _ e he => nodeEvOf_ok (W64 5) id _ c e _ he (by decide) ht1 hc1 hl1 (Nat.le_refl _))
    (fun h => by cases h)
  iframe Htl Hc
  isplitr
  · iempintro
  rw [show List.range 1 = [0] from rfl]
  iapply BigSepL.bigSepL_singleton.2
  iintro -
  simp only [FxPresUT]
  iapply fxPres_upd
  iexact Hfx

/-- **`"Hgack"` on the won family**: the self-acknowledgement's line at the appended state
(`phaseStepB_selfAck`, `fxPres_selfAck`), the share unpinned into `wonGE`. -/
theorem wonGate_ack (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (C0 : List w64) (cs1 : ServerC) (P0 : List Etcdraft.Msg) (hidC : id ∈ C0)
    (hT : uint.Z s.term + 1 < traceNumBound) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound) :
    wonB2 (GF := GF) γ md c r id s m γd C0 cs1 P0 ⊢
      HookGateOpt (some γd) r
        (sendOutGate id (becomeLeaderLog id (votedState s m)) c MsgAppResp
          [selfAck id (becomeLeaderLog id (votedState s m))])
        (wonGE γ md c r id s m γd (s.outbox ++ [selfAck id (becomeLeaderLog id (votedState s m))])) := by
  rw [sendOutGate_selfAck, ← selfAck_wonLg, ← sendEvOf_wonLg]
  unfold wonB2 wonGE trFam
  iintro ⟨%Hid, Hgh, Hc⟩
  iapply hookGateOpt_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)) hfit
    $$ Hgh with ⟨%Hb, Hgh⟩
  icases trCapB_logger γd γ r id c true _ _ $$ Hc with ⟨%tl, #Htl, Hc⟩
  ihave Hc := trCapB_mono (some γd) γ r id c true _
    (PinAt (wonLg id s m) C0 (repCN (leaderC (confAbs C0) (idAbs id) cs1) 1) P0 s.outbox) _
    (fun C cs P h => ⟨h.1, h.2.1, h.2.2.1, by
      have h4 := h.2.2.2.1; dsimp only at h4 ⊢; rwa [simIdleS_wonL_one] at h4, h.2.2.2.2⟩) $$ Hc
  have hrole1 : (wonLg id s m).role = .leader := rfl
  have hTn : uint.nat (wonLg id s m).term < traceNumBound := by
    show uint.nat s.term < traceNumBound; word
  have hcn : uint.nat (wonLg id s m).logst.committed < traceNumBound := Hb.1
  have hln : uint.nat (plastIndex (toPState (wonLg id s m))) < traceNumBound := Hb.2
  have hok : (selfAck id (wonLg id s m)).TrOk :=
    selfAck_trOk id _ (by show uint.Z s.term < traceNumBound; omega)
      (by rw [logLast_eq_plastIndex]; word)
  obtain ⟨ma0, hma⟩ : ∃ ma0, TraceSim.msgAbs C0 C0.length (selfAck id (wonLg id s m)) = some ma0 :=
    ⟨_, rfl⟩
  ihave #Hfx := fxPres_selfAck (GF := GF) γ id
    (SendEvOf (W64 11) id (wonLg id s m) c (selfAck id (wonLg id s m))) (wonLg id s m)
    (PinAt (wonLg id s m) C0 (repCN (leaderC (confAbs C0) (idAbs id) cs1) 1) P0 s.outbox)
    (PinAt (wonLg id s m) C0 (repCN (leaderC (confAbs C0) (idAbs id) cs1) 1) (P0 ++ [ma0])
      (s.outbox ++ [selfAck id (wonLg id s m)]))
    C0 ma0 hma hrole1 (fun C cs P h => ⟨h.1, h.1 ▸ hidC, h.2.2.2.1⟩)
    (pinAt_step (wonLg id s m) C0 _ P0 s.outbox _ ma0)
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGateOpt_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true
      (PinAt (wonLg id s m) C0 (repCN (leaderC (confAbs C0) (idAbs id) cs1) 1) (P0 ++ [ma0])
        (s.outbox ++ [selfAck id (wonLg id s m)])) (fun o => o.isSome = true) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    isplitr
    · ipureintro; simp
    isplitr
    · ipureintro; exact Hid
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun _ _ _ h => h.2.2.2) $$ Hc
    ipureintro
    exact outOk_snoc (outOk_self s) hok
  iapply trCapB_hookGateOpt (some γd) γ r id c tl _ true
    (PinAt (wonLg id s m) C0 (repCN (leaderC (confAbs C0) (idAbs id) cs1) 1) P0 s.outbox) _
    (fun o => o.isSome = true) (fun o => o.isSome = true) iprop(emp)
    (phaseStepB_selfAck id c (wonLg id s m) s.outbox C0 _ P0 ma0 hma hrole1)
    (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun _ _ => rfl)
    (fun _ e he => sendEvOf_ok (W64 11) id _ c _ e _ he (by decide) hTn hcn hln (hok rfl).1 (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hc Hfx

/-- **`"#Hgcast"` on the won family**: an append request's line at the appended state
(`phaseStepB_msgApp_pin`, `fxPres_app` with `app_lead` and the request's facts from raft's ghost state at
the won state, `msgFacts_app_of_log`), the share unpinned at the outbox with the request. -/
theorem wonGate_app (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (m : MessageM) (pvs : GMap w64 Progress) (to : w64) (mm : Msg) (o : List Msg)
    (hlrn : c.learners = ∅) (hfit : receiptBound GF + γ.reBoot.length ≤ traceNumBound)
    (hT : uint.Z s.term + 1 < traceNumBound)
    (hdom : to ∈ c.voters ∪ c.learners) (hne : to ≠ id)
    (happ : AppOk id (toPState ({ becomeLeader id (votedState s m) with prvals := pvs } : NState)) mm ∧
      mm.commit = (toPState ({ becomeLeader id (votedState s m) with prvals := pvs } : NState)).commit ∧
      mm.dst = to ∧ mm.rejecthint = W64 0) :
    wonGE (GF := GF) γ md c r id s m γd o ⊢
      HookGateOpt (some γd) r
        (sendOutGate id ({ becomeLeader id (votedState s m) with prvals := pvs } : NState) c MsgApp [mm])
        (wonGE γ md c r id s m γd (o ++ [mm])) := by
  obtain ⟨hok, hcm, hdst, hrh⟩ := happ
  have hok' : AppOk id (toPState (wonLg id s m)) mm := hok
  have hcm' : mm.commit = (toPState (wonLg id s m)).commit := hcm
  rw [sendOutGate_one id _ c MsgApp mm (W64 9) rfl, ← sendEvOf_wonLg_bl]
  unfold wonGE trFam
  iintro ⟨%Hlen, %Hid, Hgh, ⟨%b, Hf⟩, %Hok⟩
  iapply hookGateOpt_fupd
  imod ownStepGhost_traceBound (GF := GF) γ md c id (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)) hfit
    $$ Hgh with ⟨%Hb, Hgh⟩
  icases trCapB_out γd γ r id c b _ _ $$ Hf with ⟨%Hout, Hf⟩
  icases trCapB_pinMem γd γ r id c b _ _ $$ Hf with ⟨%C0, %cs0, %P0, %HΦ0, Hf⟩
  icases trCapB_logger γd γ r id c b _ _ $$ Hf with ⟨%tl, #Htl, Hf⟩
  icases trCapB_pinPerm γd γ r id c b _ _ C0 (fun _ _ _ h => h.1) $$ Hf with ⟨%hperm0, Hf⟩
  obtain ⟨⟨⟨a0, -, -, hs0, -, -, bl0⟩, -⟩, hidC⟩ := HΦ0
  have hb0 : (toPState (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals))).base = base0 := hs0.1
  have hrole1 : (wonLg id s m).role = .leader := rfl
  have hrole2 : (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)).role = .leader := rfl
  icases ownStepGhost_appFacts γ md c id (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)) hrole2 hb0
    $$ Hgh with ⟨⟨#Hil, #Hrc, %Htle⟩, Hgh⟩
  have hlogeq : (toPState (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals))).log =
      (toPState (wonLg id s m)).log := rfl
  have hbeq : (toPState (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals))).base =
      (toPState (wonLg id s m)).base := rfl
  have htm : (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)).term = s.term := rfl
  have hb : traceNumBound = 2 ^ 61 := rfl
  have hloglen : ((toPState (wonLg id s m)).log.length : Int) < 2 ^ 63 := by
    have := plastIndex_length _ _ hs0; omega
  obtain ⟨hpk, hents⟩ := appOk_slice id (toPState (wonLg id s m)) mm hok' (by rw [hs0.1]; rfl) hloglen
  have hlt := hok'.2.2.2.2.1
  have hlogterm : uint.Z mm.logterm ≤ uint.Z s.term := by
    rw [← htm]; exact Htle _ _ (by rw [hlogeq, hbeq]; exact hlt)
  have hpl : plastIndex (toPState (wonLg id s m)) =
      plastIndex (toPState (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals))) := rfl
  have hTn : uint.nat (wonLg id s m).term < traceNumBound := by
    show uint.nat s.term < traceNumBound; word
  have hcn : uint.nat (wonLg id s m).logst.committed < traceNumBound := Hb.1
  have hln : uint.nat (plastIndex (toPState (wonLg id s m))) < traceNumBound := by rw [hpl]; exact Hb.2
  have hbI : (traceNumBound : Int) = 2 ^ 61 := by rw [hb]; exact Int.natCast_pow 2 61
  have hlenL : (toPState (wonLg id s m)).log.length < traceNumBound := by
    have h2 := Hb.2
    rw [← hpl] at h2
    have h3 := plastIndex_length _ _ hs0
    have : uint.Z (plastIndex (toPState (wonLg id s m))) < traceNumBound := by word
    omega
  have hnums : mm.NumsBelow traceNumBound := by
    refine ⟨?_, by omega, ?_, ?_, ?_, ?_⟩
    · rw [hok'.2.2.1]; show uint.nat s.term < traceNumBound; word
    · have : uint.Z mm.logterm < traceNumBound := by omega
      word
    · have : uint.nat mm.index ≤ (toPState (wonLg id s m)).log.length := by omega
      omega
    · rw [hcm']; exact Hb.1
    · rw [hrh]; show 0 < traceNumBound; rw [hb]; omega
  have htrok : mm.TrOk := Msg.trOk_of_nums (by rw [hok'.1]; decide) (by rw [hok'.1]; decide) (fun _ => hnums)
  obtain ⟨ma0, hma⟩ : ∃ ma0, TraceSim.msgAbs C0 C0.length mm = some ma0 := by
    simp [TraceSim.msgAbs, hok'.1]
  have hto : mm.dst ∈ elements c.incoming := by rw [hdst]; exact mem_incoming_of c to hlrn Hout hdom
  have hpt : ma0.type = .appendEntriesRequest := by simp [TraceSim.msgAbs, hok'.1] at hma; rw [← hma]
  have hps : ma0.subtype = "app" := by simp [TraceSim.msgAbs, hok'.1] at hma; rw [← hma]
  have hsrc : ma0.source = idAbs id := by
    simp [TraceSim.msgAbs, hok'.1] at hma; rw [← hma]; simp [hok'.2.1]
  have hmatch : uint.Z ((prvalsMatch (wonLg id s m).prvals !! mm.dst).getD (W64 0)) ≤ uint.Z mm.index := by
    show uint.Z ((prvalsMatch (wonPvs id (logLast s.logst) s.prvals) !! mm.dst).getD (W64 0)) ≤ _
    rw [prvalsMatch_wonPvs, hdst, if_neg hne]
    cases s.prvals !! to with
    | none => simp only [Option.map_none, Option.getD_none]; exact uint_Z_nonneg _
    | some _ => simp only [Option.map_some, Option.getD_some]; exact uint_Z_nonneg _
  ihave Hfx := fxPres_app (GF := GF) γ id (SendEvOf (W64 9) id (wonLg id s m) c mm)
    (PinAt (wonLg id s m) C0 cs0 P0 o) (PinAt (wonLg id s m) C0 cs0 (P0 ++ [ma0]) (o ++ [mm]))
    ma0 (msgAbs_canon C0 C0.length mm ma0 hma) hpt hps hsrc
    (fun C cs P h => h.1 ▸ hidC)
    (fun C _ _ h => by rw [msgAbs_dest hma, h.1]; exact (mem_confAbs C0 mm.dst).2 (hperm0.mem_iff.1 hto))
    (app_lead (wonLg id s m) C0 cs0 P0 o id mm ma0 hma hrole1 hok' hcm')
    (pinAt_step (wonLg id s m) C0 cs0 P0 o mm ma0) $$ []
  · imodintro
    iintro %C %cs %P %h
    obtain ⟨rfl, -⟩ := h
    iapply msgFacts_app_of_log γ C id (toPState (wonLg id s m)) mm ma0 hma hok' hs0.1
      (by have := hs0.2.1; rw [hs0.1] at this; exact this) hloglen
    rw [← hlogeq, show (toPState (wonLg id s m)).term =
      (wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)).term from rfl]
    iframe Hil Hrc
  ihave Hfx := fxPres_upd γ id _ _ _ $$ Hfx
  imodintro
  iapply hookGateOpt_mono (some γd) r _
    iprop(trCapB (some γd) γ r id c true (PinAt (wonLg id s m) C0 cs0 (P0 ++ [ma0]) (o ++ [mm]))
      (fun o => o.isSome = true) ∗ emp)
  isplitl [Hgh]
  · iintro ⟨Hc, -⟩
    isplitr
    · ipureintro; simp only [List.length_append, List.length_singleton]; omega
    isplitr
    · ipureintro; exact Hid
    iframe Hgh
    isplitl [Hc]
    · iexists true
      iapply trCapB_mono (some γd) γ r id c true _ _ _ (fun _ _ _ h => h.2.2.2) $$ Hc
    ipureintro
    exact outOk_snoc Hok htrok
  iapply trCapB_hookGateOpt (some γd) γ r id c tl _ b (PinAt (wonLg id s m) C0 cs0 P0 o) _
    (fun o => o.isSome = true) (fun o => o.isSome = true) iprop(emp)
    (phaseStepB_msgApp_pin id c (wonLg id s m) o mm C0 cs0 P0 ma0 hma hrole1 hto hok' hcm' hmatch (by omega))
    (fun e he => sendEvOf_notBoot he (by decide) (by decide) (by decide))
    (fun _ _ => rfl)
    (fun _ e he => sendEvOf_ok (W64 9) id _ c _ e _ he (by decide) hTn hcn hln hnums (Nat.le_refl _))
    (fun h => by cases h)
  simp only [FxPresUT]
  iframe Htl Hf Hfx

end families

section bundle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **`raft.Step`'s traced bundle on a candidate's vote response of its term that wins the election**
(see the header): the receive line, the `BecomeLeader` line, the empty entry's `Replicate` line, the
self-acknowledgement and the broadcast's lines; the end state is raft's after `becomeLeader` and the
broadcast (`wonEnd`), raft's ghost state given back at the won state (`CloseMid`). -/
theorem stepBundle_traced_candVoteRespWon :
    stepBundle_traced.onC (GF := GF) (hG := hG) CandVoteRespWon := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole, hq⟩ := hp
  have hmty : mtypeOf m.Type' = some .voteResp := by rw [hTy]; rfl
  have htrd : MsgType.traced .voteResp = true := rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of .voteResp m ents hmty htrd hsh
  have hev16 : evt = W64 16 := by
    rcases hev with ⟨h, -⟩ | ⟨h, -, -⟩ | ⟨h, -⟩ | (⟨h, -⟩ | ⟨-, h⟩ | ⟨h, -, -⟩) <;> first | exact h | cases h
  subst hev16
  have hto' : m.To' = id := hto .voteResp hmty htrd
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hhook : CandHooked c m s := ⟨hTy, hterm, hrole, .inl hq⟩
  have hnl := jquorum_not_jlost c _ hq
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup⟩ := resp_ne (.inr (.inr hTy))
  have hmt2 : mtypeOf m.Type' = some .voteResp ∧ MsgType.traced .voteResp = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %MsgType.voteResp %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  ihave #Hm : isMessage γ (absMsg .voteResp m ents) $$ []
  · ihave #H := Hmsg $$ %MsgType.voteResp %hmt2
    rw [← isMessage_absMsg_ctx γ .voteResp m ents ctx ⟨by decide, by decide⟩]
    iapply isMessageC_isMessage
    iexact H
  rw [htr]
  ihave Hcap := trCapB_bootFit (some γd) γ r id c bfl _ Λ $$ Hcap
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  obtain ⟨⟨⟨a0, ha0, hR0, hs0, hP0, bt, bc, bl⟩, hfitC⟩, hidC⟩ := hI0
  ihave Hcap := trCapB_mono (some γd) γ r id c bfl _ (IdlePin s tn.voters cs0 P0) Λ
    (fun C cs P h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩) $$ Hcap
  obtain ⟨hmT, hmd, -, -, -, -, hvr⟩ := msgAbs_recvTy hev hma
  have hmty' : ma.type = .requestVoteResponse := hvr rfl
  have hmd' : ma.dest = idAbs id := by rw [hmd]; exact congrArg idAbs hto'
  have hb0 : s.logst.prev = base0 := hs0.1
  imodintro
  iexists vrWonR bfl γ md c r id s m γd tn cs0 (toC (confAbs tn.voters) (respSrv a0 ma)) P0 Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [vrWonR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, vrWonR]
    isplitr
    · -- the receive line, its result phase carrying the won tally's quorum
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg .voteResp m ents).NumsBelow traceNumBound := (hok .voteResp hmty hreT htrd).1
      have hps := phaseStepR_voteRespWon id c s m ents tn.voters cs0 P0 a0 ha0 ma hev hto' hterm hrole
        hnb hma hq
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf (W64 16) id s c (absMsg .voteResp m ents) e →
          TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok (W64 16) id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs .voteResp (W64 16) bfl k ma (fun _ => False)
        (recvPhantoms ma) _ _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · iapply fxPresR_voteRespCand γ id ma _ _ _ hmty' hmd'
        · rintro C cs P ⟨rfl, rfl, rfl, -⟩
          refine ⟨hidC, ?_⟩
          rw [hmT, ← ha0]
          show uint.Z m.Term' = a0.currentTerm
          rw [hR0.1]
          show uint.Z m.Term' = uint.Z (toPState s).term
          rw [hterm]; rfl
        · rintro C cs P cs' P' ⟨rfl, rfl, rfl, -⟩ ⟨⟨-, rfl, hP, -⟩, -⟩
          refine ⟨by simpa using hP.symm, fun a ha => ?_⟩
          exact toC_respSrv _ _ _ ma (ha0.trans ha.symm)
      · iexists tn; iframe Hdir Htok
    isplitr
    · -- the preamble: no step-down at the node's term
      unfold preGate
      iintro %_ HG0
      simp only [hnbf, ↓reduceIte]
      imodintro
      iexact HG0
    isplitr
    · iintro %h; exact (hns h).elim
    isplitr
    · iintro %h; exfalso; rcases h with h | h
      · exact hnV h
      · exact hnPV h
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %h; exfalso; rw [hrole] at h; cases h
      isplit
      · iintro %_
        iunfold candidateGates
        dsimp only [vrWonR]
        isplitr
        · iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnl]
        isplitr
        · iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnl]
        isplitr
        · iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnl]
        isplitr
        · -- `"Hgbl"`: the registration and the `BecomeLeader` line
          iintro %_ ⟨Hgh, Hc⟩
          rw [htr]
          iapply wonGate_bl γd γ md c r id s m ents tn.voters _ P0 hto' hterm hrole hq hb0 hidC hfitC hT hfit
          iframe Hm Hgh Hc
        isplitr
        · -- `"Hgrep"`: the win's last phase and the empty entry's `Replicate` line
          iintro %_ HTw HB1
          rw [htr]
          iapply wonGate_rep γd γ md c r id s m ents tn.voters _ P0 htr hTy hto' hterm hrole hq hidC hT hfit
          iframe HTw Hm HB1
        isplitr
        · -- `"Hgack"`: the self-acknowledgement
          iintro HB2
          rw [htr]
          iapply wonGate_ack γd γ md c r id s m tn.voters _ P0 hidC hT hfit
          iexact HB2
        isplitr
        · -- `"#Hgcast"`: the broadcast
          imodintro
          iintro %_ %pvs %to %mm %o %Hto %Happ HG
          rw [htr]
          iapply wonGate_app γd γ md c r id s m pvs to mm o hlrn hfit hT
            ((GMap.elem_of_subseteq _ _).1 hdom _ Hto.2) Hto.1
            ⟨Happ.1, Happ.2.1, Happ.2.2.1, Happ.2.2.2.2⟩
          iexact HG
        repeat (isplitr; · first | (rw [htr]; iexact Hnosnap) |
          iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnl])
        iguard_false [hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnl]
      · iintro %h; exfalso; rw [hrole] at h; cases h
    · ipureintro
      exact ⟨wonGE_permInv γ md c r id s m γd, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the won state's end (`wonEnd`), raft's ghost state at the won state
    iunfold stepClose
    iintro %s' %B %recv %_ %hend Hout
    unfold stepOutG
    dsimp only [vrWonR]
    icases Hout with (⟨%hn, -⟩ | ⟨%hn, -⟩ | H | %h | ⟨%b, %N, %h⟩)
    · exact (hn.1 hhook).elim
    · exact (hn.1 hhook).elim
    · unfold wonGE
      icases H with ⟨%hlen, %Hid, Hgh, ⟨%b, Hf⟩, %Hok⟩
      obtain ⟨ms, pvs, hse, hpm⟩ := wonEnd hTy hrole hterm hlen (hend (by rw [htr]; rfl))
      have hS : ∀ C, SimIdleS C (wonLg id s m) = SimIdleS C s' := fun C => by
        rw [hse]; exact simIdleS_wonEnd C id s m ms pvs Hid hpm
      imod trFam_idle (some γd) γ r id c b (wonLg id s m) s' _ hS $$ Hf with Hc
      imodintro
      isplitl [Hgh]
      · iright
        iexists wonStateW id s m (wonPvs id (logLast s.logst) s.prvals)
        iframe Hgh
        ipureintro
        exact .inr (.inl ⟨hTy, hrole, hterm, wonPvs id (logLast s.logst) s.prvals, wonPvs_reset _ _ _ Hid, rfl,
          by rw [hse]; rfl⟩)
      isplitl [Hc]
      · iexists b
        iapply trCapB_monoΛ (some γd) γ r id c b _ _ _ (fun o h => .inr h) $$ Hc
      · ipureintro; exact outTrStep_of_outOk Hok
    · exact h.elim
    · exact h.elim

end bundle

end EtcdGrove
end Perennial
