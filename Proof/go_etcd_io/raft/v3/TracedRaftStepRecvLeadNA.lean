/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on a leader's rejected `MsgAppResp` and
its `MsgHeartbeatResp`, of its term** (2026-11-11, trace-check Q8 stage 1 slice 27c,
`notes/decisions.md`, "Q8 stage 1 (slice 27c)").

The receive line (slice 22b's `phaseStepR_leadResp`, `fxPresR_leadResp`: the specification records
nothing a share reads), then `stepLeader`'s sends at `s`: the probe's or the catch-up's append to the
responder (`"Hgsapp"`: `MaybeDecrTo` then `sendAppend`, or the flow control's `sendAppend`), each a
`SendAppendEntriesRequest` line (`lineF_app`), and, for a heartbeat response with a read-index context,
the confirmed requests' responses (`"#Hghresp"`, untraced: `lineF_untraced`). The end state is `s` with
the appends queued, other `Progress` values of the same `Match` values, and (read index) another
read-only state and untraced responses (`leadRespNA_end`), whose idle server is `s`'s.

The family is `lineF` at `s` (raft's ghost state at `s`, the idle server of `s`), with the sender among
the voters (the receive law's premise, amendment A6's `MsgEnds`, carried out of the receive line's phase:
the append's destination must be a voter, which `"Hgsapp"` does not say). The close is at `s`
(`CloseAt.of_traced`).

The read-index path is in scope (no premise excludes it): a heartbeat response's context is the node's own
heartbeat's, and the traced harness never calls `ReadIndex`, but nothing in the bundle's premises says so,
and the path costs only the untraced sends and the read-only state's change.
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvLeadSend

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section pure
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions]

/-- The idle server's part after answering confirmed reads (`readRespondAll`: the read-only state and
untraced responses or read states). -/
theorem simIdleS_readRespondAll (C : List w64) (id : w64) (s : NState) (qs : List ReadReq) :
    SimIdleS C (readRespondAll id s qs) = SimIdleS C s := by
  obtain ⟨o, r, he⟩ := readRespondAll_eq id s qs
  rw [he]; rfl

/-- **A leader's response of its term that moves no `Match`**: a rejected `MsgAppResp` or a
`MsgHeartbeatResp`. -/
def LeadRespNA (s : NState) (m : MessageM) : Prop :=
  m.Term' = s.term ∧ s.role = .leader ∧
    ((m.Type' = MsgAppResp ∧ m.Reject' = true) ∨ m.Type' = MsgHeartbeatResp)

/-- **The end state of a `LeadRespNA` path's step function**: its idle server is `s`'s (the appends
queued, the `Progress` values at the same `Match` values, the read-only state and the untraced responses
of a confirmed read). -/
theorem leadRespNA_end {c : CfgM} {id : w64} {m : MessageM} {ents : List EntryM} {ctx : List w8}
    {s s' : NState} (hp : LeadRespNA s m) (h : StepFnEnd c id s m ents ctx s') :
    ∀ C, SimIdleS C s = SimIdleS C s' := by
  obtain ⟨-, hr, hty⟩ := hp
  obtain ⟨d, hres⟩ := h.2.2 hr
  have hX : ∀ (ms : List Msg) (pvs : GMap w64 Progress), prvalsMatch pvs = prvalsMatch s.prvals →
      ∀ C, SimIdleS C s = SimIdleS C { sendMsgs s ms with prvals := pvs } :=
    fun ms pvs hm C => (simIdleS_prvals C s ms pvs hm).symm
  unfold LeaderStepResultC LeaderNonpropResultC at hres
  rcases hty with ⟨ht, hrej⟩ | ht
  · rw [ht] at hres
    simp [MsgAppResp, MsgVoteResp, MsgProp, MsgBeat, MsgHeartbeatResp, MsgReadIndex, MsgForgetLeader,
      MsgTimeoutNow, MsgUnreachable, MsgSnapStatus, MsgTransferLeader, MsgCheckQuorum, MsgApp, MsgHeartbeat,
      MsgPreVoteResp, MsgReadIndexResp, hrej] at hres
    rcases hres.2 with ⟨-, rfl⟩ | ⟨-, ms, pvs, rfl, -, hm⟩
    · exact fun _ => rfl
    · exact hX ms pvs hm
  · rw [ht] at hres
    simp [MsgAppResp, MsgVoteResp, MsgProp, MsgBeat, MsgHeartbeatResp, MsgReadIndex, MsgForgetLeader,
      MsgTimeoutNow, MsgUnreachable, MsgSnapStatus, MsgTransferLeader, MsgCheckQuorum, MsgApp, MsgHeartbeat,
      MsgPreVoteResp, MsgReadIndexResp] at hres
    obtain ⟨-, ms, -, pvs, hm, hres⟩ := hres
    rcases hres with ⟨-, rfl⟩ | ⟨-, N, -, rfl⟩
    · exact hX ms pvs hm
    · intro C
      rw [simIdleS_readRespondAll]
      exact hX ms pvs hm C

end pure

section bundle
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `LeadRespNA`'s resources: before the receive line the capability at the pinned idle phase and the
message in flight; after it, the local family at `s` (`G0`, `G1`, where `Step` ends) with the sender `f`
a voter; `False` at every other resource. -/
def leadNAR (bt : Bool) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState) (γd : GName)
    (tn : TraceNames) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (Λ : Option TraceEv → Prop) (k : Nat)
    (ma : Etcdraft.Msg) (f : w64) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun o => iprop(⌜f ∈ elements c.incoming⌝ ∗ lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) o)
  G1 := fun o => iprop(⌜f ∈ elements c.incoming⌝ ∗ lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) o)
  GE := fun _ => iprop(⌜False⌝)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **The receive line's result as the local family**: the pinned idle phase is the idle server's at the
outbox of `s`, and the sender is a voter (`trCapB_pinPerm`). -/
theorem lineF_of_leadPin (γd : GName) (γ : RaftNames) (md : GMode) (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (Λ : Option TraceEv → Prop) (C0 : List w64) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (f : w64)
    (htr : s.gh.tr = some γd) :
    (ownStepGhost γ md c id s ∗
        trCapB (some γd) γ r id c true (fun C cs P => IdlePin s C0 cs0 P0 C cs P ∧ f ∈ C)
          (fun o => o.isSome = true) : IProp GF) ⊢
      ⌜f ∈ elements c.incoming⌝ ∗ lineF γ md c r id s (fun C => SimIdleS C s) (stepLastEv Λ) s.outbox := by
  iintro ⟨Hgh, Hc⟩
  icases trCapB_pinPerm γd γ r id c true _ _ C0 (fun _ _ _ h => h.1.1) $$ Hc with ⟨%hperm, Hc⟩
  icases trCapB_pinMem γd γ r id c true _ _ $$ Hc with ⟨%C1, %cs1, %P1, %HΦ1, Hc⟩
  obtain ⟨⟨⟨hC1, -⟩, hf⟩, -⟩ := HΦ1
  isplitr
  · ipureintro; rw [hC1] at hf; exact hperm.mem_iff.2 hf
  unfold lineF trFam
  rw [htr]
  iframe Hgh
  isplitl [Hc]
  · iexists true
    iapply trCapB_monoΛ (some γd) γ r id c true _ _ _ (fun o h => .inr h)
    iapply trCapB_mono (some γd) γ r id c true _ _ _
      (fun C cs P h => simIdle_phaseAt C s cs P h.2.2.2.1.2.2.2) $$ Hc
  ipureintro; exact outOk_self s

/-- **`raft.Step`'s traced bundle on a leader's rejected `MsgAppResp` or `MsgHeartbeatResp` of its
term** (see the header). -/
theorem stepBundle_traced_leadRespNA : stepBundle_traced.on (GF := GF) (hG := hG) LeadRespNA := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  have hp' := hp
  obtain ⟨hterm, hrole, hrr⟩ := hp'
  obtain ⟨ty, hmty, hresp⟩ : ∃ ty, mtypeOf m.Type' = some ty ∧
      ((ty = .appResp ∧ m.Reject' = true) ∨ ty = .heartbeatResp) := by
    rcases hrr with ⟨h, hr⟩ | h
    · exact ⟨.appResp, by rw [h]; rfl, .inl ⟨rfl, hr⟩⟩
    · exact ⟨.heartbeatResp, by rw [h]; rfl, .inr rfl⟩
  have htrd : ty.traced = true := by rcases hresp with ⟨rfl, -⟩ | rfl <;> rfl
  obtain ⟨evt, hevt, hev⟩ := recvEvTy_of ty m ents hmty htrd hsh
  have hto' : m.To' = id := hto ty hmty htrd
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hTy : m.Type' = MsgAppResp ∨ m.Type' = MsgHeartbeatResp ∨ m.Type' = MsgVoteResp := by
    rcases hrr with ⟨h, -⟩ | h
    · exact .inl h
    · exact .inr (.inl h)
  obtain ⟨hnA, hnH, hnP, hnRI, hnTL, hnTN, hnB, hnCQ, hnPVR, hnV, hnPV, hnHup⟩ := resp_ne hTy
  have hnAcc : ¬ (m.Type' = MsgAppResp ∧ m.Reject' = false) := by
    rintro ⟨h1, h2⟩
    rcases hrr with ⟨-, h⟩ | h
    · rw [h] at h2; cases h2
    · rw [h] at h1; exact absurd h1 (by simp [MsgAppResp, MsgHeartbeatResp])
  have hnVR : m.Type' ≠ MsgVoteResp := by
    rcases hrr with ⟨h, -⟩ | h <;> rw [h] <;> simp [MsgAppResp, MsgHeartbeatResp, MsgVoteResp]
  have hmt2 : mtypeOf m.Type' = some ty ∧ ty.traced = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %ty %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  rw [msgAbs_absMsg_ctx] at hma
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  imodintro
  iexists leadNAR bfl γ md c r id s γd tn cs0 P0 Λ k ma m.From'
  isplitl [Hcap Htok]
  · dsimp only [leadNAR]; iframe Hcap Htok
  have hrt : (ty = .appResp ∧ m.Reject' = true) ∨ ty = .heartbeatResp := hresp
  have hmaty : ma.type = .appendEntriesResponse := by
    have hty' : ((absMsg ty m ents).ty = .appResp ∧ (absMsg ty m ents).reject = true) ∨
        (absMsg ty m ents).ty = .heartbeatResp := by
      rcases hresp with ⟨rfl, hr⟩ | rfl
      · exact .inl ⟨rfl, hr⟩
      · exact .inr rfl
    exact (msgAbs_leadResp hty' hma).1
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, leadNAR]
    isplitr
    · -- the receive line
      iintro ⟨Hgh, Hc, Htok⟩
      iapply hookGateOpt_fupd_recv
      icases ownStepGhost_nsLink γ md c id s $$ Hgh with ⟨%Hnl, Hgh⟩
      imod ownStepGhost_traceOk γ md c id s hfit $$ Hgh with ⟨%Hb, Hgh⟩
      imodintro
      have hreT : γ.reTrace.isSome := by rw [← Hnl.2.1, htr]; rfl
      have hnb : (absMsg ty m ents).NumsBelow traceNumBound := (hok ty hmty hreT htrd).1
      have hps := phaseStepR_leadResp id c s ty m ents evt tn.voters cs0 P0 ma hev hto' hrt hterm hrole hnb hma
      have hnb' := recvEvTy_notBoot hev
      have hOk : ∀ e, SendEvOf evt id s c (absMsg ty m ents) e → TraceEv.Ok (elements c.incoming).length e :=
        fun e he => sendEvOf_ok evt id s c _ e _ he ⟨hnb'.1, hnb'.2.2.2⟩ (by word) Hb.2 Hb.1 hnb (Nat.le_refl _)
      iapply hookGateOpt_mono s.gh.tr r _
        iprop(ownStepGhost γ md c id s ∗ trCapB (some γd) γ r id c true
          (fun C cs P => IdlePin s tn.voters cs0 P0 C cs P ∧ m.From' ∈ C) (fun o => o.isSome = true))
      isplitr
      · iintro H
        iapply lineF_of_leadPin γd γ md c r id s Λ tn.voters cs0 P0 m.From' htr $$ H
      iapply recvGate_traced γd γ r id c s m ents sn ctx rs ty evt bfl k ma (fun _ => False) (recvPhantoms ma)
        (IdlePin s tn.voters cs0 P0) _ Λ (ownStepGhost γ md c id s) htr hmty hevt hps hOk
      iframe Hgh Hc
      isplitr
      · iapply fxPresR_leadResp γ id ma _ s tn.voters cs0 P0 hmaty m.From'
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
    · iintro %h; exact (h.elim hnV hnPV).elim
    isplitr
    · iintro %h; exact (hnHup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %h; rw [hrole] at h; cases h
      isplit
      · iintro %h; rw [hrole] at h; rcases h with h | h <;> cases h
      · iintro %_
        iunfold leaderGates
        isplitr
        · iguard_false [hnB]
        isplitr
        · iguard_false [hnRI]
        isplitr
        · iguard_false [hnRI]
        isplitr
        · iguard_false [hnTL]
        isplitr
        · iguard_false [hnTL]
        isplitr
        · rw [← htr]; iexact Hnosnap
        isplitr
        · iguard_false [hnCQ]
        isplitr
        · iguard_false [hnP]
        isplitr
        · iguard_false [hnP]
        isplitr
        · iguard_false [hnP]
        isplitr
        · -- the probe's or the catch-up's append to the responder
          iintro %_ %mm %o %Happ ⟨%hf, HG⟩
          obtain ⟨hok', hcm, hdst, hmatch, hrh⟩ := Happ
          iapply hookGateOpt_frame
          isplitr
          · ipureintro; exact hf
          iapply lineF_app γd γ md c r id s Λ mm o htr hrole hT hfit (by rw [hdst]; exact hf) hok' hcm
            (by rw [hdst]; exact hmatch) hrh $$ HG
        isplitr
        · -- a confirmed read's response (untraced)
          imodintro
          iintro %_ %mm %o %hmm ⟨%hf, HG⟩
          iapply hookGateOpt_frame
          isplitr
          · ipureintro; exact hf
          iapply lineF_untraced γd γ md c r id s _ _ mm o htr (by rw [hmm]; rfl) $$ HG
        isplitr
        · iintro %h; exact (hnAcc h).elim
        isplitr
        · imodintro; iintro %h; exact (hnAcc h).elim
        isplitr
        · imodintro; iintro %h; exact (hnAcc h).elim
        isplitr
        · imodintro; iintro %h; exact (hnAcc h).elim
        · imodintro; iintro %h; exact (hnAcc h).elim
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: the idle server of the end state is `s`'s
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty htrd)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    have hS : ∀ C, SimIdleS C s = SimIdleS C s' := by
      obtain ⟨pvs, h⟩ := ((hend (by rw [htr]; rfl)) hty).2.2.2 hns hnHup hnV
      rw [hpre pvs] at h
      exact leadRespNA_end hp h
    unfold stepOut
    dsimp only [leadNAR]
    icases Hout with (H | H | %h | %h | ⟨%b, %N, %h⟩)
    rotate_right 3
    · exact h.elim
    · exact h.elim
    · exact h.elim
    all_goals
      icases H with ⟨-, H⟩
      rw [← htr]
      iapply lineF_close γ md c r id s s' (stepLastEv Λ) hS $$ H

end bundle

end EtcdGrove
end Perennial
