/-
Lean-first (no Rocq counterpart). **`raft.Step`'s traced bundle on an append request or a heartbeat of a
leader's own term: the path refuted** (2026-11-11, trace-check Q8 stage 1 slice 27d, `notes/decisions.md`,
"Q8 stage 1 (slice 27d)"; a path the coverage check of the slice found unproved).

Raft's `stepLeader` ignores a `MsgApp` or `MsgHeartbeat` of its term (`LeaderNonpropResultC`), and the
specification has no such receive either: such a message is a leader's of the receiver's term
(`isMessage_app_inv`, `isMessage_hb_inv`: `isLeader γ m.From m.Term`), the receiver leads that term
(`ownRaftGhost_isLeader`), so the two are one node (`isLeader_unique`, election safety), which a message
between servers is not (`TrRecvShape`). The receive gate derives the contradiction from raft's ghost state;
every resource after it is `False` (`refR`).
-/
module

public import Proof.go_etcd_io.raft.v3.TracedRaftStepRecvHb

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 TraceSim

section paths
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **The resources of a refuted path**: the capability and the token before the receive line; `False`
after it (the receive gate refutes the path). -/
def refR (bt : Bool) (γ : RaftNames) (r : Loc) (id : w64) (s : NState) (c : CfgM) (γd : GName)
    (tn : TraceNames) (cs0 : ServerC) (P0 : List Etcdraft.Msg) (Λ : Option TraceEv → Prop) (k : Nat)
    (ma : Etcdraft.Msg) : StepG GF where
  G := iprop(trCapB (some γd) γ r id c bt (IdlePin s tn.voters cs0 P0) Λ ∗ inFlight tn k ma)
  G0 := fun _ => iprop(⌜False⌝)
  G1 := fun _ => iprop(⌜False⌝)
  GE := fun _ => iprop(⌜False⌝)
  Gf := iprop(⌜False⌝)
  Gb1 := iprop(⌜False⌝)
  Gb2 := iprop(⌜False⌝)
  Gp1 := iprop(⌜False⌝)
  Gp2 := fun _ => iprop(⌜False⌝)
  Gc := fun _ _ _ => iprop(⌜False⌝)

/-- **An append request or a heartbeat of a leader's own term.** -/
def LeadReq (s : NState) (m : MessageM) : Prop :=
  (m.Type' = MsgApp ∨ m.Type' = MsgHeartbeat) ∧ m.Term' = s.term ∧ s.role = .leader

/-- **`raft.Step`'s traced bundle on an append request or a heartbeat of a leader's own term**: no such
step (the sender would lead the receiver's term, `isLeader_unique`). -/
theorem stepBundle_traced_leadReq : stepBundle_traced.on (GF := GF) (hG := hG) LeadReq := by
  intro γ md c r id s m ents sn ctx rs γd Λ bfl hp htr hpv hcq hty hwf hloc hhup hto hT hmT hok hfit hlrn hdom
    hnpc hsh hboot
  obtain ⟨hTy, hterm, hrole⟩ := hp
  obtain ⟨ty, hmty, hty2⟩ : ∃ ty, mtypeOf m.Type' = some ty ∧ (ty = .app ∨ ty = .heartbeat) := by
    rcases hTy with h | h
    · exact ⟨.app, by rw [h]; rfl, .inl rfl⟩
    · exact ⟨.heartbeat, by rw [h]; rfl, .inr rfl⟩
  have htrd : ty.traced = true := by rcases hty2 with rfl | rfl <;> rfl
  have hto' : m.To' = id := hto ty hmty htrd
  have hne : id ≠ m.From' := fun h => hsh.2.2.1 (by
    rcases hTy with h' | h'
    · exact .inr (.inl h')
    · exact .inr (.inr h')) (by rw [hto', h])
  have hnbf : ¬ PreBF m s := fun h => absurd h.1 (by rw [hterm]; omega)
  have hpre : ∀ pvs, preState s m pvs = s := fun pvs => by simp [preState, hnbf]
  have hns : ¬ StaleMsg s m := fun h => absurd h.2 (by rw [hterm]; omega)
  have hsome : s.gh.tr ≠ none := by rw [htr]; simp
  have hnhup : m.Type' ≠ MsgHup := fun h => by rw [h] at hmty; cases hmty
  have hnv : m.Type' ≠ MsgVote := fun h => by
    rw [h] at hmty; cases hmty; rcases hty2 with h2 | h2 <;> cases h2
  have hnpv : m.Type' ≠ MsgPreVote := fun h => by
    rw [h] at hmty; cases hmty; rcases hty2 with h2 | h2 <;> cases h2
  have hmt2 : mtypeOf m.Type' = some ty ∧ ty.traced = true := ⟨hmty, htrd⟩
  iintro ⟨Hcap, ⟨Htok, #Hmsg⟩, #Hnosnap⟩
  iunfold recvTokOf at Htok
  icases Htok $$ %ty %hmt2 with ⟨%tn, %k, %ma, #Hdir, %hma, Htok⟩
  ihave #Hmc := Hmsg $$ %ty %hmt2
  ihave #Hm := isMessageC_isMessage γ _ $$ Hmc
  ihave #HL : iprop(isLeader (GF := GF) γ m.From' (toPState s).term) $$ [Hm]
  · rcases hty2 with rfl | rfl
    · rw [show m.From' = (absMsg .app m ents ctx).src from rfl,
        show (toPState s).term = (absMsg .app m ents ctx).term from hterm.symm]
      icases isMessage_app_inv γ (absMsg .app m ents ctx) rfl $$ Hm with ⟨-, #H, -⟩
      iexact H
    · rw [show m.From' = (absMsg .heartbeat m ents ctx).src from rfl,
        show (toPState s).term = (absMsg .heartbeat m ents ctx).term from hterm.symm]
      icases isMessage_hb_inv γ (absMsg .heartbeat m ents ctx) rfl $$ Hm with ⟨#H, -⟩
      iexact H
  rw [htr]
  icases trCapB_pinDir γd γ r id c bfl _ Λ $$ Hcap with ⟨%tn', %cs0, %P0, #Hdir', %hI0, Hcap⟩
  icases traceDir_agree γd tn tn' $$ [$Hdir $Hdir'] with %Htn
  subst Htn
  imodintro
  iexists refR bfl γ r id s c γd tn cs0 P0 Λ k ma
  isplitl [Hcap Htok]
  · dsimp only [refR]; iframe Hcap Htok
  isplitr
  · iunfold stepGates
    dsimp only [ghostIn, refR]
    isplitr
    · -- the receive line: refuted
      iintro ⟨Hgh, -, -⟩
      iapply hookGateOpt_fupd_recv
      iunfold ownStepGhost at Hgh
      icases Hgh with ⟨Hg, -⟩
      ihave #Hl := ownRaftGhost_isLeader γ id (toPState s) (by simp [toPState, hrole, proleRole]) $$ Hg
      icases isLeader_unique γ id m.From' (toPState s).term $$ Hl HL with %h
      exact (hne h).elim
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
      · exact hnv h
      · exact hnpv h
    isplitr
    · iintro %h; exact (hnhup h).elim
    isplitr
    · unfold stepFnGates
      iintro %pvs
      rw [hpre pvs]
      isplit
      · iintro %_
        iapply followerGates_false
      isplit
      · iintro %_
        iapply candidateGates_false
        rw [htr]; iexact Hnosnap
      · iintro %_
        iapply leaderGates_false
        rw [htr]; iexact Hnosnap
    · ipureintro
      exact ⟨fun _ _ _ => rfl, IdxFree.of_some _ hsome, IdxFree.of_some _ hsome,
        IdxFree.of_some _ hsome, fun _ _ => IdxFree.of_some _ hsome⟩
  · -- the closing wand: no resource reaches it
    iapply stepClose_anyB
    iapply stepClose_of_at _ _ _ _ _ _ _ _ _ _ (fun _ => CloseAt.of_traced hmty htrd)
    iunfold stepCloseAt
    iintro %s' %B %recv %_ %hend Hout
    unfold stepOut
    dsimp only [refR]
    icases Hout with (%h | %h | %h | %h | ⟨%b, %N, %h⟩)
    all_goals exact h.elim

end paths

end EtcdGrove
end Perennial
