/-
Closing an instance slot after a handler changed it (shared by the reply handlers).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-- The scalar fields of a bookkeeping record and its image (`ownLb`'s pure part). -/
def lbFields [GooseExts] (y : epaxos.LeaderBookkeeping) (lb : LbRec) : Prop :=
  y.ballot' = lb.ballot ∧ y.allEqual' = lb.allEqual ∧ y.preAcceptOKs' = lb.preAcceptOKs ∧
    y.acceptOKs' = lb.acceptOKs ∧ y.nacks' = lb.nacks ∧ y.preparing' = lb.preparing ∧
    y.tryingToPreAccept' = lb.tryingToPreAccept ∧ y.lastTriedBallot' = lb.lastTriedBallot ∧
    y.status' = lb.status ∧ y.seq' = lb.seq ∧ y.leaderResponded' = lb.leaderResponded ∧
    y.preAcceptsSent' = lb.preAcceptsSent

/-- The scalar fields of an instance and its image (`ownInst`'s pure part). -/
def instFields [GooseExts] (y : epaxos.Instance) (w : InstRec) : Prop :=
  y.bal' = w.bal ∧ y.vbal' = w.vbal ∧ y.Status' = w.status ∧ y.Seq' = w.seq ∧
    (w.status ≠ stEXECUTED → y.Index' = W64 0)

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : StateTreemap GF]

theorem instAt_some (γ : EpNames) (i : Nat) (x : InstId) (pt : Loc) (w : InstRec)
    {o : Option InstRec} (h : o = some w) :
    instAt (GF := GF) γ i x pt o ⊣⊢ ownInst γ i x pt w := by
  subst h; exact .rfl

theorem updP_instAtP (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) (x : InstId)
    (o : Option InstRec) :
    updP (instAtP (GF := GF) γ i inst) x (fun pt => instAt γ i x pt o) = instAtP γ i (upd inst x o) := by
  funext y pt; unfold updP upd instAtP; split <;> simp_all

theorem updP_instAtP_irrel (γ : EpNames) (i : Nat) (inst : InstId → Option InstRec) (x : InstId)
    (o : Option InstRec) (Q : Loc → IProp GF) :
    updP (instAtP γ i inst) x Q = updP (instAtP γ i (upd inst x o)) x Q := by
  funext y pt; unfold updP upd instAtP; split <;> simp_all

/-- A slot known to hold `ptr` (`updateCommittedP` keeps the slot predicate). -/
def ptrSlot (γ : EpNames) (i : Nat) (x : InstId) (ptr : Loc) (w : InstRec) :
    Loc → IProp GF :=
  fun pt => iprop(⌜pt = ptr⌝ ∗ instAt γ i x pt (some w))

/-- `sync()`: nothing without a durable log (`Durable` is false). -/
theorem wp_sync_e (r rr : Loc) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ fld rr go!"Durable" ↦□ false }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"sync")) (Val #()))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hrr, #Hd⟩
  wp_auto
  wp_end

theorem updP_apply_self (P : InstId → Loc → IProp GF) (x : InstId)
    (Q : Loc → IProp GF) (pt : Loc) : updP P x Q x pt ⊢ Q pt := by
  simp [updP]

theorem updP_updP {α : Type} (P : InstId → α) (x : InstId) (Q Q' : α) :
    updP (updP P x Q) x Q' = updP P x Q' := by
  funext y; unfold updP; split <;> simp_all

theorem outsOk_bcast1 (γ : EpNames) (i : Nat) (e : Out) (b : Bcast) (h : NoSends [e]) :
    outsOk (GF := GF) γ i [e, .bcast b] ⊢ outboxesNil γ i ∗ pendFrag γ i b.norm ∗ curFrag γ i [] 0 :=
  outsOk_bcast γ i [e] b h

theorem outsOk_bcast2 (γ : EpNames) (i : Nat) (e1 e2 : Out) (b : Bcast) (h : NoSends [e1, e2]) :
    outsOk (GF := GF) γ i [e1, e2, .bcast b] ⊢ outboxesNil γ i ∗ pendFrag γ i b.norm ∗ curFrag γ i [] 0 :=
  outsOk_bcast γ i [e1, e2] b h

theorem noSends_ev (es : List Event) : NoSends (es.map Out.ev) := by
  intro o ho
  obtain ⟨e, -, rfl⟩ := List.mem_map.mp ho
  constructor
  · intro t m h; cases h
  · intro b h; cases h

/-- Close slot `x` holding `ptr ↦ y` with image `w` and bookkeeping `lb` at `y.lb' ↦ yl`. -/
theorem slot_close_gen (γ : EpNames) (i : Nat) (x : InstId) (ptr : Loc) (y : epaxos.Instance)
    (w : InstRec) (lb : LbRec) (yl : epaxos.LeaderBookkeeping) (gs prs : List Loc)
    (hyf : instFields y w) (hlb : w.lb = some lb) (hf : lbFields yl lb) :
    ptr ↦ y ∗ y.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗ cmdsRep (GF := GF) y.Cmds' w.cmds ∗
      (∃ dq : DFrac, y.Deps' ↦*{dq} w.deps) ∗ ⌜y.lb' ≠ null⌝ ∗ y.lb' ↦ yl ∗
      (match lb.clientProposals with
        | none => iprop(⌜yl.clientProposals' = slice.nil⌝)
        | some ps => iprop(⌜yl.clientProposals' ≠ slice.nil ∧ gs.length = ps.length⌝ ∗
            yl.clientProposals' ↦*□ gs ∗
            [∗list] k ↦ g ∈ gs, propHeld γ i (decide (w.status = stEXECUTED)) g
              (ps.getD k default))) ∗
      cmdsRep yl.cmds' lb.cmds ∗
      (if lbDepsOwned lb then iprop(yl.deps' ↦* lb.deps)
        else iprop(∃ dq : DFrac, yl.deps' ↦*{dq} lb.deps)) ∗
      (yl.prepareReplies' ↦* prs ∗ ownSliceCap Loc yl.prepareReplies' (DFrac.own 1)) ∗ ⌜prs.length = lb.prepareReplies.length⌝ ∗
      ([∗list] k ↦ l ∈ prs, ownPReply l (lb.prepareReplies.getD k default)) ⊢
    instAt γ i x ptr (some w) := by
  iintro ⟨Hy, #Hid, Hc, Hd, %Hnn, Hyl, Hcp, Hlc, Hld, Hpr, %Hprl, Hl⟩
  unfold instAt ownInst
  iexists y
  iframe Hy Hid Hc Hd
  isplitr
  · ipureintro; exact hyf
  rw [hlb]
  isplitr
  · ipureintro; exact Hnn
  unfold ownLb
  iexists yl, gs, prs
  iframe Hyl Hpr Hl Hcp Hlc Hld
  isplitr
  · ipureintro; exact hf
  ipureintro; exact Hprl

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
