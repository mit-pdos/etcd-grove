/-
`(*Replica).handlePrepareReply` against the model's `hPrepareReply` (fix R-PROM included): the
early returns, the reply recorded (`append`), the decision (`prepDecide`: the four loops over
`lb.prepareReplies`), then sub-case 1 (commit, `updateCommitted`), 2/3 (accept, `bcastAccept`),
5/6 (`startPhase1`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.StartPhase1
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.UpdateCommitted
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.PRDecide

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- The scalar fields of a bookkeeping record and its image (`ownLb`'s pure part). -/
def LbF (y : epaxos.LeaderBookkeeping) (lb : LbRec) : Prop :=
  y.ballot' = lb.ballot ∧ y.allEqual' = lb.allEqual ∧ y.preAcceptOKs' = lb.preAcceptOKs ∧
    y.acceptOKs' = lb.acceptOKs ∧ y.nacks' = lb.nacks ∧ y.preparing' = lb.preparing ∧
    y.tryingToPreAccept' = lb.tryingToPreAccept ∧ y.lastTriedBallot' = lb.lastTriedBallot ∧
    y.status' = lb.status ∧ y.seq' = lb.seq ∧ y.leaderResponded' = lb.leaderResponded ∧
    y.preAcceptsSent' = lb.preAcceptsSent

/-- Close an instance whose bookkeeping changed in scalar fields only (`preparing`, `nacks`). -/
theorem slot_close_scalar (γ : EpNames) (i : Nat) (x : InstId) (ptr : Loc) (y : epaxos.Instance)
    (w : InstRec) (lb lb' : LbRec) (yl yl' : epaxos.LeaderBookkeeping) (gs prs : List Loc)
    (hyf : y.bal' = w.bal ∧ y.vbal' = w.vbal ∧ y.Status' = w.status ∧ y.Seq' = w.seq ∧
      (w.status ≠ stEXECUTED → y.Index' = W64 0))
    (hf : LbF yl' lb') (hyl : yl'.clientProposals' = yl.clientProposals' ∧ yl'.cmds' = yl.cmds' ∧
      yl'.deps' = yl.deps' ∧ yl'.prepareReplies' = yl.prepareReplies')
    (hsame : lb'.clientProposals = lb.clientProposals ∧ lb'.cmds = lb.cmds ∧ lb'.deps = lb.deps ∧
      lb'.prepareReplies = lb.prepareReplies ∧ lbDepsOwned lb' = lbDepsOwned lb) :
    ptr ↦ y ∗ y.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗ cmdsRep (GF := GF) y.Cmds' w.cmds ∗
      (∃ dq : DFrac, y.Deps' ↦*{dq} w.deps) ∗ ⌜y.lb' ≠ null⌝ ∗ y.lb' ↦ yl' ∗
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
    instAt γ i x ptr (some { w with lb := some lb' }) := by
  obtain ⟨h1, h2, h3, h4⟩ := hyl
  obtain ⟨s1, s2, s3, s4, s5⟩ := hsame
  iintro ⟨Hy, #Hid, Hc, Hd, %Hnn, Hyl, Hcp, Hlc, Hld, Hpr, %Hprl, Hl⟩
  unfold instAt ownInst
  iexists y
  iframe Hy Hid Hc Hd
  isplitr
  · ipureintro; exact hyf
  simp only
  isplitr
  · ipureintro; exact Hnn
  unfold ownLb
  iexists yl', gs, prs
  iframe Hyl
  isplitr
  · ipureintro; exact hf
  rw [s1, s2, s3, s4, s5, h1, h2, h3, h4]
  iframe
  ipureintro; exact Hprl

/-- Close an instance whose bookkeeping changed in scalar fields and its replies. -/
theorem slot_close_prs (γ : EpNames) (i : Nat) (x : InstId) (ptr : Loc) (y : epaxos.Instance)
    (w : InstRec) (lb lb' : LbRec) (yl yl' : epaxos.LeaderBookkeeping) (gs prs' : List Loc)
    (hyf : y.bal' = w.bal ∧ y.vbal' = w.vbal ∧ y.Status' = w.status ∧ y.Seq' = w.seq ∧
      (w.status ≠ stEXECUTED → y.Index' = W64 0))
    (hf : LbF yl' lb') (hyl : yl'.clientProposals' = yl.clientProposals' ∧ yl'.cmds' = yl.cmds' ∧
      yl'.deps' = yl.deps')
    (hsame : lb'.clientProposals = lb.clientProposals ∧ lb'.cmds = lb.cmds ∧ lb'.deps = lb.deps ∧
      lbDepsOwned lb' = lbDepsOwned lb) :
    ptr ↦ y ∗ y.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗ cmdsRep (GF := GF) y.Cmds' w.cmds ∗
      (∃ dq : DFrac, y.Deps' ↦*{dq} w.deps) ∗ ⌜y.lb' ≠ null⌝ ∗ y.lb' ↦ yl' ∗
      (match lb.clientProposals with
        | none => iprop(⌜yl.clientProposals' = slice.nil⌝)
        | some ps => iprop(⌜yl.clientProposals' ≠ slice.nil ∧ gs.length = ps.length⌝ ∗
            yl.clientProposals' ↦*□ gs ∗
            [∗list] k ↦ g ∈ gs, propHeld γ i (decide (w.status = stEXECUTED)) g
              (ps.getD k default))) ∗
      cmdsRep yl.cmds' lb.cmds ∗
      (if lbDepsOwned lb then iprop(yl.deps' ↦* lb.deps)
        else iprop(∃ dq : DFrac, yl.deps' ↦*{dq} lb.deps)) ∗
      (yl'.prepareReplies' ↦* prs' ∗ ownSliceCap Loc yl'.prepareReplies' (DFrac.own 1)) ∗ ⌜prs'.length = lb'.prepareReplies.length⌝ ∗
      ([∗list] k ↦ l ∈ prs', ownPReply l (lb'.prepareReplies.getD k default)) ⊢
    instAt γ i x ptr (some { w with lb := some lb' }) := by
  obtain ⟨h1, h2, h3⟩ := hyl
  obtain ⟨s1, s2, s3, s5⟩ := hsame
  iintro ⟨Hy, #Hid, Hc, Hd, %Hnn, Hyl, Hcp, Hlc, Hld, Hpr, %Hprl, Hl⟩
  unfold instAt ownInst
  iexists y
  iframe Hy Hid Hc Hd
  isplitr
  · ipureintro; exact hyf
  simp only
  isplitr
  · ipureintro; exact Hnn
  unfold ownLb
  iexists yl', gs, prs'
  iframe Hyl Hpr Hl
  isplitr
  · ipureintro; exact hf
  rw [s1, s2, s3, s5, h1, h2, h3]
  iframe
  ipureintro; exact Hprl

/-- The replies' images after `append`. -/
theorem prs_snoc (prs : List Loc) (reps : List PReply) (l : Loc) (e : PReply)
    (h : prs.length = reps.length) :
    ([∗list] k ↦ x ∈ prs, ownPReply (GF := GF) x (reps.getD k default)) ∗ ownPReply l e ⊢
      [∗list] k ↦ x ∈ prs ++ [l], ownPReply x ((reps ++ [e]).getD k default) := by
  iintro ⟨Hl, He⟩
  iapply (BigSepL.bigSepL_append).2
  isplitl [Hl]
  · iapply BigSepL.bigSepL_mono ?_ $$ Hl
    intro k x hk
    have hk' : k < reps.length := by rw [← h]; exact (List.getElem?_eq_some_iff.mp hk).1
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk']
  · iapply (BigSepL.bigSepL_singleton).2
    simp [List.getD_eq_getElem?_getD, h]
    iexact He

theorem repInstsP_upd (γ : EpNames) (i : Nat) (r : Loc) (inst : InstId → Option InstRec)
    (x : InstId) (o : Option InstRec) :
    repInstsP (GF := GF) r (updP (instAtP γ i inst) x (fun pt => instAt γ i x pt o)) ⊢
      repInsts γ i r (upd inst x o) := by
  refine (repInstsP_congr _ _ _ ?_).trans (repInsts_P γ i r _).2
  funext y pt
  unfold updP instAtP upd
  by_cases h : y = x
  · subst h; simp
  · simp [h]

theorem inst_open (γ : EpNames) (i : Nat) (x : InstId) (pt : Loc) (w : InstRec) (lb : LbRec)
    (hlb : w.lb = some lb) :
    instAt (GF := GF) γ i x pt (some w) ⊢ ∃ y : epaxos.Instance, pt ↦ y ∗
      ⌜y.bal' = w.bal ∧ y.vbal' = w.vbal ∧ y.Status' = w.status ∧ y.Seq' = w.seq ∧
        (w.status ≠ stEXECUTED → y.Index' = W64 0)⌝ ∗
      y.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗ cmdsRep y.Cmds' w.cmds ∗
      (∃ dq : DFrac, y.Deps' ↦*{dq} w.deps) ∗ ⌜y.lb' ≠ null⌝ ∗
      ∃ (yl : epaxos.LeaderBookkeeping) (gs prs : List Loc), y.lb' ↦ yl ∗ ⌜LbF yl lb⌝ ∗
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
      ([∗list] k ↦ l ∈ prs, ownPReply l (lb.prepareReplies.getD k default)) := by
  rcases w with ⟨a, b, c, d, e, f, g, h⟩
  cases hlb
  unfold instAt ownInst ownLb LbF
  exact .rfl

theorem ownPReply_open (l : Loc) (pr : PReply) :
    ownPReply (GF := GF) l pr ⊢ ∃ (cs ds : GoSlice) (dq : DFrac),
      l ↦□ epaxos.PrepareReply.mk pr.m.acceptorId pr.m.replica pr.m.inst pr.m.ballot
        pr.m.vballot pr.m.status cs pr.m.seq ds ∗
      prCmds cs pr.cmdsNil pr.m.command ∗ ds ↦*{dq} pr.m.deps := by
  unfold ownPReply; exact .rfl

instance cmdsRep_persistent (cs : GoSlice) (o : Option (List WCmd)) :
    Persistent (cmdsRep (GF := GF) cs o) := by
  cases o <;> unfold cmdsRep <;> infer_instance

/-- A recorded reply, read-only (its deps discarded). -/
def ownPReplyP (l : Loc) (pr : PReply) : IProp GF :=
  iprop(∃ cs ds : GoSlice,
    l ↦□ epaxos.PrepareReply.mk pr.m.acceptorId pr.m.replica pr.m.inst pr.m.ballot
      pr.m.vballot pr.m.status cs pr.m.seq ds ∗
    prCmds cs pr.cmdsNil pr.m.command ∗ ds ↦*□ pr.m.deps)

instance ownPReplyP_persistent (l : Loc) (pr : PReply) : Persistent (ownPReplyP (GF := GF) l pr) := by
  unfold ownPReplyP; infer_instance

theorem ownPReplyP_open (l : Loc) (pr : PReply) :
    ownPReplyP (GF := GF) l pr ⊢ ∃ cs ds : GoSlice,
      l ↦□ epaxos.PrepareReply.mk pr.m.acceptorId pr.m.replica pr.m.inst pr.m.ballot
        pr.m.vballot pr.m.status cs pr.m.seq ds ∗
      prCmds cs pr.cmdsNil pr.m.command ∗ ds ↦*□ pr.m.deps := by
  unfold ownPReplyP; exact .rfl

theorem ownPReplyP_to (l : Loc) (pr : PReply) : ownPReplyP (GF := GF) l pr ⊢ ownPReply l pr := by
  unfold ownPReplyP ownPReply
  iintro ⟨%cs, %ds, #H1, #H2, #H3⟩
  iexists cs, ds, DFrac.discard
  isplitl []
  · iexact H1
  isplitl []
  · iexact H2
  iexact H3

theorem ownPReply_persist (l : Loc) (pr : PReply) : ownPReply (GF := GF) l pr ⊢ |==> ownPReplyP l pr := by
  unfold ownPReplyP ownPReply
  iintro ⟨%cs, %ds, %dq, #H1, #H2, H3⟩
  imod ownSlice_persist _ _ _ $$ H3 with #H3
  imodintro
  iexists cs, ds
  isplitl []
  · iexact H1
  isplitl []
  · iexact H2
  iexact H3

theorem bigSepL_bupd_monoI {A : Type} {Φ Ψ : Nat → A → IProp GF} (l : List A)
    (h : ∀ k x, Φ k x ⊢ |==> Ψ k x) :
    ([∗list] k ↦ x ∈ l, Φ k x) ⊢ |==> [∗list] k ↦ x ∈ l, Ψ k x := by
  induction l generalizing Φ Ψ with
  | nil => iintro _; imodintro; iempintro
  | cons a l ih =>
    iintro ⟨Ha, Hl⟩
    imod h 0 a $$ Ha with Ha
    imod ih (Φ := fun k x => Φ (k + 1) x) (Ψ := fun k x => Ψ (k + 1) x) (fun k x => h (k + 1) x)
      $$ Hl with Hl
    imodintro
    iframe

/-- The bookkeeping struct during the decision. -/
def prYl (yl : epaxos.LeaderBookkeeping) (prs' : GoSlice) (b : Bool) : epaxos.LeaderBookkeeping :=
  { yl with prepareReplies' := prs', preparing' := false, leaderResponded' := b }

/-- `subCase` and `chosen` from an index stage. -/
def scOf (d : Nat × Option Nat) : w64 := W64 d.1
def chOf (prs : List Loc) (o : Option Nat) : Loc :=
  match o with
  | some j => prs.getD j null
  | none => null

theorem pr_wp_isInitialBallot (b q n : w32) :
    {{ pkgInit_epaxos (GF := GF) }}
      (App (App (App (Val #(functions epaxos.isInitialBallot [])) (Val #b)) (Val #q)) (Val #n))
    {{ RET #(isInitialBallot b q); True }} := by
  wp_start
  wp_auto
  rw [show isInitialBallot b q = decide (b = q) by unfold model.isInitialBallot; rfl]
  iapply HΦ
  itrivial

/-- Close a slot with a new record (bookkeeping with read-only deps, not executed). -/
theorem inst_close_new (γ : EpNames) (i : Nat) (x : InstId) (ptr : Loc) (y' : epaxos.Instance)
    (w' : InstRec) (lb' : LbRec) (yl' : epaxos.LeaderBookkeeping) (gs prs' : List Loc)
    (cps : GoSlice)
    (hyf : y'.bal' = w'.bal ∧ y'.vbal' = w'.vbal ∧ y'.Status' = w'.status ∧ y'.Seq' = w'.seq ∧
      (w'.status ≠ stEXECUTED → y'.Index' = W64 0))
    (hlb : w'.lb = some lb') (hf : LbF yl' lb') (hdo : lbDepsOwned lb' = false)
    (hex : w'.status ≠ stEXECUTED) (hcp : yl'.clientProposals' = cps) :
    ptr ↦ y' ∗ y'.id' ↦□ epaxos.instanceId.mk (W32 x.q) (W32 x.i) ∗ cmdsRep (GF := GF) y'.Cmds' w'.cmds ∗
      y'.Deps' ↦*□ w'.deps ∗ ⌜y'.lb' ≠ null⌝ ∗ y'.lb' ↦ yl' ∗
      (match lb'.clientProposals with
        | none => iprop(⌜cps = slice.nil⌝)
        | some ps => iprop(⌜cps ≠ slice.nil ∧ gs.length = ps.length⌝ ∗ cps ↦*□ gs ∗
            [∗list] k ↦ g ∈ gs, propHeld γ i false g (ps.getD k default))) ∗
      cmdsRep yl'.cmds' lb'.cmds ∗ yl'.deps' ↦*□ lb'.deps ∗
      (yl'.prepareReplies' ↦* prs' ∗ ownSliceCap Loc yl'.prepareReplies' (DFrac.own 1)) ∗ ⌜prs'.length = lb'.prepareReplies.length⌝ ∗
      ([∗list] k ↦ l ∈ prs', ownPReply l (lb'.prepareReplies.getD k default)) ⊢
    instAt γ i x ptr (some w') := by
  iintro ⟨Hy, #Hid, Hc, #Hd, %Hnn, Hyl, Hcp, Hlc, #Hld, Hpr, %Hprl, Hl⟩
  unfold instAt ownInst
  iexists y'
  iframe Hy Hid Hc
  isplitr
  · ipureintro; exact hyf
  isplitl []
  · iexists DFrac.discard; iexact Hd
  rw [hlb]
  isplitr
  · ipureintro; exact Hnn
  unfold ownLb
  iexists yl', gs, prs'
  iframe Hyl Hpr Hl Hlc
  isplitr
  · ipureintro; exact hf
  rw [show decide (w'.status = stEXECUTED) = false from decide_eq_false hex, hcp, hdo]
  isplitl [Hcp]
  · iexact Hcp
  isplitl []
  · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hld
  ipureintro; exact Hprl

theorem ownRepRest_open (i : Nat) (r : Loc) (σ : RState) :
    ownRepRest (GF := GF) i r σ ⊢ repRowArr r go!"crtInstance" σ.crtInstance ∗
      repRowArr r go!"CommittedUpTo" σ.committedUpTo ∗
      (∀ cut, repRowArr r go!"crtInstance" σ.crtInstance -∗
        repRowArr r go!"CommittedUpTo" cut -∗
        ownRepRest i r { σ with committedUpTo := cut }) := by
  unfold ownRepRest
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10⟩
  iframe H1 H2
  iintro %cut H1 H2
  iframe

theorem pr_noSends_ev (e : Event) : NoSends [Out.ev e] := by
  intro o ho; simp only [List.mem_singleton] at ho; subst ho
  exact ⟨fun _ _ h => Out.noConfusion h, fun _ h => Out.noConfusion h⟩

/-- The handler's message: a `*PrepareReply` (owned), its command slice not `nil` (decoded:
Go's `make` never returns `nil`; HUB-REQUEST handlers-3 asks the Unmarshal spec to say so). -/
def ownPrepareReplyNN (l : Loc) (m : PrepareReply) : IProp GF :=
  iprop(∃ cs ds : GoSlice, l ↦ epaxos.PrepareReply.mk m.acceptorId m.replica m.inst m.ballot
      m.vballot m.status cs m.seq ds ∗ ownCmds cs m.command (DFrac.own 1) ∗
      ownDeps ds m.deps (DFrac.own 1))

/-- What `handlePrepareReply` needs of the state and the message (from the invariant: the reply
reaches a bookkeeping, `Inv.replyTargets`; message ids in range, `Inv.msgWf`; `cmdsNil` only for
NONE, `InvAux.prepNoProp`; a non-NONE report has `N` deps, `Inv.reports`). -/
structure PRWf (i : Nat) (σ : RState) (ord : List w32) (m : PrepareReply) (w : InstRec)
    (lb : LbRec) : Prop where
  hrep : RepWf i σ ord
  hq : 0 ≤ zz m.replica ∧ zz m.replica < nR
  hn : 0 ≤ zz m.inst ∧ toN m.inst + 1 < MAX_INSTANCE
  hw : σ.inst ⟨toN m.replica, toN m.inst⟩ = some w
  hlb : w.lb = some lb
  hnil : lb.preparing = true → ∀ e ∈ lb.prepareReplies, e.cmdsNil = true → e.m.status = stNONE
  hdeps : lb.preparing = true → ∀ e ∈ lb.prepareReplies ++ [⟨m, false⟩], e.m.status ≠ stNONE →
    e.m.deps.length = nR
  hcmd : lb.preparing = true → ∀ e ∈ lb.prepareReplies ++ [⟨m, false⟩], e.m.status ≠ stNONE →
    e.m.command ≠ []
  hconf : ConfWf σ
  hord : ∀ o ∈ ord, 0 ≤ sint.Z o
  houts : OutsWf (hPrepareReply σ m).2

set_option hygiene false in
/-- Evaluate a call of `handlePrepareReply`'s `isPreAccepted` closure on a reply `x` (the
closure's body entered by `wp_auto`). -/
macro "pa_eval" x:term : tactic => `(tactic| (
  wp_bind (exceptionDo _)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #()⌝ ∗ «$res0_ptr» ↦
    isPreAcceptedAt (prMax lb m) $x))) $$ [«$res0» e]
  · by_cases hv : ($x).m.vballot = prMax lb m
    · rw [decide_eq_true hv]
      wp_auto
      by_cases hs1 : ($x).m.status = W8 1
      · rw [decide_eq_true hs1]
        wp_auto
        rw [show isPreAcceptedAt (prMax lb m) $x = true by
          unfold isPreAcceptedAt; rw [hv, hs1]; simp [stPREACCEPTED]]
        isplitr
        · ipureintro; rfl
        iframe
      · rw [decide_eq_false hs1]
        wp_auto
        by_cases hs2 : ($x).m.status = W8 2
        · rw [decide_eq_true hs2]
          rw [show isPreAcceptedAt (prMax lb m) $x = true by
            unfold isPreAcceptedAt; rw [hv, hs2]; simp [stPREACCEPTED, stPREACCEPTED_EQ]]
          isplitr
          · ipureintro; rfl
          iframe
        · rw [decide_eq_false hs2]
          rw [show isPreAcceptedAt (prMax lb m) $x = false by
            unfold isPreAcceptedAt stPREACCEPTED stPREACCEPTED_EQ
            simp; exact fun _ => ⟨hs1, hs2⟩]
          isplitr
          · ipureintro; rfl
          iframe
    · rw [decide_eq_false hv]
      wp_auto
      rw [show isPreAcceptedAt (prMax lb m) $x = false by
        unfold isPreAcceptedAt
        have : (($x).m.vballot == prMax lb m) = false := by simpa using hv
        rw [this]]
      isplitr
      · ipureintro; rfl
      iframe))

set_option maxHeartbeats 8000000 in
set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 100000 in
set_option pp.maxSteps 1000000 in
/-- **`handlePrepareReply(preply)`**: from the instance lock's contents (`ownRep σ`), the message,
and the ghost step's outputs (the fragment at the model's result, its pending broadcast), the
handler ends in the lock's invariant shape (`repDone`). -/
theorem wp_handlePrepareReply (hS : replica.Replica.SendMsg.spec (GF := GF))
    (hSQ : replica.Replica.SlowQuorumSize.spec (GF := GF)) (hNoop : state.NOOP.spec (GF := GF))
    (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (σ : RState) (l : Loc) (m : PrepareReply) (w : InstRec) (lb : LbRec)
    (hw : PRWf i σ ord m w lb) :
    {{ hdCtx (GF := GF) γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ ownPrepareReplyNN l m ∗
        repFrag γ i (hPrepareReply σ m).1 ∗ outsOk γ i (hPrepareReply σ m).2 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handlePrepareReply"))
        (Val #l))
    {{ RET #(); repDone γ i r }} := by
  wp_start as ⟨#Hctx, Hrep, Hm, Hf, Houts⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  icases ownRep_open γ i r σ $$ Hrep with ⟨%Hib, %Hcb, Hinsts, Hrest⟩
  icases ownRepRest_bump i r σ m.ballot $$ Hrest with ⟨Hmrb, Hrest⟩
  unfold ownPrepareReplyNN
  icases Hm with ⟨%cs, %ds, Hm, Hcs, Hds⟩
  have hq' : toN m.replica < nR := by
    have := hw.hq.1; have := hw.hq.2; simp only [toN, zz] at *; omega
  have hn' : toN m.inst < MAX_INSTANCE := by have := hw.hn.2; omega
  icases (repInsts_P γ i r σ.inst).1 $$ Hinsts with Hinsts
  icases repInstsP_acc r _ ⟨toN m.replica, toN m.inst⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  rw [hw.hw]
  icases inst_open γ i _ ptr w lb hw.hlb $$ Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, %Hlbnn,
    %yl, %gs, %prs, Hyl, %Hylf, Hcp, Hlcmds, Hldeps, ⟨Hlprs, Hlcap⟩, %Hlprsl, Hlpr⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  have e1 : sint.Z (W64 (sint.Z m.replica)) = sint.Z m.replica := by word
  have e2 : sint.Z (W64 (sint.Z m.inst)) = sint.Z m.inst := by word
  have hqe : (sint.Z m.replica).toNat = toN m.replica := rfl
  have hne : (sint.Z m.inst).toNat = toN m.inst := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧
      sint.Z (W64 (sint.Z m.replica)) < sint.Z iss.len := by
    have := hw.hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  have h2 : 0 ≤ sint.Z (W64 (sint.Z m.inst)) ∧ sint.Z (W64 (sint.Z m.inst)) < sint.Z row.len := by
    have := hw.hn.1; have := hw.hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  wp_auto
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hqe]; exact Hrow
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hne]; exact Hptr.1
  -- maxRecvBallot
  ipersist r
  ipersist preply
  wp_join iprop(efld r go!"maxRecvBallot" ↦ (bumpRecvBallot σ m.ballot).maxRecvBallot ∗
      l ↦ epaxos.PrepareReply.mk m.acceptorId m.replica m.inst m.ballot m.vballot m.status cs m.seq ds)
    with [Hmrb Hm] as ⟨Hmrb, Hm⟩
  · rw [bumpRecvBallot_true _ _ (by simpa using Hif)]; iframe Hm; iexact Hmrb
  · rw [bumpRecvBallot_false _ _ (by simpa using Hif)]; iframe Hm; iexact Hmrb
  -- the nil tests
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
  ihave %Hlnn := typedPointsto_not_null _ _ _ $$ Hyl
  ihave Hrest := Hrest $$ Hmrb
  rw [show decide (ptr = null) = false from decide_eq_false Hnn]
  wp_auto
  rw [show decide (y.lb' = null) = false from decide_eq_false Hlbnn]
  wp_auto
  have hset : ptrs.set (toN m.inst) ptr = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hptr.1
    rw [← this.2]; exact List.set_getElem_self this.1
  have hib1 : instBounds (bumpRecvBallot σ m.ballot).inst := by simpa using Hib
  rw [Hylf.2.2.2.2.2.1]
  rcases hp : lb.preparing
  · -- not preparing: return
    wp_auto
    rw [hPR_notPrep σ m w lb hw.hw hw.hlb hp]
    iapply HΦ
    iapply repDone_of γ i r (bumpRecvBallot σ m.ballot) [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    iframe Hrest
    isplitr
    · ipureintro; exact hib1
    isplitr
    · ipureintro; simpa using Hcb
    ihave Hx := slot_close_scalar (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb lb yl yl gs prs Hyf
      Hylf ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps
        Hlprs Hlcap Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some { w with lb := some lb })) [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
    · iexact Hins
    rw [← hw.hlb, show ({ w with lb := w.lb } : InstRec) = w from rfl, upd_self _ _ _ hw.hw]
    simp only [bumpRecvBallot_inst]
    iexact Hins
  -- preparing
  wp_auto
  wp_if_destruct
  · -- committed here: preparing = false, return
    have hc : stGe w.status stCOMMITTED = true := (stGe_iff _ _).mpr (by rw [← Hyf.2.2.1]; exact Hif)
    rw [hPR_committed σ m w lb hw.hw hw.hlb hp hc]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    rw [ownRepRest_setInst]
    iframe Hrest
    isplitr
    · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
    isplitr
    · ipureintro; simpa [RState.setInst] using Hcb
    ihave Hx := slot_close_scalar (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb { lb with preparing := false } yl { yl with preparing' := false }
      gs prs Hyf (by obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf; exact ⟨a1, a2, a3, a4, a5, rfl, a7, a8, a9, a10, a11, a12⟩) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ $$ [Hy Hycmds Hydeps Hyl Hcp
        Hlcmds Hldeps Hlprs Hlcap Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some { w with lb := some { lb with preparing := false } })) [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
    · iexact Hins
    simp only [RState.setInst, bumpRecvBallot_inst]
    iexact Hins
  have hc : stGe w.status stCOMMITTED = false := by
    rcases h : stGe w.status stCOMMITTED
    · rfl
    · exact absurd ((stGe_iff _ _).mp h) (by rw [← Hyf.2.2.1]; exact Hif)
  wp_if_destruct
  · -- promised a higher ballot (fix R-PROM): preparing = false, return
    have hb : lb.lastTriedBallot.slt w.bal = true := by
      rw [slt_iff, ← Hylf.2.2.2.2.2.2.2.1, ← Hyf.1]; exact Hif
    rw [hPR_promised σ m w lb hw.hw hw.hlb hp hc hb]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    rw [ownRepRest_setInst]
    iframe Hrest
    isplitr
    · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
    isplitr
    · ipureintro; simpa [RState.setInst] using Hcb
    ihave Hx := slot_close_scalar (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb { lb with preparing := false } yl { yl with preparing' := false }
      gs prs Hyf (by obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf; exact ⟨a1, a2, a3, a4, a5, rfl, a7, a8, a9, a10, a11, a12⟩) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ $$ [Hy Hycmds Hydeps Hyl Hcp
        Hlcmds Hldeps Hlprs Hlcap Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some { w with lb := some { lb with preparing := false } })) [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
    · iexact Hins
    simp only [RState.setInst, bumpRecvBallot_inst]
    iexact Hins
  have hb : lb.lastTriedBallot.slt w.bal = false := by
    rcases h : lb.lastTriedBallot.slt w.bal
    · rfl
    · exact absurd ((slt_iff _ _).mp h) (by rw [← Hylf.2.2.2.2.2.2.2.1, ← Hyf.1]; exact Hif)
  rw [Hylf.2.2.2.2.2.2.2.1]
  by_cases he : m.ballot = lb.lastTriedBallot
  case neg =>
    -- another ballot: a nack
    simp only [he, _root_.decide_false, Bool.not_false]
    wp_auto
    rw [hPR_nack σ m w lb hw.hw hw.hlb hp hc hb he]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    rw [ownRepRest_setInst]
    iframe Hrest
    isplitr
    · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
    isplitr
    · ipureintro; simpa [RState.setInst] using Hcb
    ihave Hx := slot_close_scalar (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb { lb with nacks := lb.nacks + 1 } yl { yl with nacks' := yl.nacks' + W64 1 }
      gs prs Hyf (by obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf; exact ⟨a1, a2, a3, a4, by rw [a5]; rfl, a6, a7, a8, a9, a10, a11, a12⟩) ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ $$ [Hy Hycmds Hydeps Hyl Hcp
        Hlcmds Hldeps Hlprs Hlcap Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; exact ⟨Hlbnn, Hlprsl⟩
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some { w with lb := some { lb with nacks := lb.nacks + 1 } })) [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
    · iexact Hins
    simp only [RState.setInst, bumpRecvBallot_inst]
    iexact Hins
  simp only [he, _root_.decide_true, Bool.not_true]
  wp_auto
  -- a reply from this acceptor already recorded: return
  ihave %Hprslen := ownSlice_len _ _ _ $$ Hlprs
  ihave HI : (∃ k : Nat, "Hi" ∷ i_ptr ↦ W64 k ∗ "He" ∷ (∃ v : Loc, e_ptr ↦ v) ∗
      "Hlprs" ∷ yl.prepareReplies' ↦* prs ∗
      "Hlpr" ∷ ([∗list] k ↦ l ∈ prs, ownPReply l (lb.prepareReplies.getD k default)) ∗
      "%Hk" ∷ ⌜k ≤ prs.length ∧ ∀ j < k, (lb.prepareReplies.getD j default).m.acceptorId ≠
        m.acceptorId⌝ : IProp GF) $$ [i e Hlprs Hlpr]
  · iexists 0; iframe i Hlprs Hlpr
    isplitl [e]
    · iexists _; iexact e
    ipureintro; exact ⟨Nat.zero_le _, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  wp_for HI
  wp_if_destruct
  · -- an iteration
    have hlenZ : (prs.length : Int) = sint.Z yl.prepareReplies'.len := by
      rw [Hprslen.1]; exact Int.toNat_of_nonneg Hprslen.2
    have hkz : (k : Int) ≤ sint.Z yl.prepareReplies'.len := by
      have h1 := Hk.1; omega
    have hkw : sint.Z (W64 (k : Int)) = k := by
      have : sint.Z yl.prepareReplies'.len < 2 ^ 63 := by word
      word
    have hkl : k < prs.length := by
      have h' : sint.Z (W64 (k : Int)) < sint.Z yl.prepareReplies'.len := Hif
      rw [hkw] at h'; omega
    obtain ⟨lk, hlk⟩ : ∃ lk, prs[k]? = some lk := ⟨prs[k], List.getElem?_eq_getElem hkl⟩
    have hbk : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z yl.prepareReplies'.len :=
      ⟨by word, Hif⟩
    simp only [hbk, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ _ prs _ lk hbk.1 $$ [$Hlprs] as Hlprs
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact hlk
    icases He with ⟨%v, He⟩
    icases bigSepL_get_acc hlk $$ Hlpr with ⟨Hk1, Hlpr⟩
    icases ownPReply_open _ _ $$ Hk1 with ⟨%kcs, %kds, %kdq, #Hkl, Hkc, Hkd⟩
    ihave #Hkl2 := Hkl
    iStructNamed Hkl
    wp_auto
    ihave Hlpr := Hlpr $$ [Hkc Hkd]
    · unfold ownPReply; iexists kcs, kds, kdq; iframe Hkl2 Hkc Hkd
    wp_if_destruct
    · -- a duplicate: return
      have hk' : k < lb.prepareReplies.length := by rw [← Hlprsl]; exact hkl
      have hd : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = true := by
        rw [List.any_eq_true]
        refine ⟨lb.prepareReplies[k], List.getElem_mem hk', ?_⟩
        have : (lb.prepareReplies.getD k default) = lb.prepareReplies[k] := by
          simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
        rw [← this]; simpa using Hif
      wp_for_post
      rw [hPR_dup σ m w lb hw.hw hw.hlb hp hc hb he hd]
      iapply HΦ
      iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
      iframe Hf Houts
      iapply ownRep_of
      rw [he]
      iframe Hrest
      isplitr
      · ipureintro; simpa using Hib
      isplitr
      · ipureintro; simpa using Hcb
      ihave Hx := slot_close_scalar (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb lb yl yl gs prs Hyf
        Hylf ⟨rfl, rfl, rfl, rfl⟩ ⟨rfl, rfl, rfl, rfl, rfl⟩ $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps
          Hlprs Hlcap Hlpr]
      · iframe
        isplitl []
        · iexact Hyid
        ipureintro; exact ⟨Hlbnn, Hlprsl⟩
      ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some { w with lb := some lb })) [Hptrs] Hx
      · rw [hset]; iexact Hptrs
      ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
      · iexact Hins
      rw [← hw.hlb, show ({ w with lb := w.lb } : InstRec) = w from rfl, upd_self _ _ _ hw.hw]
      simp only [bumpRecvBallot_inst]
      iexact Hins
    · -- the next reply
      wp_for_post
      iframe
      iexists k + 1
      have hk1 : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by word
      rw [hk1]
      iframe Hi Hlprs Hlpr
      isplitl [He]
      · iexists _; iexact He
      ipureintro
      refine ⟨hkl, fun j hj => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact Hk.2 j hj
      · subst hj; exact Hif
  -- no duplicate: record the reply
  have hkp : k = prs.length := by
    have h' := Hif
    have hlenZ : (prs.length : Int) = sint.Z yl.prepareReplies'.len := by
      rw [Hprslen.1]; exact Int.toNat_of_nonneg Hprslen.2
    have hkw : sint.Z (W64 (k : Int)) = k := by
      have : sint.Z yl.prepareReplies'.len < 2 ^ 63 := by word
      have := Hk.1; word
    rw [hkw] at h'; have := Hk.1; omega
  have hd : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId) = false := by
    rcases h : lb.prepareReplies.any (fun e => e.m.acceptorId == m.acceptorId)
    · rfl
    · exfalso
      obtain ⟨e, he1, he2⟩ := List.any_eq_true.mp h
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem he1
      have := Hk.2 j (by rw [hkp, Hlprsl]; exact hj)
      apply this
      simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using he2
  wp_apply wp_slice_literal (V := Loc) [l]
  isplitr
  · ipureintro; rfl
  iintro %slp Hsl
  icases Hsl with ⟨Hsl, -⟩
  wp_apply (wp_slice_append (V := Loc) _ prs _ [l] (DFrac.own 1)) $$ [$Hlprs $Hlcap $Hsl] as %prs' ⟨Hlprs, Hlcap, -⟩
  -- the message, read-only from now on (it is in `lb.prepareReplies`)
  ipersist Hm
  imod ownCmds_persist _ _ _ $$ Hcs with #Hcs
  unfold ownDeps
  ipersist Hds
  ihave Hnew : ownPReply l ⟨m, false⟩ $$ []
  · unfold ownPReply
    iexists cs, ds, DFrac.discard
    isplitl []
    · simp only; rw [he]; iexact Hm
    iframe Hds
    unfold prCmds; simp only [Bool.false_eq_true, if_false]
    iframe Hcs
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  wp_apply (hSQ γ rr i L p) $$ [$Hpr $Hfro]
  ihave %Hprs'len := ownSlice_len _ _ _ $$ Hlprs
  have hreps : (prReps lb m).length = prs.length + 1 := by
    unfold prReps; simp [Hlprsl]
  wp_if_destruct
  · -- fewer than a majority: return
    have hl : (prReps lb m).length < (nR + 1) / 2 := by
      have h' : sint.Z prs'.len < sint.Z (W64 3) := Hif
      have : (prs.length + 1 : Int) = sint.Z prs'.len := by
        have h1 := Hprs'len.1; simp only [List.length_append, List.length_singleton] at h1
        have h2 : ((prs.length + 1 : Nat) : Int) = sint.Z prs'.len := by
          rw [h1]; exact Int.toNat_of_nonneg Hprs'len.2
        push_cast at h2; exact h2
      rw [hreps]; unfold nR; have : sint.Z (W64 3) = 3 := rfl; omega
    rw [hPR_few σ m w lb hw.hw hw.hlb hp hc hb he hd hl]
    iapply HΦ
    iapply repDone_of γ i r _ [] (by intro o ho; simp at ho)
    iframe Hf Houts
    iapply ownRep_of
    rw [ownRepRest_setInst, he]
    iframe Hrest
    isplitr
    · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
    isplitr
    · ipureintro; simpa [RState.setInst] using Hcb
    ihave Hlpr := prs_snoc prs lb.prepareReplies l ⟨m, false⟩ Hlprsl $$ [Hlpr Hnew]
    · iframe
    ihave Hx := slot_close_prs (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr y w lb
      { lb with prepareReplies := prReps lb m } yl { yl with prepareReplies' := prs' } gs (prs ++ [l]) Hyf Hylf ⟨rfl, rfl, rfl⟩
      ⟨rfl, rfl, rfl, rfl⟩ $$ [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hldeps Hlprs Hlcap Hlpr]
    · iframe
      isplitl []
      · iexact Hyid
      ipureintro; refine ⟨Hlbnn, ?_⟩; rw [hreps]; simp
    ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt (some { w with lb := some { lb with prepareReplies := prReps lb m } }))
      [Hptrs] Hx
    · rw [hset]; iexact Hptrs
    ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
    · iexact Hins
    simp only [RState.setInst, bumpRecvBallot_inst]
    iexact Hins
  -- a majority: decide. The replies, read-only from now on.
  have hl : ¬ (prReps lb m).length < (nR + 1) / 2 := by
    intro hl'
    apply Hif
    have h1 := Hprs'len.1; simp only [List.length_append, List.length_singleton] at h1
    have h2 : ((prs.length + 1 : Nat) : Int) = sint.Z prs'.len := by
      rw [h1]; exact Int.toNat_of_nonneg Hprs'len.2
    push_cast at h2
    rw [hreps] at hl'; unfold nR at hl'; rw [← h2]; have : sint.Z (W64 3) = 3 := rfl; omega
  ihave Hlpr := prs_snoc prs lb.prepareReplies l ⟨m, false⟩ Hlprsl $$ [Hlpr Hnew]
  · iframe
  rw [show lb.prepareReplies ++ [⟨m, false⟩] = prReps lb m from rfl]
  imod bigSepL_bupd_monoI
    (Φ := fun k x => ownPReply x ((prReps lb m).getD k default))
    (Ψ := fun k x => ownPReplyP x ((prReps lb m).getD k default))
    (prs ++ [l]) (fun k x => ownPReply_persist x ((prReps lb m).getD k default)) $$ Hlpr with #Hreps
  have hlen2 : (prs ++ [l]).length = (prReps lb m).length := by rw [hreps]; simp
  rw [show ({ yl with prepareReplies' := prs', preparing' := false } : epaxos.LeaderBookkeeping) =
    prYl yl prs' (lb.leaderResponded || ((prReps lb m).take 0).any lrP) by
      unfold prYl; rw [← Hylf.2.2.2.2.2.2.2.2.2.2.1]; simp]
  -- loop 1: leaderResponded, the first committed reply, maxVbal
  ipersist lb
  ipersist inst
  ihave HI : (∃ k : Nat, "Hi" ∷ i_ptr ↦ W64 k ∗ "Hel" ∷ (∃ v : Loc, element_ptr ↦ v) ∗
      "Hlprs" ∷ prs' ↦* (prs ++ [l]) ∗
      "Hyl" ∷ y.lb' ↦ prYl yl prs' (lb.leaderResponded || ((prReps lb m).take k).any lrP) ∗
      "Hsc" ∷ subCase_ptr ↦ scOf (stg 1 (((prReps lb m).take k).findIdx? comP)) ∗
      "Hch" ∷ chosen_ptr ↦ chOf (prs ++ [l]) (((prReps lb m).take k).findIdx? comP) ∗
      "Hmx" ∷ maxVbal_ptr ↦ ((prReps lb m).take k).foldl mxF (W32 (-1)) ∗
      "%Hk" ∷ ⌜k ≤ (prReps lb m).length⌝ : IProp GF)
      $$ [i element Hlprs Hyl subCase chosen maxVbal]
  · iexists 0
    iframe i Hlprs Hyl
    isplitl [element]
    · iexists _; iexact element
    simp only [List.take_zero, List.findIdx?_nil, List.foldl_nil]
    iframe
    ipureintro; omega
  wp_for HI
  ihave %Hprs2len := ownSlice_len _ _ _ $$ Hlprs
  have hlenZ2 : ((prs ++ [l]).length : Int) = sint.Z prs'.len := by
    rw [Hprs2len.1]; exact Int.toNat_of_nonneg Hprs2len.2
  wp_if_destruct
  · -- an iteration
    have hkw : sint.Z (W64 (k : Int)) = k := by
      have : sint.Z prs'.len < 2 ^ 63 := by word
      have := Hk; rw [← hlen2] at this; word
    have hkl : k < (prReps lb m).length := by
      have h' : sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
      rw [hkw, ← hlenZ2, hlen2] at h'; omega
    have hkl2 : k < (prs ++ [l]).length := by rw [hlen2]; exact hkl
    obtain ⟨lk, hlk⟩ : ∃ lk, (prs ++ [l])[k]? = some lk := ⟨_, List.getElem?_eq_getElem hkl2⟩
    have hbk : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z prs'.len :=
      ⟨by rw [hkw]; omega, Hif⟩
    simp only [hbk, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index _ _ (prs ++ [l]) _ lk hbk.1 $$ [$Hlprs] as Hlprs
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by rw [hkw]; simp]; exact hlk
    ihave #Hk1 := BigSepL.bigSepL_lookup hlk $$ Hreps
    icases ownPReplyP_open _ _ $$ Hk1 with ⟨%kcs, %kds, #Hkl, #Hkc, #Hkd⟩
    ihave #Hkl2 := Hkl
    iStructNamed Hkl
    icases Hel with ⟨%v, Hel⟩
    wp_auto
    wp_join iprop(y.lb' ↦ prYl yl prs' (lb.leaderResponded || ((prReps lb m).take (k + 1)).any lrP))
      with [Hyl] as Hyl
    · rw [take_any_succ _ _ _ hkl, show lrP ((prReps lb m).getD k default) = true by
        simp [lrP]; simpa using Hif]
      simp only [Bool.or_true]
      unfold prYl
      iexact Hyl
    · rw [take_any_succ _ _ _ hkl, show lrP ((prReps lb m).getD k default) = false by
        simp [lrP]; simpa using Hif]
      simp only [Bool.or_false]
      iexact Hyl
    have hcom : ((prReps lb m).take (k + 1)).findIdx? comP =
        (((prReps lb m).take k).findIdx? comP).or
          (if comP ((prReps lb m).getD k default) then some k else none) :=
      findIdx?_take_succ _ _ _ hkl
    have hcomE : comP ((prReps lb m).getD k default) =
        decide (sint.Z (W8 4) ≤ sint.Z ((prReps lb m).getD k default).m.status) := by
      unfold comP; rw [Bool.eq_iff_iff, stGe_iff, decide_eq_true_iff]; exact Iff.rfl
    have hmx : ((prReps lb m).take (k + 1)).foldl mxF (W32 (-1)) =
        mxF (((prReps lb m).take k).foldl mxF (W32 (-1))) ((prReps lb m).getD k default) :=
      take_foldl_succ _ _ _ _ hkl
    by_cases hc1 : sint.Z (W8 4) ≤ sint.Z ((prReps lb m).getD k default).m.status
    · -- committed: the first one sets subCase = 1
      simp only [decide_eq_true hc1]
      wp_auto
      wp_join iprop(subCase_ptr ↦ scOf (stg 1 (((prReps lb m).take (k + 1)).findIdx? comP)) ∗
          chosen_ptr ↦ chOf (prs ++ [l]) (((prReps lb m).take (k + 1)).findIdx? comP) ∗
          element_ptr ↦ lk)
        with [Hsc Hch Hel] as ⟨Hsc, Hch, Hel⟩
      · -- subCase = 1 already: unchanged
        rcases ho : ((prReps lb m).take k).findIdx? comP with _ | j0
        · rw [ho] at Hif; exact absurd Hif (by simp [scOf, stg])
        rw [hcom, ho]; simp only [Option.some_or]
        iframe Hsc Hch Hel
      · -- the first committed reply
        have ho : ((prReps lb m).take k).findIdx? comP = none := by
          rcases h : ((prReps lb m).take k).findIdx? comP with _ | j0
          · rfl
          · rw [h] at Hif; exact absurd rfl Hif
        rw [hcom, ho, hcomE, decide_eq_true hc1]
        simp only [ite_true, Option.none_or, scOf, stg, chOf]
        have : (prs ++ [l]).getD k null = lk := by
          simp [List.getD_eq_getElem?_getD, hlk]
        rw [this]
        iframe Hsc Hch Hel
      -- maxVbal
      wp_join iprop(maxVbal_ptr ↦ ((prReps lb m).take (k + 1)).foldl mxF (W32 (-1)) ∗
          element_ptr ↦ lk) with [Hmx Hel] as ⟨Hmx, Hel⟩
      · rw [hmx, show mxF (((prReps lb m).take k).foldl mxF (W32 (-1)))
            ((prReps lb m).getD k default) = ((prReps lb m).getD k default).m.vballot from
          if_pos ((slt_iff _ _).mpr (by simpa using Hif))]
        iframe Hmx Hel
      · rw [hmx, show mxF (((prReps lb m).take k).foldl mxF (W32 (-1)))
            ((prReps lb m).getD k default) = ((prReps lb m).take k).foldl mxF (W32 (-1)) from
          if_neg (fun h => Hif (by simpa using (slt_iff _ _).mp h))]
        iframe Hmx Hel
      wp_for_post
      iframe
      iexists k + 1
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe Hi Hlprs Hyl Hsc Hch Hmx
      isplitl [Hel]
      · iexists _; iexact Hel
      ipureintro; omega
    · simp only [decide_eq_false hc1]
      wp_auto
      have hcom' : ((prReps lb m).take (k + 1)).findIdx? comP = ((prReps lb m).take k).findIdx? comP := by
        rw [hcom, hcomE, decide_eq_false hc1]; simp
      -- maxVbal
      wp_join iprop(maxVbal_ptr ↦ ((prReps lb m).take (k + 1)).foldl mxF (W32 (-1)) ∗
          element_ptr ↦ lk) with [Hmx Hel] as ⟨Hmx, Hel⟩
      · rw [hmx, show mxF (((prReps lb m).take k).foldl mxF (W32 (-1)))
            ((prReps lb m).getD k default) = ((prReps lb m).getD k default).m.vballot from
          if_pos ((slt_iff _ _).mpr (by simpa using Hif))]
        iframe Hmx Hel
      · rw [hmx, show mxF (((prReps lb m).take k).foldl mxF (W32 (-1)))
            ((prReps lb m).getD k default) = ((prReps lb m).take k).foldl mxF (W32 (-1)) from
          if_neg (fun h => Hif (by simpa using (slt_iff _ _).mp h))]
        iframe Hmx Hel
      wp_for_post
      iframe
      iexists k + 1
      rw [hcom']
      rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
      iframe Hi Hlprs Hyl Hsc Hch Hmx
      isplitl [Hel]
      · iexists _; iexact Hel
      ipureintro; omega
  -- loop 1 over: k is the number of replies
  have hkE : k = (prReps lb m).length := by
    have hkw : sint.Z (W64 (k : Int)) = k := by
      have : sint.Z prs'.len < 2 ^ 63 := by word
      have := Hk; rw [← hlen2] at this; word
    have h' : ¬ sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
    rw [hkw, ← hlenZ2, hlen2] at h'; omega
  subst hkE
  rw [List.take_length]
  rw [show stg 1 ((prReps lb m).findIdx? comP) = dec1 (prReps lb m) from rfl,
    show chOf (prs ++ [l]) ((prReps lb m).findIdx? comP) =
      chOf (prs ++ [l]) (dec1 (prReps lb m)).2 by
        unfold dec1 stg; rcases (prReps lb m).findIdx? comP <;> rfl,
    show (prReps lb m).foldl mxF (W32 (-1)) = prMax lb m from rfl,
    show (lb.leaderResponded || (prReps lb m).any lrP) = prLr lb m from rfl]
  -- stage 2: an accepted reply at maxVbal
  wp_join iprop(subCase_ptr ↦ scOf (dec2 (prReps lb m) (prMax lb m)) ∗
      chosen_ptr ↦ chOf (prs ++ [l]) (dec2 (prReps lb m) (prMax lb m)).2 ∗
      prs' ↦* (prs ++ [l]) ∗ maxVbal_ptr ↦ prMax lb m ∗ y.lb' ↦ prYl yl prs' (prLr lb m))
    with [Hsc Hch Hlprs Hmx Hyl] as ⟨Hsc, Hch, Hlprs, Hmx, Hyl⟩
  · -- no committed reply: the loop
    have h1 : (dec1 (prReps lb m)).1 = 0 := by
      have := Hif; unfold scOf at this; rcases h : dec1 (prReps lb m) with ⟨c, o⟩
      rw [h] at this; simp only at this ⊢
      have hc : c < 2 := by
        unfold dec1 stg at h; split at h <;> (simp only [Prod.mk.injEq] at h; omega)
      word
    have h1' : dec1 (prReps lb m) = (0, none) := by
      unfold dec1 stg at h1 ⊢; split <;> simp_all
    rw [h1']
    rw [show dec2 (prReps lb m) (prMax lb m) = stg 2 ((prReps lb m).findIdx? (accP (prMax lb m))) by
      unfold dec2; rw [if_pos h1]]
    unfold prYl
    ihave HI : (∃ k : Nat, "Hi" ∷ i_ptr ↦ W64 k ∗ "Hel" ∷ (∃ v : Loc, element_ptr ↦ v) ∗
        "Hlprs" ∷ prs' ↦* (prs ++ [l]) ∗ "Hsc" ∷ subCase_ptr ↦ W64 0 ∗
        "Hch" ∷ chosen_ptr ↦ null ∗ "Hmx" ∷ maxVbal_ptr ↦ prMax lb m ∗
        "%Hk" ∷ ⌜k ≤ (prReps lb m).length ∧
          ∀ j < k, accP (prMax lb m) ((prReps lb m).getD j default) = false⌝ : IProp GF)
        $$ [i element Hlprs Hsc Hch Hmx]
    · iexists 0; iframe
      isplitl [element]
      · iexists _; iexact element
      ipureintro; exact ⟨by omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    wp_for HI
    wp_if_destruct
    · -- an iteration
      have hkw : sint.Z (W64 (k : Int)) = k := by
        have : sint.Z prs'.len < 2 ^ 63 := by word
        have := Hk.1; rw [← hlen2] at this; word
      have hkl : k < (prReps lb m).length := by
        have h' : sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
        rw [hkw, ← hlenZ2, hlen2] at h'; omega
      have hkl2 : k < (prs ++ [l]).length := by rw [hlen2]; exact hkl
      obtain ⟨lk, hlk⟩ : ∃ lk, (prs ++ [l])[k]? = some lk := ⟨_, List.getElem?_eq_getElem hkl2⟩
      have hbk : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z prs'.len :=
        ⟨by rw [hkw]; omega, Hif⟩
      simp only [hbk, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ _ (prs ++ [l]) _ lk hbk.1 $$ [$Hlprs] as Hlprs
      · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by rw [hkw]; simp]; exact hlk
      ihave #Hk1 := BigSepL.bigSepL_lookup hlk $$ Hreps
      icases ownPReplyP_open _ _ $$ Hk1 with ⟨%kcs, %kds, #Hkl, #Hkc, #Hkd⟩
      ihave #Hkl2 := Hkl
      iStructNamed Hkl
      icases Hel with ⟨%v, Hel⟩
      have hlkD : (prs ++ [l]).getD k null = lk := by simp [List.getD_eq_getElem?_getD, hlk]
      wp_auto
      by_cases hv : ((prReps lb m).getD k default).m.vballot = prMax lb m
      · simp only [hv, _root_.decide_true]
        wp_auto
        wp_if_destruct
        · -- found: sub-case 2
          have hacc : accP (prMax lb m) ((prReps lb m).getD k default) = true := by
            unfold accP; simp only [hv, beq_self_eq_true, Bool.true_and]
            simpa [stACCEPTED] using Hif
          wp_for_post
          rw [findIdx?_first _ _ k hkl hacc Hk.2]
          simp only [scOf, stg, chOf, hlkD]
          iframe
        · have hacc : accP (prMax lb m) ((prReps lb m).getD k default) = false := by
            unfold accP; simp only [hv, beq_self_eq_true, Bool.true_and]
            simpa [stACCEPTED] using Hif
          wp_for_post
          iframe
          iexists k + 1
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          isplitl [Hel]
          · iexists _; iexact Hel
          ipureintro; refine ⟨hkl, fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact Hk.2 j hj
          · subst hj; exact hacc
      · simp only [hv, _root_.decide_false]
        wp_auto
        have hacc : accP (prMax lb m) ((prReps lb m).getD k default) = false := by
          unfold accP
          have h2 : (((prReps lb m).getD k default).m.vballot == prMax lb m) = false := by
            simpa using hv
          rw [h2]
        wp_for_post
        iframe
        iexists k + 1
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe
        isplitl [Hel]
        · iexists _; iexact Hel
        ipureintro; refine ⟨hkl, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact Hk.2 j hj
        · subst hj; exact hacc
    · -- none found
      have hkE : k = (prReps lb m).length := by
        have hkw : sint.Z (W64 (k : Int)) = k := by
          have : sint.Z prs'.len < 2 ^ 63 := by word
          have := Hk.1; rw [← hlen2] at this; word
        have h' : ¬ sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
        have := Hk.1
        rw [hkw, ← hlenZ2, hlen2] at h'; omega
      rw [findIdx?_none _ _ (fun j hj => Hk.2 j (by omega))]
      simp only [scOf, stg, chOf]
      iframe
  · have h1 : (dec1 (prReps lb m)).1 ≠ 0 := by
      intro h; apply Hif; unfold scOf; rw [h]; rfl
    rw [show dec2 (prReps lb m) (prMax lb m) = dec1 (prReps lb m) by
      unfold dec2; rw [if_neg h1]]
    iframe
  -- stage 3's condition
  ihave #Hm2 := Hm
  iStructNamed Hm2
  wp_bind (if: _ then _ else #false)
  iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide ((dec2 (prReps lb m) (prMax lb m)).1 = 0) &&
      isInitialBallot (prMax lb m) m.replica && !(prLr lb m))⌝ ∗
      subCase_ptr ↦ scOf (dec2 (prReps lb m) (prMax lb m)) ∗ maxVbal_ptr ↦ prMax lb m ∗
      y.lb' ↦ prYl yl prs' (prLr lb m)))) $$ [Hsc Hmx Hyl]
  · by_cases h0 : (dec2 (prReps lb m) (prMax lb m)).1 = 0
    · have h0' : scOf (dec2 (prReps lb m) (prMax lb m)) = W64 0 := by unfold scOf; rw [h0]; rfl
      rw [decide_eq_true h0']
      unfold prYl
      wp_auto
      wp_apply pr_wp_isInitialBallot
      cases hI : isInitialBallot (prMax lb m) m.replica
      · wp_auto
        iframe
        ipureintro; simp [h0, hI]
      · wp_auto
        iframe
        ipureintro; simp [h0, hI]
    · have h0' : scOf (dec2 (prReps lb m) (prMax lb m)) ≠ W64 0 := by
        intro h; apply h0
        have hlt := dec2_lt (prReps lb m) (prMax lb m)
        unfold scOf at h; word
      rw [decide_eq_false h0']
      wp_auto
      iframe
      ipureintro; simp [h0]
  iintro %v ⟨%hv, Hsc, Hmx, Hyl⟩
  subst hv
  ipersist isPreAccepted
  generalize hcv : (decide ((dec2 (prReps lb m) (prMax lb m)).1 = 0) &&
      isInitialBallot (prMax lb m) m.replica && !(prLr lb m)) = cv
  -- stage 3: identical pre-accepted replies at the initial ballot
  wp_join iprop(subCase_ptr ↦ scOf (dec3 (prReps lb m) (prMax lb m) (prLr lb m) m.replica) ∗
      chosen_ptr ↦ chOf (prs ++ [l]) (dec3 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).2 ∗
      prs' ↦* (prs ++ [l]) ∗ maxVbal_ptr ↦ prMax lb m ∗ y.lb' ↦ prYl yl prs' (prLr lb m))
    with [Hsc Hch Hlprs Hmx Hyl] as ⟨Hsc, Hch, Hlprs, Hmx, Hyl⟩
  · -- condition false: unchanged
    have hc : ¬ ((dec2 (prReps lb m) (prMax lb m)).1 = 0 ∧
        isInitialBallot (prMax lb m) m.replica = true ∧ prLr lb m = false) := by
      intro h; rw [h.1, h.2.1, h.2.2] at hcv; simp at hcv
    rw [show dec3 (prReps lb m) (prMax lb m) (prLr lb m) m.replica = dec2 (prReps lb m) (prMax lb m) by
      unfold dec3; rw [if_neg hc]]
    iframe
  · -- the loop
    have hc : (dec2 (prReps lb m) (prMax lb m)).1 = 0 ∧
        isInitialBallot (prMax lb m) m.replica = true ∧ prLr lb m = false := by
      have h := hcv; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
    rw [show dec3 (prReps lb m) (prMax lb m) (prLr lb m) m.replica =
        stg 3 ((prReps lb m).findIdx? (subCase3Ok (prReps lb m) (prMax lb m))) by
      unfold dec3; rw [if_pos hc], dec2_zero _ _ hc.1]
    unfold prYl
    ihave ⟨#HN, -, -, -, -, -, -, -, -, -, -, -, -, %HLn⟩ := fwRO_fields _ _ _ _ _ $$ Hfro
    ihave HI : (∃ k : Nat, "Hi" ∷ i_ptr ↦ W64 k ∗ "Hel" ∷ (∃ v : Loc, element_ptr ↦ v) ∗
        "Hlprs" ∷ prs' ↦* (prs ++ [l]) ∗ "Hsc" ∷ subCase_ptr ↦ W64 0 ∗
        "Hch" ∷ chosen_ptr ↦ null ∗ "Hmx" ∷ maxVbal_ptr ↦ prMax lb m ∗
        "%Hk" ∷ ⌜k ≤ (prReps lb m).length ∧
          ∀ j < k, subCase3Ok (prReps lb m) (prMax lb m) ((prReps lb m).getD j default) = false⌝ :
          IProp GF)
        $$ [i element Hlprs Hsc Hch Hmx]
    · iexists 0; iframe
      isplitl [element]
      · iexists _; iexact element
      ipureintro; exact ⟨by omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    wp_for HI
    wp_if_destruct
    · -- an iteration
      have hkw : sint.Z (W64 (k : Int)) = k := by
        have : sint.Z prs'.len < 2 ^ 63 := by word
        have := Hk.1; rw [← hlen2] at this; word
      have hkl : k < (prReps lb m).length := by
        have h' : sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
        rw [hkw, ← hlenZ2, hlen2] at h'; omega
      have hkl2 : k < (prs ++ [l]).length := by rw [hlen2]; exact hkl
      obtain ⟨lk, hlk⟩ : ∃ lk, (prs ++ [l])[k]? = some lk := ⟨_, List.getElem?_eq_getElem hkl2⟩
      have hbk : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z prs'.len :=
        ⟨by rw [hkw]; omega, Hif⟩
      simp only [hbk, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ _ (prs ++ [l]) _ lk hbk.1 $$ [$Hlprs] as Hlprs
      · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by rw [hkw]; simp]; exact hlk
      ihave #Hk1 := BigSepL.bigSepL_lookup hlk $$ Hreps
      icases ownPReplyP_open _ _ $$ Hk1 with ⟨%kcs, %kds, #Hkl, #Hkc, #Hkd⟩
      ihave #Hkl2 := Hkl
      iStructNamed Hkl
      icases Hel with ⟨%v, Hel⟩
      have hlkD : (prs ++ [l]).getD k null = lk := by simp [List.getD_eq_getElem?_getD, hlk]
      generalize hE : (prReps lb m).getD k default = e
      wp_auto
      pa_eval e
      iintro %v ⟨%hv, Hres⟩
      subst hv
      wp_auto
      rcases hpa : isPreAcceptedAt (prMax lb m) e
      · -- not pre-accepted: the next reply
        have hsc3 : subCase3Ok (prReps lb m) (prMax lb m) e = false := by
          unfold subCase3Ok; simp [hpa]
        wp_auto
        wp_for_post
        iframe
        iexists k + 1
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe
        isplitl [Hel]
        · iexists _; iexact Hel
        ipureintro; refine ⟨hkl, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact Hk.2 j hj
        · subst hj; rw [hE]; exact hsc3
      · wp_auto
        by_cases hlr : e.m.acceptorId = e.m.replica
        · -- the leader's own reply: the next reply
          have hsc3 : subCase3Ok (prReps lb m) (prMax lb m) e = false := by
            unfold subCase3Ok; simp [hlr]
          rw [decide_eq_true hlr]
          wp_auto
          wp_for_post
          iframe
          iexists k + 1
          rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
          iframe
          isplitl [Hel]
          · iexists _; iexact Hel
          ipureintro; refine ⟨hkl, fun j hj => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact Hk.2 j hj
          · subst hj; rw [hE]; exact hsc3
        · rw [decide_eq_false hlr]
          wp_auto
          irename AcceptorId => eAcc
          irename Replica => eRep
          irename Instance => eInst
          irename Ballot => eBal
          irename VBallot => eVb
          irename Status => eSt
          irename Command => eCmd
          irename Seq => eSeq
          irename Deps => eDeps
          ihave HJ : (∃ j : Nat, "Hj" ∷ i_ptr ↦ W64 j ∗ "Hot" ∷ (∃ v : Loc, other_ptr ↦ v) ∗
              "Hlprs" ∷ prs' ↦* (prs ++ [l]) ∗ "Hmx" ∷ maxVbal_ptr ↦ prMax lb m ∗
              "Hid" ∷ identical_ptr ↦ W64 ((((prReps lb m).take j).filter (q3 (prMax lb m) e)).length : Nat) ∗
              "%Hj" ∷ ⌜j ≤ (prReps lb m).length⌝ : IProp GF)
              $$ [i other Hlprs Hmx identical]
          · iexists 0; iframe
            isplitl [other]
            · iexists _; iexact other
            ipureintro; omega
          wp_for HJ
          wp_if_destruct
          · -- an inner iteration: reply `o`
            have hjw : sint.Z (W64 (j : Int)) = j := by
              have : sint.Z prs'.len < 2 ^ 63 := by word
              have := Hj; rw [← hlen2] at this; word
            have hjl : j < (prReps lb m).length := by
              have h' : sint.Z (W64 (j : Int)) < sint.Z prs'.len := Hif
              rw [hjw, ← hlenZ2, hlen2] at h'; omega
            have hjl2 : j < (prs ++ [l]).length := by rw [hlen2]; exact hjl
            obtain ⟨lj, hljo⟩ : ∃ lj, (prs ++ [l])[j]? = some lj := ⟨_, List.getElem?_eq_getElem hjl2⟩
            have hbj : 0 ≤ sint.Z (W64 (j : Int)) ∧ sint.Z (W64 (j : Int)) < sint.Z prs'.len :=
              ⟨by rw [hjw]; omega, Hif⟩
            simp only [hbj, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index _ _ (prs ++ [l]) _ lj hbj.1 $$ [$Hlprs] as Hlprs
            · ipureintro; rw [show (sint.Z (W64 (j : Int))).toNat = j by rw [hjw]; simp]; exact hljo
            ihave #Hj1 := BigSepL.bigSepL_lookup hljo $$ Hreps
            icases ownPReplyP_open _ _ $$ Hj1 with ⟨%ocs, %ods, #Hol, #Hoc, #Hod⟩
            iStructNamed Hol
            icases Hot with ⟨%vo, Hot⟩
            have hoD : (prReps lb m).getD j default ∈ prReps lb m := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
            generalize hO : (prReps lb m).getD j default = o at hoD
            wp_auto
            pa_eval o
            iintro %v ⟨%hv, Hres2⟩
            subst hv
            wp_auto
            rcases hpa2 : isPreAcceptedAt (prMax lb m) o
            · have hq : q3 (prMax lb m) e o = false := by unfold q3; simp [hpa2]
              wp_auto
              wp_for_post
              iframe
              iexists j + 1
              rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word,
                take_filter_len_succ _ _ _ hjl, hO, hq]
              simp only [ite_true, ite_false, Bool.false_eq_true, Nat.add_zero]
              iframe
              isplitl [Hot]
              · iexists _; iexact Hot
              ipureintro; omega
            · wp_auto
              by_cases hlr2 : o.m.acceptorId = o.m.replica
              · have hq : q3 (prMax lb m) e o = false := by unfold q3; simp [hlr2]
                rw [decide_eq_true hlr2]
                wp_auto
                wp_for_post
                iframe
                iexists j + 1
                rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word,
                  take_filter_len_succ _ _ _ hjl, hO, hq]
                simp only [ite_true, ite_false, Bool.false_eq_true, Nat.add_zero]
                iframe
                isplitl [Hot]
                · iexists _; iexact Hot
                ipureintro; omega
              · rw [decide_eq_false hlr2]
                wp_auto
                by_cases hsq : o.m.seq = e.m.seq
                · rw [decide_eq_true hsq]
                  wp_auto
                  have hoS : o.m.status ≠ stNONE := by
                    intro h; unfold isPreAcceptedAt at hpa2; rw [h] at hpa2
                    simp [stNONE, stPREACCEPTED, stPREACCEPTED_EQ] at hpa2
                  have heS : e.m.status ≠ stNONE := by
                    intro h; unfold isPreAcceptedAt at hpa; rw [h] at hpa
                    simp [stNONE, stPREACCEPTED, stPREACCEPTED_EQ] at hpa
                  have heM : e ∈ prReps lb m := by
                    rw [← hE]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hkl]
                  have hlen : o.m.deps.length ≤ e.m.deps.length := by
                    rw [hw.hdeps hp o hoD hoS, hw.hdeps hp e heM heS]; exact Nat.le_refl _
                  wp_apply (wp_equal ods kds o.m.deps e.m.deps DFrac.discard DFrac.discard hlen)
                    $$ [$Hod $Hkd] as -
                  rcases hde : depsEqual o.m.deps e.m.deps
                  · have hq : q3 (prMax lb m) e o = false := by unfold q3; simp [hde]
                    wp_auto
                    wp_for_post
                    iframe
                    iexists j + 1
                    rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word,
                      take_filter_len_succ _ _ _ hjl, hO, hq]
                    simp only [ite_true, ite_false, Bool.false_eq_true, Nat.add_zero]
                    iframe
                    isplitl [Hot]
                    · iexists _; iexact Hot
                    ipureintro; omega
                  · have hq : q3 (prMax lb m) e o = true := by
                      unfold q3; simp [hpa2, hlr2, hsq, hde]
                    wp_auto
                    have hcb : (((prReps lb m).take j).filter (q3 (prMax lb m) e)).length ≤ j := by
                      exact Nat.le_trans (List.length_filter_le _ _) (by simp; omega)
                    wp_for_post
                    iframe
                    iexists j + 1
                    rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word,
                      take_filter_len_succ _ _ _ hjl, hO, hq]
                    simp only [ite_true, ite_false, Bool.false_eq_true, Nat.add_zero]
                    rw [show W64 ((((prReps lb m).take j).filter (q3 (prMax lb m) e)).length : Int) + W64 1 =
                      W64 (((((prReps lb m).take j).filter (q3 (prMax lb m) e)).length + 1 : Nat) : Int) by
                        have hb63 : ((prReps lb m).length : Int) < 2 ^ 63 := by
                          rw [← hlen2, hlenZ2]; word
                        have := hcb; have := hjl; word]
                    iframe
                    isplitl [Hot]
                    · iexists _; iexact Hot
                    ipureintro; omega
                · have hq : q3 (prMax lb m) e o = false := by unfold q3; simp [hsq]
                  rw [decide_eq_false hsq]
                  wp_auto
                  wp_for_post
                  iframe
                  iexists j + 1
                  rw [show W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) by word,
                    take_filter_len_succ _ _ _ hjl, hO, hq]
                  simp only [ite_true, ite_false, Bool.false_eq_true, Nat.add_zero]
                  iframe
                  isplitl [Hot]
                  · iexists _; iexact Hot
                  ipureintro; omega
          · -- the count over all replies
            have hjE : j = (prReps lb m).length := by
              have hjw : sint.Z (W64 (j : Int)) = j := by
                have : sint.Z prs'.len < 2 ^ 63 := by word
                have := Hj; rw [← hlen2] at this; word
              have h' : ¬ sint.Z (W64 (j : Int)) < sint.Z prs'.len := Hif
              have := Hj
              rw [hjw, ← hlenZ2, hlen2] at h'; omega
            subst hjE
            rw [List.take_length]
            have hcb : ((prReps lb m).filter (q3 (prMax lb m) e)).length ≤ (prReps lb m).length :=
              List.length_filter_le _ _
            have hb63 : ((prReps lb m).length : Int) < 2 ^ 63 := by rw [← hlen2, hlenZ2]; word
            have hcnt : sint.Z (BitVec.sdiv (W64 (L.length : Int)) (W64 2)) = 2 := by
              rw [HLn.1]; rfl
            have hcz : sint.Z (W64 ((((prReps lb m).filter (q3 (prMax lb m) e)).length : Nat) : Int)) =
                (((prReps lb m).filter (q3 (prMax lb m) e)).length : Int) := by
              have := hcb; word
            rw [hcnt, hcz]
            by_cases h2 : (2 : Int) ≤ (((prReps lb m).filter (q3 (prMax lb m) e)).length : Int)
            · -- sub-case 3: break
              have hsc3 : subCase3Ok (prReps lb m) (prMax lb m) e = true := by
                rw [subCase3Ok_eq]
                have : nR / 2 ≤ ((prReps lb m).filter (q3 (prMax lb m) e)).length := by
                  unfold nR; omega
                simp [hpa, hlr, this]
              rw [decide_eq_true h2]
              wp_auto
              wp_for_post
              rw [findIdx?_first _ _ k hkl (by rw [hE]; exact hsc3) Hk.2]
              simp only [scOf, stg, chOf, hlkD]
              iframe
            · have hsc3 : subCase3Ok (prReps lb m) (prMax lb m) e = false := by
                rw [subCase3Ok_eq]
                have : ¬ nR / 2 ≤ ((prReps lb m).filter (q3 (prMax lb m) e)).length := by
                  unfold nR; omega
                simp [this]
              rw [decide_eq_false h2]
              wp_auto
              wp_for_post
              iframe
              iexists k + 1
              rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
              iframe
              isplitl [Hel]
              · iexists _; iexact Hel
              ipureintro; refine ⟨hkl, fun j hj => ?_⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
              · exact Hk.2 j hj
              · subst hj; rw [hE]; exact hsc3
    · -- none: no sub-case 3
      have hkE : k = (prReps lb m).length := by
        have hkw : sint.Z (W64 (k : Int)) = k := by
          have : sint.Z prs'.len < 2 ^ 63 := by word
          have := Hk.1; rw [← hlen2] at this; word
        have h' : ¬ sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
        have := Hk.1
        rw [hkw, ← hlenZ2, hlen2] at h'; omega
      rw [findIdx?_none _ _ (fun j hj => Hk.2 j (by omega))]
      simp only [scOf, stg, chOf]
      iframe
  -- stage 5: a pre-accepted reply at maxVbal
  wp_join iprop(subCase_ptr ↦ scOf (dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica) ∗
      chosen_ptr ↦ chOf (prs ++ [l]) (dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).2 ∗
      prs' ↦* (prs ++ [l]) ∗ maxVbal_ptr ↦ prMax lb m ∗ y.lb' ↦ prYl yl prs' (prLr lb m))
    with [Hsc Hch Hlprs Hmx Hyl] as ⟨Hsc, Hch, Hlprs, Hmx, Hyl⟩
  · have h1 : (dec3 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 = 0 := by
      have := Hif; unfold scOf at this
      have hlt := dec3_lt (prReps lb m) (prMax lb m) (prLr lb m) m.replica
      word
    rw [dec3_zero _ _ _ _ h1]
    rw [show dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica =
        stg 5 ((prReps lb m).findIdx? (isPreAcceptedAt (prMax lb m))) by
      unfold dec5; rw [if_pos h1]]
    unfold prYl
    ihave HI : (∃ k : Nat, "Hi" ∷ i_ptr ↦ W64 k ∗ "Hel" ∷ (∃ v : Loc, element_ptr ↦ v) ∗
        "Hlprs" ∷ prs' ↦* (prs ++ [l]) ∗ "Hsc" ∷ subCase_ptr ↦ W64 0 ∗
        "Hch" ∷ chosen_ptr ↦ null ∗ "Hmx" ∷ maxVbal_ptr ↦ prMax lb m ∗
        "%Hk" ∷ ⌜k ≤ (prReps lb m).length ∧
          ∀ j < k, isPreAcceptedAt (prMax lb m) ((prReps lb m).getD j default) = false⌝ :
          IProp GF)
        $$ [i element Hlprs Hsc Hch Hmx]
    · iexists 0; iframe
      isplitl [element]
      · iexists _; iexact element
      ipureintro; exact ⟨by omega, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
    wp_for HI
    wp_if_destruct
    · -- an iteration
      have hkw : sint.Z (W64 (k : Int)) = k := by
        have : sint.Z prs'.len < 2 ^ 63 := by word
        have := Hk.1; rw [← hlen2] at this; word
      have hkl : k < (prReps lb m).length := by
        have h' : sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
        rw [hkw, ← hlenZ2, hlen2] at h'; omega
      have hkl2 : k < (prs ++ [l]).length := by rw [hlen2]; exact hkl
      obtain ⟨lk, hlk⟩ : ∃ lk, (prs ++ [l])[k]? = some lk := ⟨_, List.getElem?_eq_getElem hkl2⟩
      have hbk : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z prs'.len :=
        ⟨by rw [hkw]; omega, Hif⟩
      simp only [hbk, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index _ _ (prs ++ [l]) _ lk hbk.1 $$ [$Hlprs] as Hlprs
      · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by rw [hkw]; simp]; exact hlk
      ihave #Hk1 := BigSepL.bigSepL_lookup hlk $$ Hreps
      icases ownPReplyP_open _ _ $$ Hk1 with ⟨%kcs, %kds, #Hkl, #Hkc, #Hkd⟩
      ihave #Hkl2 := Hkl
      iStructNamed Hkl
      icases Hel with ⟨%v, Hel⟩
      have hlkD : (prs ++ [l]).getD k null = lk := by simp [List.getD_eq_getElem?_getD, hlk]
      generalize hE : (prReps lb m).getD k default = e
      wp_auto
      pa_eval e
      iintro %v ⟨%hv, Hres⟩
      subst hv
      wp_auto
      rcases hpa : isPreAcceptedAt (prMax lb m) e
      · wp_auto
        wp_for_post
        iframe
        iexists k + 1
        rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
        iframe
        isplitl [Hel]
        · iexists _; iexact Hel
        ipureintro; refine ⟨hkl, fun j hj => ?_⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · exact Hk.2 j hj
        · subst hj; rw [hE]; exact hpa
      · -- found: sub-case 5
        wp_auto
        wp_for_post
        rw [findIdx?_first _ _ k hkl (by rw [hE]; exact hpa) Hk.2]
        simp only [scOf, stg, chOf, hlkD]
        iframe
    · have hkE : k = (prReps lb m).length := by
        have hkw : sint.Z (W64 (k : Int)) = k := by
          have : sint.Z prs'.len < 2 ^ 63 := by word
          have := Hk.1; rw [← hlen2] at this; word
        have h' : ¬ sint.Z (W64 (k : Int)) < sint.Z prs'.len := Hif
        have := Hk.1
        rw [hkw, ← hlenZ2, hlen2] at h'; omega
      rw [findIdx?_none _ _ (fun j hj => Hk.2 j (by omega))]
      simp only [scOf, stg, chOf]
      iframe
  · have h1 : (dec3 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 ≠ 0 := by
      intro h; apply Hif; unfold scOf; rw [h]; rfl
    rw [show dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica =
        dec3 (prReps lb m) (prMax lb m) (prLr lb m) m.replica by
      unfold dec5; rw [if_neg h1]]
    iframe
  -- stage 6: a no-op
  wp_join iprop(subCase_ptr ↦ scOf (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica))
    with [Hsc] as Hsc
  · have h1 : (dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 = 0 := by
      have := Hif; unfold scOf at this
      have hlt := dec5_lt (prReps lb m) (prMax lb m) (prLr lb m) m.replica
      word
    rw [show dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica = (6, none) by
      unfold dec6; rw [if_pos h1]]
    unfold scOf; iexact Hsc
  · have h1 : (dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 ≠ 0 := by
      intro h; apply Hif; unfold scOf; rw [h]; rfl
    rw [show dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica =
        dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica by
      unfold dec6; rw [if_neg h1]]
    iexact Hsc
  -- the decision is the model's
  have hdec : prDec lb m = ((dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1,
      (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).2.map
        (fun j => (prReps lb m).getD j default)) := (dec6_eq _ _ _ _).symm
  rw [← dec6_snd] at *
  rcases hch : (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).2 with _ | j
  · -- no reply chosen: a no-op (sub-case 6)
    simp only [chOf]
    wp_auto
    have hNoop' := hNoop
    unfold state.NOOP.spec at hNoop'
    wp_apply hNoop' as %ncs Hncs
    have hd5 : (dec5 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 = 0 :=
      dec5_none _ _ _ _ (by rw [← dec6_snd]; exact hch)
    have hd6 : dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica = (6, none) := by
      unfold dec6; rw [if_pos hd5]
    have hprd : prDec lb m = (6, none) := by rw [hdec, hd6]; rfl
    rw [hd6]
    simp only [scOf]
    unfold epaxos.NONE
    wp_auto
    simp only
    have hcpd : decide (w.status = stEXECUTED) = false := by
      apply decide_eq_false; intro h; rw [h] at hc; revert hc; decide
    have hprLb : prLb lb m = { lb with prepareReplies := prReps lb m, preparing := false, leaderResponded := prLr lb m, ballot := prMax lb m, cmds := some noop, status := stNONE } := by
      unfold prLb; rw [hprd]
    have h1 : (prDec lb m).1 ≠ 1 := by rw [hprd]; decide
    have hne : ¬ ((prDec lb m).1 = 2 ∨ (prDec lb m).1 = 3) := by rw [hprd]; decide
    have hcmds : (prLb lb m).cmds.getD [] = noop := by rw [hprLb]; rfl
    have hltb := Hylf.2.2.2.2.2.2.2.1
    have hseq := Hylf.2.2.2.2.2.2.2.2.2.1
    rw [hltb]
    icases ownRepRest_open _ _ _ $$ Hrest with ⟨Hcrt, Hcut, Hrest⟩
    ihave Hins := Hclose $$ %ptr %(slotSeq (some (prInstP w lb m))) [Hptrs] [Hy]
    · rw [hset]; iexact Hptrs
    · unfold slotSeq; iexists _; iframe Hy; ipureintro
      simp [prInstP, prInst, hprLb, hseq]
    imod ownCmds_persist _ _ _ $$ Hncs with #Hncs
    ihave %Hncsnn := ownCmds_nonnil _ _ _ (by simp [noopCmds]) $$ Hncs
    have hout := hw.houts
    rw [hPR_main σ m w lb hw.hw hw.hlb hp hc hb he hd hl, if_neg h1, if_neg hne, he, hcmds,
      prLb_ltb, prLb_cp] at hout
    rw [hPR_main σ m w lb hw.hw hw.hlb hp hc hb he hd hl, if_neg h1, if_neg hne, he, hcmds,
      prLb_ltb, prLb_cp]
    have hwfP : RepWf i ((bumpRecvBallot σ lb.lastTriedBallot).setInst
        ⟨toN m.replica, toN m.inst⟩ (prInstP w lb m)) ord :=
      ⟨by simpa [RState.setInst] using hw.hrep.id, hw.hrep.hi,
        by simpa [RState.setInst] using hw.hrep.po⟩
    have hconfP : ConfWf ((bumpRecvBallot σ lb.lastTriedBallot).setInst
        ⟨toN m.replica, toN m.inst⟩ (prInstP w lb m)) :=
      confWf_upd σ ⟨toN m.replica, toN m.inst⟩ (prInstP w lb m) hw.hconf _
        (by simp [RState.setInst]) (by simp [RState.setInst]) (by simp [RState.setInst])
        (by simp [RState.setInst])
    wp_apply (wp_startPhase1 hS γ i r rr L p Rext ord _ ncs noop m.replica m.inst lb.lastTriedBallot
        yl.clientProposals' lb.clientProposals hwfP hw.hq hw.hn Hncsnn hconfP hw.hord hout)
      $$ [Hins Hrest Hcrt Hcut Hcp Hf Houts]
    · iframe Hf Houts
      isplitl []
      · unfold hdCtx epROFields prefOrder; iexact Hctx0
      isplitl [Hins Hrest Hcrt Hcut]
      · unfold ownRepHole
        isplitr
        · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
        isplitr
        · ipureintro; simpa [RState.setInst] using Hcb
        isplitl [Hins]
        · iapply repInstsP_congr _ _ _ ?_ $$ Hins
          funext y' pt
          unfold updP
          by_cases hy : y' = ⟨toN m.replica, toN m.inst⟩
          · subst hy; simp [RState.setInst, upd]
          · simp [hy, instAtP, RState.setInst, upd]
        · rw [ownRepRest_setInst]; iapply Hrest $$ Hcrt Hcut
      isplitl []
      · rw [show noop = noopCmds from rfl]; iexact Hncs
      rw [hcpd]
      unfold propsOwn
      rcases hcps : lb.clientProposals with _ | ps
      · simp only [hcps]; iexact Hcp
      · simp only [hcps]
        icases Hcp with ⟨%Hp1, #Hp2, Hp3⟩
        iexists gs; iframe Hp2 Hp3; ipureintro; exact Hp1
    iintro HD
    wp_auto
    iapply HΦ $$ HD
  · -- the chosen reply `j`
    have hjl : j < (prReps lb m).length := by
      rw [dec6_snd] at hch; exact dec5_idx _ _ _ _ _ hch
    have hjl2 : j < (prs ++ [l]).length := by rw [hlen2]; exact hjl
    obtain ⟨lc, hlc⟩ : ∃ lc, (prs ++ [l])[j]? = some lc := ⟨_, List.getElem?_eq_getElem hjl2⟩
    have hlcD : (prs ++ [l]).getD j null = lc := by simp [List.getD_eq_getElem?_getD, hlc]
    simp only [chOf, hlcD]
    ihave #Hc1 := BigSepL.bigSepL_lookup hlc $$ Hreps
    icases ownPReplyP_open _ _ $$ Hc1 with ⟨%ccs, %cds, #Hcl, #Hcc, #Hcd⟩
    have hjM : (prReps lb m).getD j default ∈ lb.prepareReplies ++ [⟨m, false⟩] := by
      show _ ∈ prReps lb m
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
    have hjS := dec6_status _ _ _ _ j hch
    ihave #Hcc := cmdsRep_of_prCmds _ _ _ (fun _ => hw.hcmd hp _ hjM hjS) $$ Hcc
    ihave %Hlcnn := typedPointsto_not_null _ _ _ $$ Hcl
    iStructNamed Hcl
    rw [show decide (lc = null) = false from decide_eq_false Hlcnn]
    wp_auto
    simp only
    have hcpd : decide (w.status = stEXECUTED) = false := by
      apply decide_eq_false; intro h; rw [h] at hc; revert hc; decide
    have hprd : prDec lb m = ((dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1,
        some ((prReps lb m).getD j default)) := by rw [hdec, hch]; rfl
    have hprLb : prLb lb m = { lb with prepareReplies := prReps lb m, preparing := false, leaderResponded := prLr lb m, ballot := prMax lb m, cmds := if ((prReps lb m).getD j default).cmdsNil then none else some ((prReps lb m).getD j default).m.command, seq := ((prReps lb m).getD j default).m.seq, deps := ((prReps lb m).getD j default).m.deps, status := ((prReps lb m).getD j default).m.status } := by
      unfold prLb; rw [hprd]
    have hlt6 : (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 < 7 := by
      unfold dec6; split
      · decide
      · have := dec5_lt (prReps lb m) (prMax lb m) (prLr lb m) m.replica; omega
    icases ownRepRest_open _ _ _ $$ Hrest with ⟨Hcrt, Hcut, Hrest⟩
    wp_if_destruct
    · -- sub-case 1: committed elsewhere
      have h1 : (prDec lb m).1 = 1 := by
        rw [hprd]; have := Hif; unfold scOf at this; simp only; word
      unfold epaxos.COMMITTED
      wp_auto
      -- the slot closed with the committed record
      have hltb := Hylf.2.2.2.2.2.2.2.1
      have hexl : (prInstC w lb m).status ≠ stEXECUTED := by simp [prInstC, stCOMMITTED, stEXECUTED]
      have hyf' : ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 4, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).bal' = (prInstC w lb m).bal ∧ ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 4, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).vbal' = (prInstC w lb m).vbal ∧ ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 4, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).Status' = (prInstC w lb m).status ∧ ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 4, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).Seq' = (prInstC w lb m).seq ∧ ((prInstC w lb m).status ≠ stEXECUTED → ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 4, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).Index' = W64 0) := by
        have hwx : w.status ≠ stEXECUTED := by intro h; rw [h] at hc; revert hc; decide
        simp only [prInstC, prInst, prLb_ltb, hprLb, hltb]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact fun _ => Hyf.2.2.2.2 hwx
      have hf' : LbF ({ prYl yl prs' (prLr lb m) with ballot' := prMax lb m, cmds' := ccs, status' := W8 4, seq' := ((prReps lb m).getD j default).m.seq, deps' := cds } : epaxos.LeaderBookkeeping) { prLb lb m with status := stCOMMITTED } := by
        unfold LbF prYl; simp only [hprLb]
        obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | assumption
      ihave Hx := inst_close_new (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr _ (prInstC w lb m)
        { prLb lb m with status := stCOMMITTED } _ gs (prs ++ [l]) yl.clientProposals' hyf' rfl hf'
        (by simp [lbDepsOwned, stCOMMITTED, stPREACCEPTED, stPREACCEPTED_EQ]) hexl rfl
        $$ [Hy Hyl Hcp Hlprs Hlcap]
      · simp only [prInstC, prInst, hprLb, prYl]
        rw [hcpd]
        iframe Hy Hyl Hlprs Hlcap Hcp Hcc Hcd
        isplitl []
        · iexact Hyid
        isplitr
        · ipureintro; exact Hlbnn
        isplitr
        · ipureintro; exact hlen2
        iapply BigSepL.bigSepL_mono (fun _ => ownPReplyP_to _ _) $$ Hreps
      ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt
        (some (prInstC w lb m))) [Hptrs] Hx
      · rw [hset]; iexact Hptrs
      ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
      · iexact Hins
      have hib2 : instBounds ((bumpRecvBallot σ lb.lastTriedBallot).setInst
          ⟨toN m.replica, toN m.inst⟩ (prInstC w lb m)).inst := by
        simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
      have hcb2 : cutBounds ((bumpRecvBallot σ lb.lastTriedBallot).setInst
          ⟨toN m.replica, toN m.inst⟩ (prInstC w lb m)).committedUpTo := by
        simpa [RState.setInst] using Hcb
      wp_apply (wp_updateCommitted γ i r rr L p Rext ((bumpRecvBallot σ lb.lastTriedBallot).setInst
          ⟨toN m.replica, toN m.inst⟩ (prInstC w lb m)) m.replica hw.hq hib2 hcb2)
        $$ [$Hrr $Hfw Hins Hcut] as ⟨Hins, Hcut⟩
      · simp only [RState.setInst, bumpRecvBallot_inst, bumpRecvBallot_cut]
        iframe Hins Hcut
      rw [hPR_main σ m w lb hw.hw hw.hlb hp hc hb he hd hl, if_pos h1, he]
      simp only
      iapply HΦ
      iapply repDone_of γ i r _ _ (pr_noSends_ev _)
      iframe Hf Houts
      iapply ownRep_of
      isplitr
      · ipureintro; simpa [updateCommitted] using hib2
      isplitr
      · ipureintro
        exact cutBounds_updateCommitted _ _ hib2 hcb2
      isplitl [Hins]
      · simp only [updateCommitted, RState.setInst]; iexact Hins
      rw [show ownRepRest i r (updateCommitted ((bumpRecvBallot σ lb.lastTriedBallot).setInst
          ⟨toN m.replica, toN m.inst⟩ (prInstC w lb m)) (toN m.replica)) =
        ownRepRest i r { bumpRecvBallot σ lb.lastTriedBallot with committedUpTo :=
          (updateCommitted ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstC w lb m)) (toN m.replica)).committedUpTo } from rfl]
      simp only [updateCommitted, RState.setInst]
      iapply Hrest $$ Hcrt Hcut
    · have h1 : (prDec lb m).1 ≠ 1 := by
        rw [hprd]; intro h; apply Hif; unfold scOf; simp only at h; rw [h]; rfl
      wp_bind (if: _ then #true else _)
      iapply (wp_wand (Φ := fun v => iprop(⌜v = #(decide ((prDec lb m).1 = 2 ∨ (prDec lb m).1 = 3))⌝ ∗
          subCase_ptr ↦ scOf (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica)))) $$ [Hsc]
      · have hsc : (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 = (prDec lb m).1 := by
          rw [hprd]
        by_cases h2 : (prDec lb m).1 = 2
        · have : scOf (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica) = W64 2 := by
            unfold scOf; rw [hsc, h2]; rfl
          rw [this]
          wp_auto
          iframe; ipureintro; simp [h2]
        · have : scOf (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica) ≠ W64 2 := by
            unfold scOf; rw [hsc]; intro h; apply h2; have := hlt6; rw [hsc] at this; word
          rw [decide_eq_false this]
          wp_auto
          by_cases h3 : (prDec lb m).1 = 3
          · have : scOf (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica) = W64 3 := by
              unfold scOf; rw [hsc, h3]; rfl
            rw [this]
            iframe; ipureintro; simp [h3]
          · have : scOf (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica) ≠ W64 3 := by
              unfold scOf; rw [hsc]; intro h; apply h3; have := hlt6; rw [hsc] at this; word
            rw [decide_eq_false this]
            iframe; ipureintro; simp [h2, h3]
      iintro %v ⟨%hv, Hsc⟩
      subst hv
      wp_if_destruct
      · -- sub-cases 2/3: accept
        have h23 : (prDec lb m).1 = 2 ∨ (prDec lb m).1 = 3 := by simpa using Hif
        unfold epaxos.ACCEPTED
        wp_auto
        have hltb := Hylf.2.2.2.2.2.2.2.1
        have hexl : (prInstA w lb m).status ≠ stEXECUTED := by simp [prInstA, stACCEPTED, stEXECUTED]
        have hyf' : ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 3, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).bal' = (prInstA w lb m).bal ∧ ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 3, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).vbal' = (prInstA w lb m).vbal ∧ ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 3, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).Status' = (prInstA w lb m).status ∧ ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 3, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).Seq' = (prInstA w lb m).seq ∧ ((prInstA w lb m).status ≠ stEXECUTED → ({ y with Cmds' := ccs, bal' := yl.lastTriedBallot', vbal' := yl.lastTriedBallot', Status' := W8 3, Seq' := ((prReps lb m).getD j default).m.seq, Deps' := cds } : epaxos.Instance).Index' = W64 0) := by
          have hwx : w.status ≠ stEXECUTED := by intro h; rw [h] at hc; revert hc; decide
          simp only [prInstA, prInst, prLb_ltb, hprLb, hltb]
          refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | exact fun _ => Hyf.2.2.2.2 hwx
        have hf' : LbF ({ prYl yl prs' (prLr lb m) with ballot' := prMax lb m, cmds' := ccs, status' := W8 3, seq' := ((prReps lb m).getD j default).m.seq, deps' := cds } : epaxos.LeaderBookkeeping) (prLbA lb m) := by
          unfold LbF prYl prLbA; simp only [hprLb]
          obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12⟩ := Hylf
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | rfl | assumption
        have hdoA : lbDepsOwned (prLbA lb m) = false := by
          simp [prLbA, lbDepsOwned, stACCEPTED, stPREACCEPTED, stPREACCEPTED_EQ]
        ihave Hx := inst_close_new (GF := GF) γ i ⟨toN m.replica, toN m.inst⟩ ptr _ (prInstA w lb m)
          (prLbA lb m) _ gs (prs ++ [l]) yl.clientProposals' hyf' rfl hf' hdoA hexl rfl
          $$ [Hy Hyl Hcp Hlprs Hlcap]
        · simp only [prInstA, prLbA, prInst, hprLb, prYl]
          rw [hcpd]
          iframe Hy Hyl Hlprs Hlcap Hcp Hcc Hcd
          isplitl []
          · iexact Hyid
          isplitr
          · ipureintro; exact Hlbnn
          isplitr
          · ipureintro; exact hlen2
          iapply BigSepL.bigSepL_mono (fun _ => ownPReplyP_to _ _) $$ Hreps
        ihave Hins := Hclose $$ %ptr %(fun pt => instAt γ i ⟨toN m.replica, toN m.inst⟩ pt
          (some (prInstA w lb m))) [Hptrs] Hx
        · rw [hset]; iexact Hptrs
        ihave Hins := repInstsP_upd (GF := GF) γ i r σ.inst _ _ $$ [Hins]
        · iexact Hins
        have hib2 : instBounds ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m)).inst := by
          simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
        ihave Hrep : ownRep γ i r ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m)) $$ [Hins Hrest Hcrt Hcut]
        · iapply ownRep_of
          isplitr
          · ipureintro; exact hib2
          isplitr
          · ipureintro; simpa [RState.setInst] using Hcb
          isplitl [Hins]
          · simp only [RState.setInst, bumpRecvBallot_inst]; iexact Hins
          rw [ownRepRest_setInst]
          iapply Hrest $$ Hcrt Hcut
        have hout := hw.houts
        rw [hPR_main σ m w lb hw.hw hw.hlb hp hc hb he hd hl, if_neg h1, if_pos h23, he] at hout
        rw [hPR_main σ m w lb hw.hw hw.hlb hp hc hb he hd hl, if_neg h1, if_pos h23, he]
        simp only
        rw [show ∀ a b c : Out, [a, b, c] = [a, b] ++ [c] from fun _ _ _ => rfl]
        icases outsOk_bcast γ i _ _ (by intro o ho; simp at ho; rcases ho with rfl | rfl <;>
          exact ⟨fun _ _ h => Out.noConfusion h, fun _ h => Out.noConfusion h⟩) $$ Houts with
          ⟨Hob, Hpend, Hcur⟩
        have hwfA : RepWf i ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m)) ord :=
          ⟨by simpa [RState.setInst] using hw.hrep.id, hw.hrep.hi,
            by simpa [RState.setInst] using hw.hrep.po⟩
        have hwA : ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m)).inst ⟨toN m.replica, toN m.inst⟩ =
            some (prInstA w lb m) := by simp [RState.setInst, upd]
        have hm : (Msg.accept (acceptOf ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m)) m.replica m.inst (prLbA lb m))).wf :=
          hout (Out.bcast (bcastAcceptOf ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m)) ⟨toN m.replica, toN m.inst⟩
            (acceptOf ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstA w lb m)) m.replica m.inst (prLbA lb m)))) (by simp)
        wp_apply (wp_bcastAccept hS γ i r rr L p Rext ord _ m.replica m.inst (prInstA w lb m)
            (prLbA lb m) hwfA hw.hq hw.hn hwA rfl hdoA hm hw.hord)
          $$ [Hrep Hf Hpend Hob] as ⟨Hrep, Hf, Hpend, Hob⟩
        · iframe Hrep Hf Hpend Hob
          unfold hdCtx epROFields prefOrder; iexact Hctx0
        iapply HΦ
        unfold repDone
        iexists _
        iframe Hrep Hf
        unfold repIdle outboxesNil
        iframe
      · -- sub-case 4 is dead; sub-case 5: Phase 1 for the pre-accepted reply
        have hne : ¬ ((prDec lb m).1 = 2 ∨ (prDec lb m).1 = 3) := by simpa using Hif
        have h4 : scOf (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica) ≠ W64 4 := by
          unfold scOf; intro h; apply dec6_ne4 (prReps lb m) (prMax lb m) (prLr lb m) m.replica
          have := hlt6; word
        rw [decide_eq_false h4]
        wp_auto
        have hd6 : (dec6 (prReps lb m) (prMax lb m) (prLr lb m) m.replica).1 = (prDec lb m).1 := by
          rw [hprd]
        have hpa : isPreAcceptedAt (prMax lb m) ((prReps lb m).getD j default) = true :=
          dec6_five _ _ _ _ j ⟨by rw [hd6]; exact h1, by rw [hd6]; intro h; exact hne (Or.inl h),
            by rw [hd6]; intro h; exact hne (Or.inr h)⟩ hch
        have hcn : ((prReps lb m).getD j default).cmdsNil = false := by
          rcases hcn : ((prReps lb m).getD j default).cmdsNil
          · rfl
          · exfalso
            have hmem : (prReps lb m).getD j default ∈ prReps lb m := by
              simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]
            generalize ((prReps lb m).getD j default) = e at hmem hcn hpa
            have hmem' : e ∈ lb.prepareReplies ++ [⟨m, false⟩] := hmem
            rcases List.mem_append.mp hmem' with hm' | hm'
            · have := hw.hnil hp _ hm' hcn
              unfold isPreAcceptedAt at hpa; rw [this] at hpa
              simp [stNONE, stPREACCEPTED, stPREACCEPTED_EQ] at hpa
            · simp at hm'; rw [hm'] at hcn; simp at hcn
        have hltb := Hylf.2.2.2.2.2.2.2.1
        rw [hltb]
        -- the state startPhase1 starts from: slot x about to be overwritten
        ihave Hins := Hclose $$ %ptr %(slotSeq (some (prInstP w lb m))) [Hptrs] [Hy]
        · rw [hset]; iexact Hptrs
        · unfold slotSeq; iexists _; iframe Hy; ipureintro
          simp [prInstP, prInst, hprLb]
        have hcmds : (prLb lb m).cmds.getD [] = ((prReps lb m).getD j default).m.command := by
          rw [hprLb]; simp only [hcn, Bool.false_eq_true, ite_false, Option.getD_some]
        rw [hcn]
        simp only [Bool.false_eq_true, ite_false]
        unfold cmdsRep
        icases Hcc with ⟨%Hccnn, #Hcc⟩
        have hout := hw.houts
        rw [hPR_main σ m w lb hw.hw hw.hlb hp hc hb he hd hl, if_neg h1, if_neg hne, he, hcmds,
          prLb_ltb, prLb_cp] at hout
        rw [hPR_main σ m w lb hw.hw hw.hlb hp hc hb he hd hl, if_neg h1, if_neg hne, he, hcmds,
          prLb_ltb, prLb_cp]
        have hwfP : RepWf i ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstP w lb m)) ord :=
          ⟨by simpa [RState.setInst] using hw.hrep.id, hw.hrep.hi,
            by simpa [RState.setInst] using hw.hrep.po⟩
        have hconfP : ConfWf ((bumpRecvBallot σ lb.lastTriedBallot).setInst
            ⟨toN m.replica, toN m.inst⟩ (prInstP w lb m)) :=
          confWf_upd σ ⟨toN m.replica, toN m.inst⟩ (prInstP w lb m) hw.hconf _
            (by simp [RState.setInst]) (by simp [RState.setInst]) (by simp [RState.setInst])
            (by simp [RState.setInst])
        wp_apply (wp_startPhase1 hS γ i r rr L p Rext ord _ ccs _ m.replica m.inst lb.lastTriedBallot
            yl.clientProposals' lb.clientProposals hwfP hw.hq hw.hn Hccnn hconfP hw.hord hout)
          $$ [Hins Hrest Hcrt Hcut Hcp Hf Houts]
        · iframe Hf Houts Hcc
          isplitl []
          · unfold hdCtx epROFields prefOrder; iexact Hctx0
          isplitl [Hins Hrest Hcrt Hcut]
          · unfold ownRepHole
            isplitr
            · ipureintro; simpa [RState.setInst] using instBounds_upd _ _ _ Hib hq' hw.hn.2
            isplitr
            · ipureintro; simpa [RState.setInst] using Hcb
            isplitl [Hins]
            · iapply repInstsP_congr _ _ _ ?_ $$ Hins
              funext y' pt
              unfold updP
              by_cases hy : y' = ⟨toN m.replica, toN m.inst⟩
              · subst hy; simp [RState.setInst, upd]
              · simp [hy, instAtP, RState.setInst, upd]
            · rw [ownRepRest_setInst]; iapply Hrest $$ Hcrt Hcut
          · rw [hcpd]
            unfold propsOwn
            rcases hcps : lb.clientProposals with _ | ps
            · simp only [hcps]; iexact Hcp
            · simp only [hcps]
              icases Hcp with ⟨%Hp1, #Hp2, Hp3⟩
              iexists gs; iframe Hp2 Hp3; ipureintro; exact Hp1
        iintro HD
        wp_auto
        iapply HΦ $$ HD
  done

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
