/-
Package `proxy`: the internal specs of `Proxy.Run`'s pieces (statements only, as `Prop`s, so that
their proofs are independent: a proof takes the specs of what it calls as hypotheses; `Run.lean`
links them). The main loop's state is `ownQ γ c k pr γq` (`OwnProp.lean`), the shared facts
`proxySharedDef γ c k pr`.
-/
module

public import Dsverify.Proof.raxos.Proxy.Usm
public import Dsverify.Proof.raxos.Proxy.Issue
public import Dsverify.Proof.raxos.Proxy.Store
public import Perennial.Proof.time.Link
public import Dsverify.Proof.raxos.Proxy.MabSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

set_option hygiene false in
/-- After `wp_for`: case split on the loop's condition (`Hif`), when `wp_if_destruct` picks
another `if:` of the body. -/
macro "wp_loop_if" : tactic => `(tactic| (cleanup_bool_decide; split <;>
  (rename_i Hif; simp only [decide_eq_true_eq, Bool.not_eq_true, decide_eq_false_iff_not] at Hif;
    (try wp_auto))))

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]

attribute [local instance] HeapGS.goose_globalGS

/-! ## The timers (`common.TimerWithCancel`) -/

/-- A `TimerWithCancel` not started yet, with duration `d` and function `f` (its cancel channel,
read for good). -/
def timerOwn (t : Loc) (d : time.Duration) (f : GoFunc) : IProp GF :=
  iprop(∃ (tt ch : Loc) (γc : ChanNames),
    t.[raxos.common.TimerWithCancel, go!"t"] ↦ tt ∗ t.[raxos.common.TimerWithCancel, go!"d"] ↦ d ∗
    t.[raxos.common.TimerWithCancel, go!"c"] ↦□ ch ∗
    isChanBag (V := GoInterface) γc ch (fun _ => iprop(True)) ∗
    t.[raxos.common.TimerWithCancel, go!"f"] ↦ f)

abbrev NewTimerWithCancel_spec : Prop :=
  ∀ (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.common }}
    (App (Val (@! raxos.common.NewTimerWithCancel)) (Val #d))
  {{ (t : Loc), RET #t; timerOwn t d func.nil }}

abbrev SetTimeoutFuntion_spec : Prop :=
  ∀ (t : Loc) (d : time.Duration) (f0 f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.common ∗ timerOwn t d f0 }}
    (App (Val (t @!! go.GoType.PointerType raxos.common.TimerWithCancel.ty @!! go!"SetTimeoutFuntion"))
      (Val #f))
  {{ RET #(); timerOwn t d f }}

/-- `t.Start()`: the timer's goroutine calls `f` at most once (its single-call WP is given). -/
abbrev Start_spec : Prop :=
  ∀ (t : Loc) (d : time.Duration) (f : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.common ∗ timerOwn t d f ∗
      (∀ Φ : val → IProp GF, ▷ Φ #() -∗ WP (App (Val #f) (Val #())) {{ Φ }}) }}
    (App (Val (t @!! go.GoType.PointerType raxos.common.TimerWithCancel.ty @!! go!"Start")) (Val #()))
  {{ RET #(); True }}

/-! ## The handlers -/

/-- `pr.handleDecisionNotification()`: sends the decided slots to piggyback, if any. -/
abbrev handleDecisionNotification_spec : Prop :=
  ∀ (γ : QNames) (pr : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
      chanField Decision.ty pr go!"proxyToProposerDecisionChan" (decisionP γ) ∗ decState γ pr }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"handleDecisionNotification")) (Val #()))
  {{ RET #(); decState γ pr }}

abbrev handleClientBatch_spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γq : GName) (v : raxos.proto.client.ClientBatch),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxySharedDef γ c k pr ∗
      ownQ γ c k pr γq ∗ cbReqP γ v }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"handleClientBatch")) (Val #v))
  {{ RET #(); ownQ γ c k pr γq }}

abbrev proposeToIndex_spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γq : GName) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxySharedDef γ c k pr ∗
      ownQ γ c k pr γq ∗ reqIdxP γq ⟨i⟩ }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"proposeToIndex")) (Val #i))
  {{ RET #(); ownQ γ c k pr γq }}

abbrev handleProposeResponse_spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γq : GName) (m : ProposeResponse),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxySharedDef γ c k pr ∗
      ownQ γ c k pr γq ∗ proposeRespP γ k m }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"handleProposeResponse")) (Val #m))
  {{ RET #(); ownQ γ c k pr γq }}

abbrev handleRecorderResponse_spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γq : GName) (m : Decision),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxySharedDef γ c k pr ∗
      ownQ γ c k pr γq ∗ decisionP γ m }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"handleRecorderResponse")) (Val #m))
  {{ RET #(); ownQ γ c k pr γq }}

abbrev handleFetchResponse_spec : Prop :=
  ∀ (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γq : GName) (m : FetchResposne),
  {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proxySharedDef γ c k pr ∗
      ownQ γ c k pr γq ∗ fetchRespP γ m }}
    (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"handleFetchResponse")) (Val #m))
  {{ RET #(); ownQ γ c k pr γq }}

/-! ## Shared facts -/

/-- `updateStateMachine`'s shared facts, from the proxy's (the store's from `ownQ`'s). -/
theorem usmShared_of (γ : QNames) (c : QConf) (k : Nat) (pr : Loc) (γs : GName) (cb bm ebm : Loc) :
    ⊢@{IProp GF} proxySharedDef γ c k pr -∗ pr.[Proxy, go!"clientBatchStore"] ↦□ cb -∗
      isStoreDef γ γs cb -∗ pr.[Proxy, go!"benchmark"] ↦□ bm -∗
      pr.[Proxy, go!"executedBatches"] ↦□ ebm -∗ usmShared γ γs pr cb bm ebm := by
  iintro #Hsh #Hcb #Hst #Hbm #Hebm
  iunfold proxySharedDef at Hsh
  icases Hsh with ⟨%_hs, %_γs', %_cb', %_bm', %_ebm', #Hfacts, #Hconsts, -, #Hchans, -, -⟩
  iunfold sharedFacts at Hfacts
  icases Hfacts with ⟨-, #Hcons, #Hsmr, -, #Hnil, -⟩
  iunfold sharedConsts at Hconsts
  icases Hconsts with ⟨-, #Hcode, -⟩
  iunfold sharedChans at Hchans
  icases Hchans with ⟨#Hout, #Hfetch, -⟩
  iunfold chanField at Hout Hfetch
  icases Hout with ⟨%och, %γo, #Hoch, #Hobag⟩
  icases Hfetch with ⟨%fch, %γf, #Hfch, #Hfbag⟩
  iunfold usmShared
  iexists fch, och, γf, γo
  unfold isStore
  iframe #

end specs

end Perennial.raxos
