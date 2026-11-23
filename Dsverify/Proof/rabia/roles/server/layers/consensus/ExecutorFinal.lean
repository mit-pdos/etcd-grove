/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/consensus/ExecutorFinal.lean`, run `rabia-r1wake-1`.)

`Consensus.Executor`'s proof: the main loop (`getRequest`, `decideSlot`), never exiting (`Done` is
never closed, nothing is sent on it).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecDecide
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecBefore
public import Dsverify.Proof.rabia.roles.server.layers.consensus.ExecLaws
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.consensus

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.ledger rabia rabia.internal.queue

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable {cf : RCfg}
variable [package_sem : rabia.roles.server.layers.consensus.Assumptions] [π : NetProtoGS] [math.rand.Hyps GF]

/-- `decideSlot`'s spec (ExecDefs' `wp_decideSlot`), as a hypothesis. -/
abbrev decideSlot.spec : Prop :=
  ∀ (γ : Names) (cf : RCfg) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans) (c : Loc)
    (σ : ExSt) (x : ExSlot), k < cf.n →
    (x.pv.phase = 0 ∧ x.pv.round = 1 ∧ x.pv.myBC = [] ∧ x.recv = [] ∧ x.ql = [] ∧
      x.ρs = 0 ∧ x.cur = []) →
    {{ exPre (GF := GF) γ cf ∗ exRun γ cf k γl γc ch c σ x }}
      (App (Val (c @!! go.GoType.PointerType Consensus.ty @!! go!"decideSlot")) (Val #(W32 σ.t)))
    {{ RET #(); ∃ σ', exIdle γ cf k γl γc ch c σ' ∗ ⌜σ'.t = σ.t + 1⌝ }}

/-- A non-blocking receive on `Done` (a bag of `False`s, never closed) never fires. -/
theorem done_nb (γd : ChanNames) (ch : GoChan) (Φ : Unit → Bool → IProp GF) (Q : IProp GF) :
    isChanBag γd ch doneP ⊢ Q -∗ nonblockingRecvAuAlt γd Unit Φ Q := by
  rw [isChanBag_unseal]
  unfold isChanBagDef
  iintro ⟨#Hch, #Hinv⟩ HQ
  unfold nonblockingRecvAuAlt
  iapply ncfupd_of_fupd
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold chanBagInv
  icases Hi with ⟨%st, Hc, Hs⟩
  iexists st
  iframe Hc
  rcases st with (_ | ⟨v, rest⟩) | _ | v | v | _ | _ | (_ | ⟨v, rest⟩)
  all_goals dsimp only [doneP] at *
  case Idle | RcvPending | RcvCommit =>
    iintro Hc
    imod Hmask with -
    imod Hclose $$ [Hc] with -
    · inext; iexists _; iframe Hc
    imodintro
    iexact HQ
  all_goals first
    | (iexfalso; iexact Hs)
    | (iexfalso; icases BigSepL.bigSepL_cons.1 $$ Hs with ⟨Hs, -⟩; iexact Hs)
    | (iintro Hc
       imod Hmask with -
       imod Hclose $$ [Hc Hs] with -
       · inext; iexists _; iframe Hc; iexact Hs
       imodintro
       iexact HQ)

theorem exIdle_ro (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) (σ : ExSt) :
    exIdle (GF := GF) γ cf k γl γc ch c σ ⊢ consRO γ cf k γl γc ch c ∗ exIdle γ cf k γl γc ch c σ := by
  iintro H
  ihave #Hro : consRO γ cf k γl γc ch c $$ [H]
  · unfold exIdle exCommon; icases H with ⟨⟨#Hro, -⟩, -⟩; iexact Hro
  iframe Hro H

theorem exRun_seq (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) (σ : ExSt) (x : ExSlot) :
    exRun (GF := GF) γ cf k γl γc ch c σ x ⊢ ⌜σ.t < lenLedger⌝ ∗
      structFieldRef Consensus go!"SvrSeq" c ↦ (W64 (σ.t : Int) : w64) ∗
      (structFieldRef Consensus go!"SvrSeq" c ↦ (W64 (σ.t : Int) : w64) -∗
        exRun γ cf k γl γc ch c σ x) := by
  unfold exRun
  iintro ⟨Hc, Hcoin, Hseq, %ht, Hs⟩
  iframe Hseq
  isplitr
  · ipureintro; exact ht
  iintro Hseq
  iframe
  ipureintro; exact ht

theorem consExecRes_k (γ : Names) (k : Nat) (γl : SrvNames) (γc : ConsNames) (ch : SrvChans)
    (c : Loc) : consExecRes (GF := GF) γ cf k γl γc ch c ⊢ ⌜k < cf.n⌝ ∗ consExecRes γ cf k γl γc ch c := by
  unfold consExecRes
  iintro ⟨H1, H2, H3, H4, H5, H6, H7, H8, H9, H10, H11, %hk⟩
  iframe
  ipureintro; exact ⟨hk, hk⟩

theorem Consensus.Executor.wp_proof_of (D : ExDeps (GF := GF)) (hDec : decideSlot.spec (GF := GF)) :
    Consensus.Executor.spec (GF := GF) := by
  intro γ cf k γl γc ch c
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  icases consExecRes_k γ k γl γc ch c $$ Hres with ⟨%hk, Hres⟩
  iapply fupd_wp
  imod exIdle_init_proof γ k γl γc ch c $$ Hres with Hidle
  imodintro
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ [Hpkg]
  · iPkgInit
  wp_apply (lc := 4) wp_with_defer as %defer Hdefer
  icases exIdle_ro γ k γl γc ch c _ $$ Hidle with ⟨#Hro, Hidle⟩
  ihave #Hro' := Hro
  iunfold consRO at Hro'
  icases Hro' with ⟨%ledger, %ql, %wg, #HsvrId, #Hwg, #Hdone, #Hn2h, #Hh2n, #Hn2e, #He2n, #Hql,
    #Hledger, #Hqlock, #Hstat, #Hchans, #HledRO, #Hslinv, #HslCh, #Hkeys⟩
  ihave ⟨%ps, #Hcv⟩ := confRO_val $$ Hconf
  ihave Hc2 := Hcv
  iStructNamed Hc2
  ihave #Hch' := Hchans
  iunfold srvChans at Hch'
  icases Hch' with ⟨#HcDone, -, -, -, -, -, -, -⟩
  wp_auto
  wp_apply time.wp_Sleep
  ihave HI : ∃ σ, exIdle γ cf k γl γc ch c σ $$ [Hidle]
  · iexists _; iexact Hidle
  wp_for
  icases HI with ⟨%σ, Hidle⟩
  wp_apply_core (chan.wp_select_nonblocking_alt [iprop(True)] iprop(True))
  isplitr
  · iintro -
    simp only [chan.nonblockingAltClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, ch.done, γl.done
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ HcDone
    iapply done_nb γl.done ch.done _ _ $$ HcDone
    isplit <;> itrivial
  · iapply BigSepL2.bigSepL2_nil.2
    iempintro
  iintro -
  wp_auto
  wp_apply (wp_getRequest_proof D γ k γl γc ch c σ) $$ [Hidle]
  · iframe Hidle; unfold exPre; iframe #
  iintro %b Hb
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte]
    wp_auto
    wp_for_post
    iframe
    iexists σ
    iexact Hb
  · simp only [↓reduceIte]
    icases Hb with ⟨%x, Hrun, %hx⟩
    icases exRun_seq γ k γl γc ch c σ x $$ Hrun with ⟨%ht, Hseq, Hrun⟩
    wp_auto
    have hconv : (W32 (sint.Z (W64 (σ.t : Int))) : w32) = W32 σ.t := by
      unfold lenLedger at ht; word
    rw [hconv]
    ihave Hrun := Hrun $$ Hseq
    wp_apply (hDec γ cf k γl γc ch c σ x hk hx) $$ [Hrun]
    · iframe Hrun; unfold exPre; iframe #
    iintro ⟨%σ', Hidle, -⟩
    wp_auto
    wp_for_post
    iframe
    iexists σ'
    iexact Hidle

/-- `Consensus.Executor.spec`: the main loop with `decideSlot`'s proof (`wp_decideSlot_proof`). -/
theorem Consensus.Executor.wp_proof (D : ExDeps (GF := GF)) : Consensus.Executor.spec (GF := GF) :=
  Consensus.Executor.wp_proof_of D
    (fun γ cf k γl γc ch c σ x hk hx => wp_decideSlot_proof (cf := cf) D γ k γl γc ch c hk σ x hx)

end proof

end Perennial.rabia.roles.server.layers.consensus
