/-
Package `proposer`: `handleProposeRequest`, QuePaxa's proposer loop for one slot.

Each iteration of the loop is at `(S, P)` with `evIn γ (.pstate i me lead S P)`: it sends `P` (or
its variants with random priorities at a propose step, `variants`) to the `c.n` recorders in
parallel (one goroutine each, a `WaitGroup`, the buffered `responses` channel closed after
`wg.Wait()`; in server mode 1 at step 4, a goroutine calls `ESP` with the ids only, then with the
batches if the recorder answers not-found), collects the first `c.n / 2 + 1` replies with a
positive step (a majority, from distinct peers: each goroutine sends at most one reply, with its
peer's token), and takes the next step (`next`, `adopt`) or decides (`fast`, `slow`) through
`cons_step`; with fewer replies (calls failed), it tries the step again.
-/
module

public import Dsverify.Proof.raxos.Proposer.Esp
public import Dsverify.Proof.raxos.Proposer.Conv
public import Dsverify.Proof.raxos.Proposer.Collect
public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open models_lab.pbcodec (PbCodec)
open raxos.replica.src

namespace prop

section propose
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] hyp.qpCodec

variable [gh : hyp.grpc.GrpcHyp qv.grpc] [rh : hyp.RandHyp GF]

/-- What the `responses` channel of an iteration at `(s, P)` for slot `i` carries: the reply of
peer `j < n` (recorder `j + 1`, its token `ts j`), with a positive step, of the recorder's
`record` event for a variant of `P`. -/
def replyP (γ : QNames) (ts : Nat → GName) (n : Nat) (i : Int) (lead : Bool) (s : Int)
    (P : pure.Val) (r : Loc) : IProp GF :=
  iprop(∃ (j : Nat) (v : pure.Val) (st : RecSt), ⌜j < n ∧ 0 < st.S ∧ variants lead s P v⌝ ∗
    token (ts j) ∗ repRR r (DFrac.own 1) (rrOf st) ∗ evIn γ (gotEv i s (j, v, st)))

instance mpmcProducer_timeless (γm : MpmcNames) (s : MSet) :
    Timeless (mpmcProducer (GF := GF) γm s) := by
  unfold mpmcProducer client; infer_instance

theorem repRRProp_persist (l : Loc) (v : pure.Val) :
    ⊢@{IProp GF} repRRProp l (DFrac.own 1) (rrPropOf v) -∗ |==> rpRep l v := by
  iintro H
  unfold repRRProp
  simp only [rrPropOf]
  icases H with ⟨%y, Hy, %Hyf, Hids⟩
  ipersist Hy
  ipersist Hids
  imodintro
  unfold rpRep
  iexists y
  iframe #
  ipureintro; exact Hyf

theorem repRR_persist (r : Loc) (st : RecSt) :
    ⊢@{IProp GF} repRR r (DFrac.own 1) (rrOf st) -∗ |==> ∃ x, r ↦□ x ∗ rrVal x st := by
  iintro H
  unfold repRR
  icases H with ⟨%x, Hx, %Hxf, HF, HM⟩
  simp only [rrOf, repOpt] at *
  imod repRRProp_persist _ _ $$ HF with #HF
  imod repRRProp_persist _ _ $$ HM with #HM
  ipersist Hx
  imodintro
  iexists x
  iframe #
  unfold rrVal
  iframe #
  ipureintro; exact Hxf.1

theorem repliesRep_snoc (rs : List RecorderResponse) (sts : List RecSt) (x : RecorderResponse)
    (st : RecSt) :
    ⊢@{IProp GF} repliesRep rs sts -∗ rrVal x st -∗ repliesRep (rs ++ [x]) (sts ++ [st]) := by
  unfold repliesRep
  iintro ⟨%Hlen, #H⟩ #Hx
  isplitr
  · ipureintro; simp [Hlen]
  iapply BigSepL.bigSepL_snoc.2
  isplitl
  · iapply BigSepL.bigSepL_impl $$ H
    imodintro
    iintro %n %y %Hn ⟨%st', %Hst', Hy⟩
    iexists st'
    iframe Hy
    ipureintro
    have : n < sts.length := by
      rw [← Hlen]; exact (List.getElem?_eq_some_iff.1 Hn).1
    rw [List.getElem?_append_left this]; exact Hst'
  · iexists st
    iframe Hx
    ipureintro
    simp [Hlen]

theorem reg_fit (γ : QNames) (bs : List Batch) (h : ∀ b ∈ bs, batchFit b) :
    ⊢@{IProp GF} ([∗list] b ∈ bs, batchReg γ b.id b) -∗
      [∗list] b ∈ bs, batchReg γ b.id b ∗ ⌜batchFit b⌝ := by
  iintro #H
  iapply BigSepL.bigSepL_impl $$ H
  imodintro
  iintro %n %b %hb #Hb
  iframe #
  ipureintro; exact h b (List.mem_of_getElem? hb)

theorem batchesP_reg (γ : QNames) (vs : List raxos.proto.client.ClientBatch) (bs : List Batch) :
    ⊢@{IProp GF} batchesP γ vs bs -∗ [∗list] b ∈ bs, batchReg γ b.id b := by
  unfold batchesP
  iintro ⟨%Hlen, #H⟩
  iapply (BigSepL.bigSepL_forall_eqv).2
  iintro %n %b %Hb
  have hn : n < vs.length := by
    rw [Hlen.1]; exact (List.getElem?_eq_some_iff.1 Hb).1
  ihave ⟨%b', %Hb', -, #Hr⟩ := BigSepL.bigSepL_lookup (List.getElem?_eq_getElem hn) $$ H
  rw [Hb] at Hb'
  cases Hb'
  iexact Hr


set_option hygiene false in
/-- A loop condition's hypothesis `Hif` as a proposition. -/
macro "if_hyp" : tactic => `(tactic| first
  | exact Hif
  | exact dec_true Hif
  | exact dec_not_true Hif
  | exact dec_not_false Hif
  | (rw [← Hcn.1]; first | exact Hif | exact dec_true Hif | exact dec_not_true Hif)
  | (have h := Hif; rw [Hcn.1] at h; first | exact h | exact dec_true h | exact dec_not_true h))

set_option hygiene false in
/-- The end of an iteration whose replies all have step `S`: `S = S + 1` and the next
`(S, P)` (`Step.next`), with `P` now holding `nv`. -/
macro "ghost_next" nv:term:max hnv:term:max : tactic => `(tactic| (
  imod ghost_stepR γ ⊤ (by simp) c _ (sint.Z msg.instance') (sint.Z Sw) G
    (.pstate (sint.Z msg.instance') k msg.isLeader' (wrapInc (sint.Z Sw)) $nv)
    (fun W ww0 ww1 => by
      have := Step.next (n := c.n) (e := c.ep) _ _ _ _ _ _ ww0 (HR W ww1) hall
      rw [($hnv : _ = _)] at this; exact this)
    (by intros; nofun) (by intros; nofun) $$ Hinv Hconf Hpst HgrecG with #Hpst'))

set_option hygiene false in
macro "finish_next" Pn:term:max nv:term:max : tactic => `(tactic| (
  try wp_auto
  wp_for_post
  rw [← sint_add_one] at *
  iframe
  iexists Sw + W64 1, $Pn, $nv, dsn, []
  iframe
  iframe #
  unfold dsRep
  iexists []
  iframe #
  isplitr
  · iapply repList_nil
  iapply BigSepL.bigSepL_nil.2; iempintro))

set_option hygiene false in
/-- The end of a peer goroutine with its reply `out` (`rr`, its value `xr`): send it on the
`responses` channel if it is not nil and has a positive step, then `wg.Done()`. -/
macro "final_check" : tactic => `(tactic| (
  wp_bind (If (Val _) _ _)
  iapply wp_wand (Φ := fun v => iprop(⌜v = #(decide (out ≠ null ∧ 0 < rr.s))⌝ ∗ out ↦ xr ∗
    resp_ptr ↦ out)) $$ [Hxr resp]
  · by_cases hnull : out = null
    · subst hnull
      wp_auto
      iframe; ipureintro; simp
    · rw [_root_.decide_eq_false hnull]
      wp_auto
      iframe; ipureintro
      rw [Hxrs.1]
      simp [hnull]
  iintro %v ⟨%Hv, Hxr, resp⟩
  subst Hv
  by_cases hc : out ≠ null ∧ 0 < rr.s
  · rw [_root_.decide_eq_true hc]
    icases Hpost with (%Hnf | ⟨%pp, %st, ⟨%Hpp, %Hst⟩, #Hrec⟩)
    · exfalso; subst Hnf; simp [rrNotFound] at hc
    · subst Hst
      simp only [Option.some.injEq] at Hpp
      subst Hpp
      wp_auto
      wp_apply wp_mpmc_send γm rch c.n 1
        (replyP γ ts c.n (sint.Z msg.instance') msg.isLeader' (sint.Z Sw) Pval)
        (fun _ => iprop(True)) UCMRA.unit out $$ [Hprod Htok Hxr HF HM] as Hprod
      · iframe #
        iframe Hprod
        unfold replyP
        iexists (sint.nat n), _, st
        iframe
        isplitr
        · ipureintro
          refine ⟨Hjn, ?_, Hxv⟩
          simpa [rrOf] using hc.2
        isplitl [Hxr HF HM]
        · unfold repRR
          iexists xr
          iframe
          ipureintro; exact Hxrs
        unfold gotEv
        simp only [Prop'.val]
        iframe #
      wp_apply sync.join.WaitGroup.wp_Done iprop(∃ s, mpmcProducer γm s) wg_ptr $$ [Hdone Hprod]
      · iframe
      itrivial
  · rw [_root_.decide_eq_false hc]
    wp_auto
    wp_apply sync.join.WaitGroup.wp_Done iprop(∃ s, mpmcProducer γm s) wg_ptr $$ [Hdone Hprod]
    · iframe
    itrivial))

set_option maxHeartbeats 16000000 in
theorem wp_handleProposeRequest (γ : QNames) (c : QConf) (k : Nat) (p : Loc) (msg : ProposeRequest) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proposerP γ c k p ∗
        proposeReqP γ k msg }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"handleProposeRequest"))
        (Val #msg))
    {{ (r : ProposeResponse), RET #r; proposeRespP γ k r }} := by
  wp_start as ⟨#Hprop, #Hreq⟩
  unfold proposerP
  icases Hprop with ⟨%pv, %γ1, %γ2, %γ4, %γ5, %γ6, #Hp, %Hpv, #Hconf, #Hpeers, -, -, -, -,
    -, #Hinv⟩
  obtain ⟨Hc, Hk1, Hkn, Hnr, Hname, Hhi, Hsm, Hasync⟩ := Hpv
  have Hcn := conf_n_sint c Hc
  have Hmaj := conf_maj_sint c Hc
  have Hcnat : sint.nat (W64 c.n) = c.n := by
    show (sint.Z (W64 c.n)).toNat = c.n; rw [Hcn.1]; simp
  unfold proposeReqP
  icases Hreq with ⟨%ids, %vs, %bs, #Hids, #Hvs, #Hbs, %Hreqf, #Hinit, #Hds⟩
  iStructNamed Hp
  wp_auto
  wp_apply wp_getProposeClientBatches γ p msg.proposalBtch' vs bs $$ [] as %cb ⟨%bps, #Hcb, #Hbps⟩
  · iframe #
  wp_apply wp_extractDecidedSlots γ p _ _ _ $$ [] as %dsl ⟨%ds0, #Hds0⟩
  · iframe #
  ipersist message
  ipersist prop
  iStructNamed message
  -- the start of the slot's proposer: step 4, priority `hi`
  have hi_eq : sint.Z pv.hi' = hi := by rw [Hhi]; rfl
  have name_eq : sint.Z pv.name' = (k : Int) := by
    rw [Hname]
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with
      rfl | rfl | rfl | rfl | rfl <;> rfl
  imod ghost_step1 γ ⊤ (by simp) c (.init (sint.Z msg.instance') k ids msg.isLeader')
    (.pstate (sint.Z msg.instance') k msg.isLeader' 4 ⟨hi, k, sint.Z pv.threadId', ids⟩)
    (fun W h => Step.start _ _ _ _ _ h) (by intros; nofun) (by intros; nofun)
    $$ Hinv Hconf Hinit with #Hpst0
  ihave #Hreg := batchesP_reg γ vs bs $$ Hbs
  ihave #Hbs' := Hbs
  iunfold batchesP at Hbs'
  icases Hbs' with ⟨%Hbfit, -⟩
  ihave #HP0 : propRep γ (ProposerMessage_Proposal.mk zeroValDef 0 slice.nil pv.hi' pv.name'
      pv.threadId' msg.proposalStr' cb) ⟨hi, k, sint.Z pv.threadId', ids⟩ $$ []
  · unfold propRep
    iexists bps, bs
    simp only
    iframe #
    ipureintro
    exact ⟨⟨hi_eq, name_eq, trivial⟩, Hbfit.2⟩
  -- the loop
  ihave HI : (∃ (Sw : w64) (Pv : ProposerMessage_Proposal) (Pval : pure.Val) (dsl' : GoSlice)
      (ds' : List DSlot),
      "S" ∷ S_ptr ↦ Sw ∗ "P" ∷ P_ptr ↦ Pv ∗ "decidedSlots" ∷ decidedSlots_ptr ↦ dsl' ∗
      "#HP" ∷ propRep γ Pv Pval ∗ "#Hdsr" ∷ dsRep γ dsl' ds' ∗
      "#Hpst" ∷ evIn γ (.pstate (sint.Z msg.instance') k msg.isLeader' (sint.Z Sw) Pval) : IProp GF)
      $$ [S P decidedSlots]
  · iexists W64 4, _, ⟨hi, k, sint.Z pv.threadId', ids⟩, dsl, ds0
    rw [show sint.Z (W64 4) = (4 : Int) from rfl]
    iframe
    iframe #
  wp_for HI
  rw [Hnr]
  wp_apply wp_slice_make2 (V := ProposerMessage_Proposal) (W64 c.n) as %Pis ⟨HPis, HPisc⟩
  · ipureintro; rw [Hcn.1]; omega
  rw [Hcnat]
  obtain ⟨Pc, hPc⟩ : ∃ Pc : ProposerMessage_Proposal, Pc = ProposerMessage_Proposal.mk zeroValDef 0
    slice.nil Pv.Priority' Pv.ProposerId' Pv.ThreadId' Pv.Ids' Pv.ClientBatches' := ⟨_, rfl⟩
  ihave HI2 : (∃ (n : w64), "i" ∷ i_ptr ↦ n ∗
      "HPis" ∷ Pis ↦* (List.replicate (sint.nat n) Pc ++
        List.replicate (c.n - sint.nat n) (zero_val ProposerMessage_Proposal)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ c.n⌝ : IProp GF) $$ [i HPis]
  · iexists W64 0
    iframe
    ipureintro; rw [show sint.Z (W64 0) = 0 from rfl]; omega
  wp_for HI2
  wp_pures
  rw [Hcn.1]
  wp_if_destruct
  · have Hlt : sint.Z n < c.n := by if_hyp
    ihave %HPl := ownSlice_len _ _ _ $$ HPis
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, by simp at HPl; word⟩)]
    rw [← hPc]
    wp_apply wp_store_slice_index $$ [$HPis] as HPis
    · ipureintro; simp at HPl ⊢; word
    wp_for_post
    iframe
    iexists n + W64 1
    iframe
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hn2 : (sint.Z n).toNat = sint.nat n := rfl
    rw [Hn1, Hn2, rep_set_step Pc _ _ c.n (by word)]
    iframe
    ipureintro; word
  have Hn3 : sint.nat n = c.n := by
    have : ¬ sint.Z n < c.n := by if_hyp
    have h2 := Hn.2
    word
  rw [Hn3]
  simp only [Nat.sub_self, List.replicate_zero, List.append_nil]
  ihave #HP' := HP
  iunfold propRep at HP'
  icases HP' with ⟨%bpsP, %bsP, %HPf, #HPids, #HPcb, #HPrep, #HPreg, %HPfit⟩
  -- the variants of `P`: random priorities at a propose step after step 4 or for a non-leader
  have HSrem : (BitVec.srem Sw (W64 4) = W64 0) ↔ (sint.Z Sw).tmod 4 = 0 := by
    constructor
    · intro h; have := congrArg BitVec.toInt h; rw [BitVec.toInt_srem] at this; simpa using this
    · intro h; apply BitVec.eq_of_toInt_eq; rw [BitVec.toInt_srem]; simpa using h
  wp_bind (If (Val _) _ _)
  iapply wp_wand (Φ := fun v => iprop(⌜v = #(decide ((sint.Z Sw).tmod 4 = 0 ∧
      (sint.Z Sw > 4 ∨ msg.isLeader' = false)))⌝ ∗ S_ptr ↦ Sw)) $$ [S]
  · by_cases h1 : (sint.Z Sw).tmod 4 = 0
    · rw [_root_.decide_eq_true (HSrem.2 h1)]
      wp_auto
      by_cases h2 : sint.Z Sw > 4
      · rw [_root_.decide_eq_true (show sint.Z (W64 4) < sint.Z Sw from h2)]
        wp_auto
        iframe; ipureintro; simp [h1, h2]
      · rw [_root_.decide_eq_false (show ¬ sint.Z (W64 4) < sint.Z Sw from h2)]
        wp_auto
        cases hl : msg.isLeader'
        · iframe; ipureintro; simp [h1, h2]
        · iframe; ipureintro; simp [h1, h2]
    · rw [_root_.decide_eq_false (fun h => h1 (HSrem.1 h))]
      wp_auto
      iframe; ipureintro; simp [h1]
  iintro %v ⟨%Hv, S⟩
  subst Hv
  wp_bind (If _ _ _)
  iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ xs : List ProposerMessage_Proposal,
      Pis ↦* xs ∗ ⌜xs.length = c.n ∧ ∀ (j : Nat) (x : ProposerMessage_Proposal), xs[j]? = some x →
        x = { Pc with Priority' := x.Priority' } ∧
        variants msg.isLeader' (sint.Z Sw) Pval
          ⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids⟩⌝ ∗ Pi_ptr ↦ Pis)) $$ [HPis Pi]
  · by_cases hr : (sint.Z Sw).tmod 4 = 0 ∧ (sint.Z Sw > 4 ∨ msg.isLeader' = false)
    · rw [_root_.decide_eq_true hr]
      wp_auto
      ihave HI3 : (∃ (n : w64) (xs : List ProposerMessage_Proposal), "i" ∷ i_ptr ↦ n ∗
          "HPis" ∷ Pis ↦* xs ∗
          "%Hxs" ∷ ⌜xs.length = c.n ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ c.n ∧
            ∀ (j : Nat) (x : ProposerMessage_Proposal), xs[j]? = some x →
              x = { Pc with Priority' := x.Priority' } ∧
              (j < sint.nat n → randPrio (sint.Z x.Priority'))⌝ : IProp GF) $$ [i HPis]
      · iexists W64 0, List.replicate c.n Pc
        iframe
        ipureintro
        refine ⟨by simp, by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega,
          fun j x hx => ⟨?_, fun h => absurd h (by simp)⟩⟩
        have : x = Pc := List.eq_of_mem_replicate (List.mem_of_getElem? hx)
        subst this; rw [hPc]
      wp_for HI3
      wp_pures
      rw [Hcn.1]
      wp_if_destruct
      · have Hlt : sint.Z n < c.n := by if_hyp
        rw [Hhi]
        wp_apply hyp.RandHyp.Intn (GF := GF) (W64 100000 - W64 10) (by decide) as %x %Hx
        ihave %HPl := ownSlice_len _ _ _ $$ HPis
        list_elem xs (sint.nat n) as y
        have Hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z Pis.len := ⟨Hxs.2.1, by word⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true Hb)]
        icases ownSlice_elem_acc (sint.Z n) y Pis _ xs Hxs.2.1 Hy_lookup $$ HPis with ⟨Hy, Hback⟩
        wp_auto
        ihave HPis := Hback $$ Hy
        wp_for_post
        iframe
        iexists n + W64 1, _
        iframe
        ipureintro
        have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
        refine ⟨by simp [Hxs.1], by word, by word, fun j z hz => ?_⟩
        rw [Hn1]
        have hnn : (sint.Z n).toNat = sint.nat n := rfl
        rw [hnn, List.getElem?_set] at hz
        by_cases hj : sint.nat n = j
        · subst hj
          have hlen' : sint.nat n < xs.length := by rw [Hxs.1]; word
          simp only [ite_true, hlen'] at hz
          injection hz with hz
          subst hz
          refine ⟨?_, fun _ => ?_⟩
          · have := (Hxs.2.2.2 _ _ Hy_lookup).1
            rw [this]
          · unfold randPrio hi; constructor <;> word
        · simp [hj] at hz
          obtain ⟨h1, h2⟩ := Hxs.2.2.2 _ _ hz
          exact ⟨h1, fun h => h2 (by omega)⟩
      · have Hge : ¬ sint.Z n < c.n := by if_hyp
        have Hn3 : sint.nat n = c.n := by word
        iframe
        ipureintro
        refine ⟨Hxs.1, fun j z hz => ?_⟩
        have hj : j < c.n := by rw [← Hxs.1]; exact (List.getElem?_eq_some_iff.1 hz).1
        obtain ⟨h1, h2⟩ := Hxs.2.2.2 _ _ hz
        refine ⟨h1, ?_⟩
        unfold variants
        rw [if_pos hr]
        exact ⟨h2 (by omega), rfl, rfl, rfl⟩
    · rw [_root_.decide_eq_false hr]
      wp_auto
      isplitr
      · ipureintro; rfl
      iframe
      ipureintro
      refine ⟨by simp, fun j x hx => ⟨?_, ?_⟩⟩
      · have : x = Pc := (List.eq_of_mem_replicate (List.mem_of_getElem? hx))
        subst this; rw [hPc]
      · have : x = Pc := (List.eq_of_mem_replicate (List.mem_of_getElem? hx))
        subst this
        unfold variants
        rw [if_neg hr, hPc]
        simp only
        rw [HPf.1]
  iintro %v ⟨%Hv, %xs, HPis, %Hxs, Pi⟩
  subst Hv
  wp_auto
  wp_apply chan.wp_make2 (V := Loc) (W64 c.n) as %rch %γr ⟨#Hrch, %Hcap, Hroc⟩
  · ipureintro; rw [Hcn.1]; omega
  wp_apply context.wp_Background
  wp_apply context.wp_WithTimeout_Background as %ctx %γctx %cancel %dl ⟨#Hcancel, #Hctx, -⟩
  rw [Hasync]
  wp_auto
  -- the replies' channel (`c.n` producers, 1 consumer), the peers' tokens, the WaitGroup
  imod tokens_alloc c.n with ⟨%ts, Htoks⟩
  have hne0 : ¬ (W64 c.n = W64 0) := by
    intro h; have h2 := Hcn.1; rw [h] at h2
    exact absurd h2 (by rw [show sint.Z (W64 0) = 0 from rfl]; omega)
  rw [if_neg hne0]
  imod start_mpmc rch (replyP γ ts c.n (sint.Z msg.instance') msg.isLeader' (sint.Z Sw) Pval)
    (fun _ => iprop(True)) γr c.n 1 (.Buffered []) trivial (by omega) (by decide)
    $$ Hrch Hroc with ⟨%γm, #Hm, Hprods, Hcons⟩
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ipersist responses
  ipersist ctx
  ipersist cancel
  unfold peersP
  icases Hpeers with ⟨%ps, #Hps, %Hpsl, #Hpsr⟩
  ihave Hwg := sync.join.ownAdder_wand
    iprop([∗list] _x ∈ List.replicate 0 (), ∃ s, mpmcProducer γm s) wg_ptr (W32 0) iprop(True)
    $$ [] Hwg
  · iintro -; simp only [List.replicate_zero]; iapply BigSepL.bigSepL_nil.2; iempintro
  ihave HI4 : (∃ (n : w64) (na : w32), "i" ∷ i_ptr ↦ n ∗
      "Hwg" ∷ sync.join.ownAdder wg_ptr na
        iprop([∗list] _x ∈ List.replicate (sint.nat n) (), ∃ s, mpmcProducer γm s) ∗
      "Hprods" ∷ ([∗list] Q ∈ List.replicate (c.n - sint.nat n) (mpmcProducer γm UCMRA.unit), Q) ∗
      "Htoks" ∷ ([∗list] j ∈ List.range' (sint.nat n) (c.n - sint.nat n), token (ts j)) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ c.n ∧ sint.Z na = sint.Z n⌝ : IProp GF)
      $$ [i Hwg Hprods Htoks]
  · iexists W64 0, W32 0
    simp only [show sint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
    iframe
    ipureintro; rw [show sint.Z (W64 0) = 0 from rfl]; exact ⟨by omega, by omega, rfl⟩
  wp_for HI4
  wp_pures
  rw [Hcn.1]
  wp_if_destruct
  · have Hlt : sint.Z n < c.n := by if_hyp
    wp_apply +noauto sync.join.WaitGroup.wp_Add iprop(∃ s, mpmcProducer γm s) wg_ptr _ na $$ [Hwg]
      as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    have Hm3 : c.n - sint.nat n = (c.n - 1 - sint.nat n) + 1 := by word
    rw [Hm3]
    simp only [List.replicate_succ, List.range'_succ]
    icases BigSepL.bigSepL_cons.1 $$ Hprods with ⟨Hprod, Hprods⟩
    icases BigSepL.bigSepL_cons.1 $$ Htoks with ⟨Htok, Htoks⟩
    list_elem ps (sint.nat n) as pr
    list_elem xs (sint.nat n) as x
    ihave %Hpsl' := ownSlice_len _ _ _ $$ Hps
    ihave %Hxsl' := ownSlice_len _ _ _ $$ HPis
    wp_auto
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, by word⟩)]
    wp_apply wp_load_slice_index _ (sint.Z n) ps _ pr Hn.1 $$ [Hps] as -
    · iframe #; ipureintro; exact Hpr_lookup
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hn.1, by word⟩)]
    wp_apply wp_load_slice_index _ (sint.Z n) xs _ x Hn.1 $$ [HPis] as HPis
    · iframe; ipureintro; exact Hx_lookup
    ihave ⟨%Hprn, %lc, %cc, %Hprc, #Hlc, #Hcc⟩ :=
      BigSepL.bigSepL_lookup (Φ := fun j p => iprop(⌜sint.Z p.name' = j + 1⌝ ∗
        ∃ (l cc : Loc), ⌜p.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
          l ↦□ (consensusClient.mk
            (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
          qv.grpc.isClientConn cc (world γ) (recAddr (j + 1)))) Hpr_lookup $$ Hpsr
    obtain ⟨Hxeq, Hxv⟩ := Hxs.2 _ _ Hx_lookup
    have Hr : 1 ≤ sint.nat n + 1 ∧ sint.nat n + 1 ≤ 5 := by word
    have Hjn : sint.nat n < c.n := by word
    wp_apply wp_fork $$ [Hdone Hprod Htok]
    · wp_pures
      wp_apply wp_with_defer as %defer Hdefer
      wp_bind (If (Val _) _ _)
      iapply wp_wand (Φ := fun v => iprop(⌜v = #(decide (Sw = W64 4 ∧ c.se = 1))⌝)) $$ []
      · by_cases hS4 : Sw = W64 4
        · rw [_root_.decide_eq_true hS4]
          wp_auto
          rw [Hsm]
          ipureintro
          rcases (show c.se = 0 ∨ c.se = 1 by have := Hc.2.1; omega) with h | h <;>
            rw [h] <;> simp [hS4] <;> decide
        · rw [_root_.decide_eq_false hS4]
          wp_auto
          ipureintro; rw [_root_.decide_eq_false (fun h : Sw = W64 4 ∧ c.se = 1 => hS4 h.1)]
      iintro %v %Hv
      subst Hv
      -- the send event, the request's facts
      imod ghost_step1 γ ⊤ (by simp) c (.pstate (sint.Z msg.instance') k msg.isLeader' (sint.Z Sw) Pval)
        (.send (sint.Z msg.instance') k (sint.Z Sw) ⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids⟩)
        (fun W h => Step.send _ _ _ _ _ _ h Hxv) (by intros; nofun) (by intros; nofun)
        $$ Hinv Hconf Hpst with #Hsend
      iunfold dsRep at Hdsr
      icases Hdsr with ⟨%sps, #Hsps, #Hspsr, #Hdec⟩
      ihave #HPrf := reg_fit γ bsP HPfit $$ HPreg
      by_cases hm1 : Sw = W64 4 ∧ c.se = 1
      · rw [_root_.decide_eq_true hm1]
        wp_auto
        -- server mode 1 at step 4: the ids only first
        wp_apply wp_slice_make2 (V := Loc) (W64 0) as %cb0 ⟨Hcb0, -⟩
        · ipureintro; decide
        simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
        ipersist Hcb0
        try wp_auto
        ipersist «$r0»
        ipersist «$a1»
        ihave #Hpr1 : repProp «$r0_ptr» .discard
            (⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids, []⟩ : Prop') $$ []
        · unfold repProp
          iexists (ProposerMessage_Proposal.mk zeroValDef 0 slice.nil x.Priority' x.ProposerId'
            x.ThreadId' x.Ids' cb0), []
          iframe #
          rw [Hxeq]
          simp only
          rw [hPc]
          simp only
          iframe #
          isplitr
          · ipureintro
            exact ⟨trivial, HPf.2.1, HPf.2.2⟩
          iapply repList_nil
        ihave Hreq1 : repPM «$a1_ptr» .discard ⟨sint.Z pv.name', sint.Z msg.instance',
            some ⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids, []⟩, sint.Z Sw, ds'⟩ $$ []
        · unfold repPM
          iexists (ProposerMessage.mk zeroValDef 0 slice.nil pv.name' msg.instance' «$r0_ptr» Sw
            dsl'), sps
          dsimp only
          iframe #
          ipureintro; exact ⟨rfl, rfl, rfl⟩
        rw [Hprc]
        wp_auto
        wp_apply wp_ESP γ (sint.nat n + 1) lc cc ctx _ «$a1_ptr» .discard _ slice.nil $$ [Hreq1]
          as %out %err Hres
        · iframe #
          isplitr
          · ipureintro; exact Hr
          iframe
          iintro -
          unfold pmFacts
          iexists _, k
          isplitr
          · ipureintro; rfl
          simp only [Prop'.val]
          iframe #
          try (iapply BigSepL.bigSepL_nil.2; iempintro)
        icases Hres with (⟨%Herr, %rr, Hrr, Hpost⟩ | ⟨%Herr, %Hnull⟩)
        · subst Herr
          iunfold espPost at Hpost
          icases Hpost with ⟨%Hrrok, Hpost⟩
          iunfold repRR at Hrr
          icases Hrr with ⟨%xr, Hxr, %Hxrs, HF, HM⟩
          wp_auto
          rw [Hxrs.2]
          cases hnf : rr.notFound
          · -- found: the reply of the ids-only call
            wp_auto
            final_check
          · -- not found (step 0): again, with the batches
            icases Hpost with (%Hnf | ⟨%pp, %st, ⟨%Hpp, %Hst⟩, #Hrec⟩)
            rotate_left
            · exfalso; subst Hst; simp [rrOf] at hnf
            iclear Hxr HF HM «$r0» «$a1» Hpr1
            wp_auto
            ipersist «$r0»
            ipersist «$a1»
            ihave #Hpr2 : repProp «$r0_ptr» .discard
                (⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids, bsP⟩ : Prop') $$ []
            · unfold repProp
              iexists (ProposerMessage_Proposal.mk zeroValDef 0 slice.nil x.Priority' x.ProposerId'
                x.ThreadId' x.Ids' x.ClientBatches'), bpsP
              iframe #
              rw [Hxeq]
              simp only
              rw [hPc]
              simp only
              iframe #
              ipureintro
              exact ⟨trivial, HPf.2.1, HPf.2.2⟩
            ihave #Hnil := ownSlice_nil (V := Loc) (GF := GF) DFrac.discard
            ihave Hreq2 : repPM «$a1_ptr» .discard ⟨sint.Z pv.name', sint.Z msg.instance',
                some ⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids, bsP⟩, sint.Z Sw, []⟩ $$ []
            · unfold repPM
              iexists (ProposerMessage.mk zeroValDef 0 slice.nil pv.name' msg.instance' «$r0_ptr» Sw
                slice.nil), []
              dsimp only
              iframe #
              isplitr
              · ipureintro; exact ⟨rfl, rfl, rfl⟩
              iapply repList_nil
            rw [Hprc]
            wp_auto
            wp_apply wp_ESP γ (sint.nat n + 1) lc cc ctx _ «$a1_ptr» .discard _ slice.nil $$ [Hreq2]
              as %out %err Hres
            · iframe #
              isplitr
              · ipureintro; exact Hr
              iframe
              iintro -
              unfold pmFacts
              iexists _, k
              isplitr
              · ipureintro; rfl
              simp only [Prop'.val]
              iframe #
              try (iapply BigSepL.bigSepL_nil.2; iempintro)
            icases Hres with (⟨%Herr, %rr, Hrr, Hpost⟩ | ⟨%Herr, %Hnull⟩)
            · subst Herr
              iunfold espPost at Hpost
              icases Hpost with ⟨%Hrrok2, Hpost⟩
              iunfold repRR at Hrr
              icases Hrr with ⟨%xr, Hxr, %Hxrs, HF, HM⟩
              wp_auto
              final_check
            · subst Hnull
              wp_auto
              wp_apply sync.join.WaitGroup.wp_Done iprop(∃ s, mpmcProducer γm s) wg_ptr $$ [Hdone Hprod]
              · iframe
              itrivial
        · rcases err with e | _
          · wp_auto
            wp_apply sync.join.WaitGroup.wp_Done iprop(∃ s, mpmcProducer γm s) wg_ptr $$ [Hdone Hprod]
            · iframe
            itrivial
          · exact absurd rfl Herr
      rw [_root_.decide_eq_false hm1]
      wp_auto
      ipersist pi
      ipersist «$a1»
      ihave #Hpr : repProp pi_ptr .discard
          (⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids, bsP⟩ : Prop') $$ []
      · unfold repProp
        iexists x, bpsP
        iframe #
        rw [Hxeq]
        simp only
        rw [hPc]
        simp only
        iframe #
        ipureintro
        exact ⟨trivial, HPf.2.1, HPf.2.2⟩
      ihave Hreq : repPM «$a1_ptr» .discard ⟨sint.Z pv.name', sint.Z msg.instance',
          some ⟨sint.Z x.Priority', Pval.pid, Pval.tid, Pval.ids, bsP⟩, sint.Z Sw, ds'⟩ $$ []
      · unfold repPM
        iexists (ProposerMessage.mk zeroValDef 0 slice.nil pv.name' msg.instance' pi_ptr Sw dsl'), sps
        dsimp only
        iframe #
        ipureintro; exact ⟨rfl, rfl, rfl⟩
      rw [Hprc]
      wp_auto
      wp_apply wp_ESP γ (sint.nat n + 1) lc cc ctx _ «$a1_ptr» .discard _ slice.nil $$ [Hreq]
        as %out %err Hres
      · iframe #
        isplitr
        · ipureintro; exact Hr
        iframe
        iintro -
        unfold pmFacts
        iexists _, k
        isplitr
        · ipureintro; rfl
        iframe #
        simp only [Prop'.val]
        iframe #
      icases Hres with (⟨%Herr, %rr, Hrr, Hpost⟩ | ⟨%Herr, %Hnull⟩)
      · subst Herr
        iunfold espPost at Hpost
        icases Hpost with ⟨%Hrrok, Hpost⟩
        wp_auto
        iunfold repRR at Hrr
        icases Hrr with ⟨%xr, Hxr, %Hxrs, HF, HM⟩
        final_check
      · rcases err with e | _
        · wp_auto
          wp_apply sync.join.WaitGroup.wp_Done iprop(∃ s, mpmcProducer γm s) wg_ptr $$ [Hdone Hprod]
          · iframe
          itrivial
        · exact absurd rfl Herr
    wp_for_post
    iframe
    iexists n + W64 1, na + W32 1
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hn2 : c.n - (sint.nat n + 1) = c.n - 1 - sint.nat n := by omega
    rw [Hn1, Hn2]
    iframe
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro ⟨H1, H2⟩
      rw [List.replicate_succ']
      iapply BigSepL.bigSepL_snoc.2
      iframe
    ipureintro; word
  have Hn3 : sint.nat n = c.n := by
    have : ¬ sint.Z n < c.n := by if_hyp
    word
  rw [Hn3]
  simp only [Nat.sub_self, List.replicate_zero, List.range'_zero]
  wp_apply wp_slice_make2 (V := Loc) (W64 0) as %dsn ⟨Hdsn, -⟩
  · ipureintro; decide
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist Hdsn
  wp_apply wp_fork $$ [Hwg]
  · wp_auto
    wp_apply sync.join.WaitGroup.wp_Wait
      iprop([∗list] _x ∈ List.replicate c.n (), ∃ s, mpmcProducer γm s) na wg_ptr $$ [$Hwg]
      as ⟨>HP, -⟩
    ihave ⟨%ss, %Hss, Hss⟩ := producers_collect γm c.n $$ HP
    wp_apply Hcancel
    wp_apply wp_mpmc_close γm rch c.n 1
      (replyP γ ts c.n (sint.Z msg.instance') msg.isLeader' (sint.Z Sw) Pval)
      (fun _ => iprop(True)) ss Hss $$ [Hss]
    · iframe #
      iframe
    itrivial
  -- collecting a majority of replies
  wp_apply wp_slice_make2 (V := RecorderResponse) (W64 0) as %ra0 ⟨Hra0, Hra0c⟩
  · ipureintro; decide
  simp only [show sint.nat (W64 0) = 0 from rfl, List.replicate_zero]
  ipersist Hra0
  rw [show List.replicate 1 (mpmcConsumer (GF := GF) γm UCMRA.unit) =
    [mpmcConsumer γm UCMRA.unit] from rfl]
  icases BigSepL.bigSepL_cons.1 $$ Hcons with ⟨Hcons, -⟩
  ihave HI5 : (∃ (sl : GoSlice) (rs : List RecorderResponse) (recv : MSet)
      (got : List Got) (rv : Loc),
      "responsesArray" ∷ responsesArray_ptr ↦ sl ∗ "#Hsl" ∷ sl ↦*□ rs ∗
      "Hslc" ∷ ownSliceCap RecorderResponse sl (DFrac.own 1) ∗
      "Hcons" ∷ mpmcConsumer γm recv ∗ "r" ∷ r_ptr ↦ rv ∗
      "Hgtok" ∷ ([∗list] g ∈ got, token (ts g.1)) ∗
      "#Hgrec" ∷ ([∗list] g ∈ got, evIn γ (gotEv (sint.Z msg.instance') (sint.Z Sw) g)) ∗
      "#Hrep" ∷ repliesRep rs (got.map (fun g => g.2.2)) ∗
      "%Hgot" ∷ ⌜got.length < c.n / 2 + 1 ∧ (got.map Prod.fst).Nodup ∧ ∀ g ∈ got, g.1 < c.n ∧
        0 < g.2.2.S ∧ variants msg.isLeader' (sint.Z Sw) Pval g.2.1⌝ : IProp GF)
      $$ [responsesArray Hra0c Hcons r]
  · iexists ra0, [], UCMRA.unit, [], _
    iframe
    iframe #
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · unfold repliesRep
      isplitr
      · ipureintro; rfl
      iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HI5
  wp_apply wp_mpmc_receive γm rch c.n 1
    (replyP γ ts c.n (sint.Z msg.instance') msg.isLeader' (sint.Z Sw) Pval)
    (fun _ => iprop(True)) recv $$ [Hcons] as %rp %ok Hrcv
  · iframe #; iframe
  cases ok
  · -- the channel is closed: fewer than a majority of replies
    simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hrcv with ⟨#Hclosed, Hcons, %Hrp⟩
    wp_auto
    wp_for_post
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
    ihave %Hrsl := repliesRep_length _ _ $$ Hrep
    simp only [List.length_map] at Hrsl
    have Hsz : sint.Z sl.len = got.length :=
      sint_of_nat _ _ (by rw [← Hrsl]; exact Hsll.1) Hsll.2
    rw [Hmaj.1]
    rw [_root_.decide_eq_true (show sint.Z sl.len < sint.Z (W64 ((c.n / 2 + 1 : Nat) : Int)) by
      rw [Hmaj.2.1, Hsz]; have := Hgot.1; omega)]
    wp_auto
    wp_for_post
    iframe
    iexists Sw, Pv, Pval, dsn, []
    iframe
    iframe #
    unfold dsRep
    iexists []
    iframe #
    isplitr
    · iapply repList_nil
    iapply BigSepL.bigSepL_nil.2; iempintro
  · simp only [↓reduceIte]
    icases Hrcv with ⟨Hrp, Hcons⟩
    unfold replyP
    icases Hrp with ⟨%j, %v, %st, %Hjv, Htok, Hrr, #Hrec⟩
    imod repRR_persist _ _ $$ Hrr with ⟨%xr, #Hxr, #Hxrv⟩
    wp_auto
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := RecorderResponse) [xr]
    wp_auto
    rw [show go.arrayLiteralSize [KeyedElement none
      (ElementExpression RecorderResponse.ty #xr)] = 1 from rfl]
    isplitr
    · ipureintro; rfl
    iintro %sp ⟨Hsp, -⟩
    wp_apply wp_slice_append_persistent (V := RecorderResponse) sl rs _ [xr] (DFrac.own 1)
      $$ [$Hsl $Hslc Hsp] as %sl' ⟨#Hsl', Hslc', -⟩
    · iexact Hsp
    ihave %Hsll := ownSlice_len _ _ _ $$ Hsl'
    ihave %Hrsl := repliesRep_length _ _ $$ Hrep
    simp only [List.length_map, List.length_append, List.length_singleton] at Hrsl Hsll
    have Hsz : sint.Z sl'.len = got.length + 1 := by
      have := sint_of_nat _ _ Hsll.1 Hsll.2
      rw [this, Hrsl]; push_cast; rfl
    ihave ⟨%Hjf, Hgtok⟩ := tok_fresh ts got (j, v, st) $$ Hgtok Htok
    rw [Hmaj.1]
    by_cases h2 : got.length + 1 = c.n / 2 + 1
    · have Hsl'eq : sl'.len = W64 ((c.n / 2 + 1 : Nat) : Int) :=
        w64_of_sint _ _ (by omega) (by rw [Hsz]; omega)
      rw [_root_.decide_eq_true Hsl'eq]
      wp_auto
      rw [Hmaj.1]
      rw [_root_.decide_eq_true Hsl'eq]
      wp_auto
      wp_for_post
      rw [Hmaj.1]
      rw [_root_.decide_eq_false (show ¬ sint.Z sl'.len < sint.Z (W64 ((c.n / 2 + 1 : Nat) : Int)) by
        rw [Hmaj.2.1, Hsz]; omega)]
      wp_auto
      -- a majority of replies, from distinct peers
      obtain ⟨G, hG⟩ : ∃ G : List Got, G = got ++ [(j, v, st)] := ⟨_, rfl⟩
      obtain ⟨R, hR⟩ : ∃ R : List RecorderResponse, R = rs ++ [xr] := ⟨_, rfl⟩
      obtain ⟨sts, hsts⟩ : ∃ sts : List RecSt, sts = G.map (fun g => g.2.2) := ⟨_, rfl⟩
      have HGlen : G.length = c.n / 2 + 1 := by rw [hG]; simp; omega
      have HGnd : (G.map Prod.fst).Nodup := by
        rw [hG, List.map_append, List.nodup_append]
        refine ⟨Hgot.2.1, by simp, ?_⟩
        intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact Hjf ha
      have HGall : ∀ g ∈ G, g.1 < c.n ∧ 0 < g.2.2.S ∧
          variants msg.isLeader' (sint.Z Sw) Pval g.2.1 := by
        intro g hg; rw [hG] at hg
        rcases List.mem_append.1 hg with hg | hg
        · exact Hgot.2.2 g hg
        · simp at hg; subst hg; exact Hjv
      have HR : ∀ W : World, (∀ g ∈ G, gotEv (sint.Z msg.instance') (sint.Z Sw) g ∈ W) →
          Replies c.n W (sint.Z msg.instance') msg.isLeader' (sint.Z Sw) Pval sts := by
        intro W hW; rw [hsts]; exact replies_got c.n W _ _ _ _ G HGlen HGnd HGall hW
      ihave #HgrecG : [∗list] g ∈ G, evIn γ (gotEv (sint.Z msg.instance') (sint.Z Sw) g) $$ []
      · rw [hG]
        iapply BigSepL.bigSepL_snoc.2
        iframe #
      ihave #HrepG : repliesRep R sts $$ []
      · rw [hR, hsts, hG]
        simp only [List.map_append, List.map_cons, List.map_nil]
        iapply repliesRep_snoc $$ Hrep Hxrv
      rw [← hR]
      have HRlen : R.length = c.n / 2 + 1 := by rw [hR]; simp; omega
      have Hstslen : sts.length = c.n / 2 + 1 := by rw [hsts]; simp [HGlen]
      have HszR : sint.Z sl'.len = R.length := by rw [Hsz, HRlen]; omega
      have Hne : sts ≠ [] := by intro h; rw [h] at Hstslen; simp at Hstslen
      iclear Hgtok
      -- do all replies have step `S`?
      wp_bind (App (App (App (Val doFor) _) _) _)
      iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ (∃ i : w64, i_ptr ↦ i) ∗
          allRepliesHaveS_ptr ↦ decide (∀ st' ∈ sts, st'.S = sint.Z Sw) ∗
          responsesArray_ptr ↦ sl' ∗ S_ptr ↦ Sw)) $$ [i allRepliesHaveS responsesArray S]
      · ihave HI6 : (∃ (i : w64) (b : Bool), "i" ∷ i_ptr ↦ i ∗ "allS" ∷ allRepliesHaveS_ptr ↦ b ∗
            "%Hi6" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ R.length ∧ b = true ∧
              ∀ m st', m < sint.nat i → sts[m]? = some st' → st'.S = sint.Z Sw⌝ : IProp GF)
            $$ [i allRepliesHaveS]
        · iexists W64 0, true
          iframe
          ipureintro
          refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, rfl,
            fun m st' hm _ => absurd hm (by simp)⟩
        wp_for HI6
        by_cases hi2 : sint.Z i < sint.Z sl'.len
        · rw [_root_.decide_eq_true hi2]
          simp only [_root_.decide_true, ↓reduceIte]
          have hb1 : sint.nat i < R.length := by word
          have hb2 : sint.nat i < sts.length := by word
          list_elem R (sint.nat i) as y
          list_elem sts (sint.nat i) as sty
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi6.1, hi2⟩)]
          icases ownSlice_elem_acc (sint.Z i) y sl' _ _ Hi6.1 Hy_lookup $$ Hsl' with ⟨Hy, -⟩
          iStructNamed Hy
          wp_auto
          ihave #Hyv := repliesRep_lookup R sts _ y sty Hy_lookup Hsty_lookup $$ HrepG
          iunfold rrVal at Hyv
          icases Hyv with ⟨%Hyst, -, -⟩
          by_cases hyS : y.S' = Sw
          · rw [_root_.decide_eq_true hyS]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, b
            iframe
            ipureintro
            refine ⟨by word, by word, Hi6.2.2.1, fun m st' hm hst' => ?_⟩
            have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
            rw [Hi1] at hm
            by_cases hmi : m < sint.nat i
            · exact Hi6.2.2.2 m st' hmi hst'
            · have : m = sint.nat i := by omega
              subst this
              rw [Hsty_lookup] at hst'; cases hst'
              rw [← Hyst, hyS]
          · rw [_root_.decide_eq_false hyS]
            wp_auto
            wp_for_post
            iframe
            isplitr
            · ipureintro; rfl
            rw [_root_.decide_eq_false]
            · iframe
            intro hall
            apply hyS
            have := hall sty (List.mem_of_getElem? Hsty_lookup)
            rw [this] at Hyst
            exact BitVec.eq_of_toInt_eq Hyst
        · rw [_root_.decide_eq_false hi2]
          simp only [intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte]
          obtain ⟨h0, h1, hb, h3⟩ := Hi6
          subst hb
          have hall : ∀ st' ∈ sts, st'.S = sint.Z Sw := by
            intro st' hst'
            obtain ⟨m, hm⟩ := List.getElem?_of_mem hst'
            have hm2 : m < sts.length := (List.getElem?_eq_some_iff.1 hm).1
            exact h3 m st' (by word) hm
          rw [_root_.decide_eq_true hall]
          iframe
      iintro %v ⟨%Hv, ⟨%iv, i⟩, allRepliesHaveS, responsesArray, S⟩
      subst Hv
      by_cases hall : ∀ st' ∈ sts, st'.S = sint.Z Sw
      · rw [_root_.decide_eq_true hall]
        wp_auto
        by_cases h0 : (sint.Z Sw).tmod 4 = 0
        · rw [_root_.decide_eq_true ((srem4_eq Sw 0 (by decide)).2 h0)]
          wp_auto
          rw [Hhi]
          wp_bind (App (App (App (Val doFor) _) _) _)
          iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ (∃ i : w64, i_ptr ↦ i) ∗
              allRepliesHaveFHiFit_ptr ↦ decide (∀ st' ∈ sts, st'.F.prio = hi) ∗
              responsesArray_ptr ↦ sl')) $$ [i allRepliesHaveFHiFit responsesArray]
          · ihave HI8 : (∃ (i : w64) (b : Bool), "i" ∷ i_ptr ↦ i ∗
                "allF" ∷ allRepliesHaveFHiFit_ptr ↦ b ∗
                "%Hi8" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ R.length ∧ b = true ∧
                  ∀ m st', m < sint.nat i → sts[m]? = some st' → st'.F.prio = hi⌝ : IProp GF)
                $$ [i allRepliesHaveFHiFit]
            · iexists W64 0, true
              iframe
              ipureintro
              refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, rfl,
                fun m st' hm _ => absurd hm (by simp)⟩
            wp_for HI8
            by_cases hi2 : sint.Z i < sint.Z sl'.len
            · rw [_root_.decide_eq_true hi2]
              have hb1 : sint.nat i < R.length := by word
              have hb2 : sint.nat i < sts.length := by word
              list_elem R (sint.nat i) as y
              list_elem sts (sint.nat i) as sty
              simp only [_root_.decide_true, ↓reduceIte]
              wp_auto
              have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl'.len := ⟨Hi8.1, hi2⟩
              rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
              icases ownSlice_elem_acc (sint.Z i) y sl' _ _ Hi8.1 Hy_lookup $$ Hsl' with ⟨Hy, -⟩
              iStructNamed Hy
              ihave #Hyv := repliesRep_lookup R sts _ y sty Hy_lookup Hsty_lookup $$ HrepG
              iunfold rrVal at Hyv
              icases Hyv with ⟨-, #HyF, -⟩
              iunfold rpRep at HyF
              icases HyF with ⟨%fz, #Hfz, %Hfzf, #Hfzids⟩
              iStructNamed Hfz
              wp_auto
              have Hpe : (fz.Priority' = W64 100000) ↔ sty.F.prio = hi := by
                rw [← Hfzf.1]; unfold hi; constructor
                · intro h; rw [h]; rfl
                · intro h; word
              by_cases hyF : fz.Priority' = W64 100000
              · rw [_root_.decide_eq_true hyF]
                wp_auto
                wp_for_post
                iframe
                iexists i + W64 1, b
                iframe
                ipureintro
                refine ⟨by word, by word, Hi8.2.2.1, fun m st' hm hst' => ?_⟩
                have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
                rw [Hi1] at hm
                by_cases hmi : m < sint.nat i
                · exact Hi8.2.2.2 m st' hmi hst'
                · have : m = sint.nat i := by omega
                  subst this
                  rw [Hsty_lookup] at hst'; cases hst'
                  exact Hpe.1 hyF
              · rw [_root_.decide_eq_false hyF]
                wp_auto
                wp_for_post
                iframe
                isplitr
                · ipureintro; rfl
                rw [_root_.decide_eq_false]
                · iframe
                intro hall'
                exact hyF (Hpe.2 (hall' sty (List.mem_of_getElem? Hsty_lookup)))
            · rw [_root_.decide_eq_false hi2]
              simp only [intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte,
                _root_.decide_true]
              obtain ⟨h0', h1', hb, h3'⟩ := Hi8
              subst hb
              have hallF : ∀ st' ∈ sts, st'.F.prio = hi := by
                intro st' hst'
                obtain ⟨m, hm⟩ := List.getElem?_of_mem hst'
                have hm2 : m < sts.length := (List.getElem?_eq_some_iff.1 hm).1
                exact h3' m st' (by word) hm
              rw [_root_.decide_eq_true hallF]
              iframe
          iintro %v ⟨%Hv, ⟨%iv, i⟩, allRepliesHaveFHiFit, responsesArray⟩
          subst Hv
          by_cases hallF : ∀ st' ∈ sts, st'.F.prio = hi
          · obtain ⟨x0, hx0⟩ : ∃ x0, R[0]? = some x0 :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            obtain ⟨st0, hst0⟩ : ∃ st0, sts[0]? = some st0 :=
              ⟨_, List.getElem?_eq_getElem (by omega)⟩
            imod ghost_stepR γ ⊤ (by simp) c _ (sint.Z msg.instance') (sint.Z Sw) G
              (.decide (sint.Z msg.instance') st0.F.ids)
              (fun W w0 w1 => Step.fast _ _ _ _ _ _ st0 w0 (HR W w1) h0
                (fun st' h => ⟨hall st' h, hallF st' h⟩) (by rw [List.head?_eq_getElem?]; exact hst0))
              (by intros; nofun) (by intros; nofun) $$ Hinv Hconf Hpst HgrecG with #Hdec
            rw [_root_.decide_eq_true hallF]
            wp_auto
            have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z sl'.len := ⟨by decide, by
              rw [HszR, HRlen, show sint.Z (W64 0) = 0 from rfl]; omega⟩
            rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
            icases ownSlice_elem_acc (sint.Z (W64 0)) x0 sl' _ _ (by decide) hx0 $$ Hsl' with ⟨Hy, -⟩
            iStructNamed Hy
            ihave #Hx0v := repliesRep_lookup R sts 0 x0 st0 hx0 hst0 $$ HrepG
            iunfold rrVal at Hx0v
            icases Hx0v with ⟨-, #HyF, -⟩
            iunfold rpRep at HyF
            icases HyF with ⟨%fz, #Hfz, %Hfzf, #Hfzids⟩
            iStructNamed Hfz
            repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] | wp_auto)
            wp_for_post
            iapply HΦ
            unfold proposeRespP
            iexists st0.F.ids, ids
            dsimp only
            iframe #
            unfold decided; iexact Hdec
          · rw [_root_.decide_eq_false hallF]
            ghost_next (maxOf RecSt.F sts) (show (if (sint.Z Sw).tmod 4 = 0 then
              maxOf RecSt.F sts else if (sint.Z Sw).tmod 4 = 3 then maxOf RecSt.M sts
              else Pval) = maxOf RecSt.F sts by rw [if_pos h0])
            wp_auto
            wp_apply wp_getMaxFromResponses_F γ p sl' R sts Hne $$ [] as %pr ⟨%Hprn, #Hpr⟩
            · iframe #
            finish_next pr (maxOf RecSt.F sts)
        rw [_root_.decide_eq_false (fun h => h0 ((srem4_eq Sw 0 (by decide)).1 h))]
        wp_auto
        by_cases h2 : (sint.Z Sw).tmod 4 = 2
        · rw [_root_.decide_eq_true ((srem4_eq Sw 2 (by decide)).2 h2)]
          wp_auto
          wp_apply wp_getMaxFromResponses_M γ p sl' R sts Hne $$ [] as %pr ⟨%Hprn, #Hpr⟩
          · iframe #
          wp_apply wp_isEqualProposal γ p Pv pr Pval (maxOf RecSt.M sts) $$ [] as %b %Hb
          · iframe #
            ipureintro; exact Hprn
          cases b
          · have h3 : ¬ (sint.Z Sw).tmod 4 = 3 := by omega
            ghost_next Pval (show (if (sint.Z Sw).tmod 4 = 0 then
              maxOf RecSt.F sts else if (sint.Z Sw).tmod 4 = 3 then maxOf RecSt.M sts
              else Pval) = Pval by rw [if_neg h0, if_neg h3])
            finish_next Pv Pval
          · have Htag := Hb rfl
            imod ghost_stepR γ ⊤ (by simp) c _ (sint.Z msg.instance') (sint.Z Sw) G
              (.decide (sint.Z msg.instance') Pval.ids)
              (fun W w0 w1 => Step.slow _ _ _ _ _ _ w0 (HR W w1) h2 hall
                ⟨Htag.1.symm, Htag.2.1.symm, Htag.2.2.symm⟩)
              (by intros; nofun) (by intros; nofun) $$ Hinv Hconf Hpst HgrecG with #Hdec
            wp_auto
            wp_for_post
            iapply HΦ
            unfold proposeRespP
            iexists Pval.ids, ids
            dsimp only
            iframe #
            unfold decided; iexact Hdec
        rw [_root_.decide_eq_false (fun h => h2 ((srem4_eq Sw 2 (by decide)).1 h))]
        wp_auto
        by_cases h3 : (sint.Z Sw).tmod 4 = 3
        · rw [_root_.decide_eq_true ((srem4_eq Sw 3 (by decide)).2 h3)]
          ghost_next (maxOf RecSt.M sts) (show (if (sint.Z Sw).tmod 4 = 0 then
            maxOf RecSt.F sts else if (sint.Z Sw).tmod 4 = 3 then maxOf RecSt.M sts
            else Pval) = maxOf RecSt.M sts by rw [if_neg h0, if_pos h3])
          wp_auto
          wp_apply wp_getMaxFromResponses_M γ p sl' R sts Hne $$ [] as %pr ⟨%Hprn, #Hpr⟩
          · iframe #
          finish_next pr (maxOf RecSt.M sts)
        rw [_root_.decide_eq_false (fun h => h3 ((srem4_eq Sw 3 (by decide)).1 h))]
        ghost_next Pval (show (if (sint.Z Sw).tmod 4 = 0 then maxOf RecSt.F sts
          else if (sint.Z Sw).tmod 4 = 3 then maxOf RecSt.M sts else Pval) = Pval by
            rw [if_neg h0, if_neg h3])
        finish_next Pv Pval
      · rw [_root_.decide_eq_false hall]
        wp_auto
        ihave HI7 : (∃ (i : w64) (Sc : w64) (Pc' : ProposerMessage_Proposal) (Pvc : pure.Val),
            "i" ∷ i_ptr ↦ i ∗ "S" ∷ S_ptr ↦ Sc ∗ "P" ∷ P_ptr ↦ Pc' ∗ "#HPc" ∷ propRep γ Pc' Pvc ∗
            "#Hpc" ∷ evIn γ (.pstate (sint.Z msg.instance') k msg.isLeader' (sint.Z Sc) Pvc) ∗
            "%Hadp" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ R.length ∧ sint.Z Sw ≤ sint.Z Sc ∧
              ((Sc = Sw ∧ Pvc = Pval) ∨ ∃ st', st' ∈ sts ∧ sint.Z Sw < st'.S ∧
                sint.Z Sc = st'.S ∧ Pvc = st'.F)⌝ : IProp GF) $$ [i S P]
        · iexists W64 0, Sw, Pv, Pval
          iframe
          iframe #
          ipureintro
          exact ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, Int.le_refl _,
            Or.inl ⟨rfl, rfl⟩⟩
        wp_for HI7
        by_cases hi2 : sint.Z i < sint.Z sl'.len
        · rw [_root_.decide_eq_true hi2]
          have hb1 : sint.nat i < R.length := by word
          have hb2 : sint.nat i < sts.length := by word
          list_elem R (sint.nat i) as y
          list_elem sts (sint.nat i) as sty
          simp only [_root_.decide_true, ↓reduceIte]
          ihave #Hyv := repliesRep_lookup R sts _ y sty Hy_lookup Hsty_lookup $$ HrepG
          iunfold rrVal at Hyv
          icases Hyv with ⟨%Hyst, #HyF, -⟩
          wp_auto
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hadp.1, hi2⟩)]
          icases ownSlice_elem_acc (sint.Z i) y sl' _ _ Hadp.1 Hy_lookup $$ Hsl' with ⟨Hy, -⟩
          iStructNamed Hy
          wp_auto
          by_cases hgt : sint.Z Sc < sint.Z y.S'
          · rw [_root_.decide_eq_true hgt]
            wp_auto
            iunfold rpRep at HyF
            icases HyF with ⟨%fz, #Hfz, %Hfzf, #Hfzids⟩
            iStructNamed Hfz
            imod ghost_stepR γ ⊤ (by simp) c _ (sint.Z msg.instance') (sint.Z Sw) G
              (.pstate (sint.Z msg.instance') k msg.isLeader' sty.S sty.F)
              (fun W h0 h1 => Step.adopt _ _ _ _ _ _ _ h0 (HR W h1)
                (List.mem_of_getElem? Hsty_lookup) (by
                  rcases Hadp.2.2.2 with ⟨h1, -⟩ | ⟨st'', -, h1, h2, -⟩
                  · subst h1; omega
                  · omega))
              (by intros; nofun) (by intros; nofun) $$ Hinv Hconf Hpst HgrecG with #Hpst'
            have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl'.len := ⟨Hadp.1, hi2⟩
            repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] | wp_auto)
            ihave #Hnil := ownSlice_nil (V := Loc) (GF := GF) DFrac.discard
            wp_for_post
            iframe
            iexists i + W64 1, y.S', _, sty.F
            rw [Hyst]
            iframe
            isplitr
            · unfold propRep
              iexists [], []
              dsimp only
              iframe #
              isplitr
              · ipureintro; exact Hfzf
              isplitr
              · iapply repList_nil
              isplitr
              · iapply BigSepL.bigSepL_nil.2; iempintro
              ipureintro; simp
            iframe #
            ipureintro
            refine ⟨by word, by word, by omega,
              Or.inr ⟨sty, List.mem_of_getElem? Hsty_lookup, ?_, ?_, rfl⟩⟩
            · rcases Hadp.2.2.2 with ⟨h1, -⟩ | ⟨st'', -, h1, h2, -⟩
              · subst h1; omega
              · omega
            · rfl
          · rw [_root_.decide_eq_false hgt]
            wp_auto
            wp_for_post
            iframe
            iexists i + W64 1, Sc, Pc', Pvc
            iframe
            iframe #
            ipureintro
            exact ⟨by word, by word, Hadp.2.2.1, Hadp.2.2.2⟩
        · rw [_root_.decide_eq_false hi2]
          simp only [intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte,
            _root_.decide_true]
          wp_for_post
          iframe
          iexists Sc, Pc', Pvc, dsn, []
          iframe
          iframe #
          unfold dsRep
          iexists []
          iframe #
          isplitr
          · iapply repList_nil
          iapply BigSepL.bigSepL_nil.2; iempintro
    · have Hsl'ne : ¬ sl'.len = W64 ((c.n / 2 + 1 : Nat) : Int) := by
        intro h; have := congrArg sint.Z h; rw [Hsz, Hmaj.2.1] at this; omega
      rw [_root_.decide_eq_false Hsl'ne]
      wp_auto
      wp_for_post
      iframe
      iexists sl', rs ++ [xr], recv • msetSingleton rp, got ++ [(j, v, st)], rp
      iframe
      iframe #
      isplitr
      · first
          | (iapply BigSepL.bigSepL_nil.2; iempintro)
          | (iapply BigSepL.bigSepL_snoc.2; iframe #)
      isplitr
      · simp only [List.map_append, List.map_cons, List.map_nil]
        iapply repliesRep_snoc $$ Hrep Hxrv
      ipureintro
      refine ⟨by simp; omega, ?_, fun g hg => ?_⟩
      · rw [List.map_append, List.nodup_append]
        refine ⟨Hgot.2.1, by simp, ?_⟩
        intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact Hjf ha
      · rcases List.mem_append.1 hg with hg | hg
        · exact Hgot.2.2 g hg
        · simp at hg; subst hg; exact Hjv
  done

end propose

end prop

end Perennial.raxos
