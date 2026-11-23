/-
Package `proposer`: `handleFetchRequest` (registered batches from a random peer) and
`handleDecisionRequest` (decided slots to every recorder).
-/
module

public import Dsverify.Proof.raxos.Proposer.Esp
public import Dsverify.Proof.raxos.Proposer.Conv
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

section fetch
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [raxos.replica.src.Assumptions] [raxos.proto.client.Assumptions]
  [raxos.examples.quepaxanet.Assumptions]

attribute [local instance] hyp.qpCodec

variable [gh : hyp.grpc.GrpcHyp qv.grpc] [rh : hyp.RandHyp GF]

/-- A peer's gRPC client: peer `j` (recorder `j + 1`). -/
def peerOk (γ : QNames) (pr : peer) (j : Nat) : IProp GF :=
  iprop(∃ (l cc : Loc), ⌜j < 5 ∧
      pr.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
    l ↦□ (consensusClient.mk
      (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
    qv.grpc.isClientConn cc (world γ) (recAddr (j + 1)))

/-- `findClientByName(rn)` for a configured name. -/
theorem wp_findClientByName (γ : QNames) (cf : QConf) (k : Nat) (p : Loc) (rn : w64)
    (hrn : 1 ≤ sint.Z rn ∧ sint.Z rn ≤ cf.n) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proposerP γ cf k p }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"findClientByName")) (Val #rn))
    {{ (pr : peer), RET #pr; ∃ j, peerOk γ pr j }} := by
  wp_start as #Hprop
  ihave #Hprop' := Hprop
  iunfold proposerP at Hprop'
  icases Hprop' with ⟨%pv, %γ1, %γ2, %γ4, %γ5, %γ6, #Hp, %Hpv, #Hconf, #Hpeers, -, -, -, -, -, -⟩
  have Hcn := conf_n_sint cf Hpv.1
  iStructNamed Hp
  iunfold peersP at Hpeers
  icases Hpeers with ⟨%ps, #Hps, %Hpsl, #Hpsr⟩
  ihave %Hpsl' := ownSlice_len _ _ _ $$ Hps
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ cf.n ∧
        ∀ m q, m < sint.nat i → ps[m]? = some q → q.name' ≠ rn⌝ : IProp GF) $$ [i]
  · iexists W64 0
    iframe
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega,
      fun m q hm _ => absurd hm (by simp)⟩
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z i < sint.Z pv.peers'.len := by first | exact Hif | exact dec_true Hif | exact dec_not_true Hif
    list_elem ps (sint.nat i) as q
    have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z pv.peers'.len := ⟨Hi.1, Hlt⟩
    ihave ⟨%Hqn, Hq⟩ := BigSepL.bigSepL_lookup (Φ := fun j p => iprop(⌜sint.Z p.name' = j + 1⌝ ∗
        ∃ (l cc : Loc), ⌜p.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
          l ↦□ (consensusClient.mk
            (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
          qv.grpc.isClientConn cc (world γ) (recAddr (j + 1)))) Hq_lookup $$ Hpsr
    icases ownSlice_elem_acc (sint.Z i) q _ _ _ Hi.1 Hq_lookup $$ Hps with ⟨Hqe, -⟩
    iStructNamed Hqe
    repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] |
      (wp_apply wp_load_slice_index _ (sint.Z i) ps _ q Hi.1 $$ [Hps] as -;
        · iframe #; ipureintro; exact Hq_lookup) | wp_auto)
    by_cases hqn : q.name' = rn
    · rw [_root_.decide_eq_true hqn]
      repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] |
        (wp_apply wp_load_slice_index _ (sint.Z i) ps _ q Hi.1 $$ [Hps] as -;
          · iframe #; ipureintro; exact Hq_lookup) | wp_auto)
      wp_for_post
      iapply HΦ
      iexists (sint.nat i)
      unfold peerOk
      icases Hq with ⟨%l, %cc, %Hlc, #Hl, #Hcc⟩
      iexists l, cc
      iframe #
      ipureintro; exact ⟨by word, Hlc⟩
    · rw [_root_.decide_eq_false hqn]
      wp_auto
      wp_for_post
      iframe
      iexists i + W64 1
      iframe
      ipureintro
      refine ⟨by word, by word, fun m q' hm hq' => ?_⟩
      have Hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
      rw [Hi1] at hm
      by_cases hmi : m < sint.nat i
      · exact Hi.2.2 m q' hmi hq'
      · have : m = sint.nat i := by omega
        subst this; rw [Hq_lookup] at hq'; cases hq'; exact hqn
  · have Hge : ¬ sint.Z i < sint.Z pv.peers'.len := by first | exact Hif | exact dec_true Hif | exact dec_not_true Hif
    have Hi3 : sint.nat i = cf.n := by word
    obtain ⟨q, hq⟩ : ∃ q, ps[(sint.Z rn).toNat - 1]? = some q :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hpsl]; omega)⟩
    ihave ⟨%Hqn, -⟩ := BigSepL.bigSepL_lookup (Φ := fun j p => iprop(⌜sint.Z p.name' = j + 1⌝ ∗
        ∃ (l cc : Loc), ⌜p.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
          l ↦□ (consensusClient.mk
            (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
          qv.grpc.isClientConn cc (world γ) (recAddr (j + 1)))) hq $$ Hpsr
    exfalso
    apply Hi.2.2 _ q (by omega) hq
    apply BitVec.eq_of_toInt_eq
    change sint.Z q.name' = sint.Z rn
    rw [Hqn]; omega

/-- `getRandomClient()`: some peer's client. -/
theorem wp_getRandomClient (γ : QNames) (cf : QConf) (k : Nat) (p : Loc) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proposerP γ cf k p }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"getRandomClient")) (Val #()))
    {{ (pr : peer), RET #pr; ∃ j, peerOk γ pr j }} := by
  wp_start as #Hprop
  ihave #Hprop' := Hprop
  iunfold proposerP at Hprop'
  icases Hprop' with ⟨%pv, %γ1, %γ2, %γ4, %γ5, %γ6, #Hp, %Hpv, #Hconf, -, -, -, -, -, -, -⟩
  obtain ⟨Hc, Hk1, Hkn, Hnr, Hname, Hhi, Hsm, Hasync⟩ := Hpv
  have Hcn := conf_n_sint cf Hc
  iStructNamed Hp
  wp_auto
  rw [Hnr]
  wp_apply hyp.RandHyp.Intn (GF := GF) (W64 cf.n) (by omega) as %x %Hx
  ihave HI : (∃ (r : w64), "rn" ∷ rn_ptr ↦ r ∗ "%Hr" ∷ ⌜1 ≤ sint.Z r ∧ sint.Z r ≤ cf.n⌝ : IProp GF)
    $$ [rn]
  · iexists _
    iframe
    ipureintro; constructor <;> word
  wp_for HI
  wp_if_destruct
  · wp_apply hyp.RandHyp.Intn (GF := GF) (W64 cf.n) (by omega) as %y %Hy
    wp_for_post
    iframe
    iexists _
    iframe
    ipureintro; constructor <;> word
  · wp_apply wp_findClientByName γ cf k p r Hr $$ [] as %pr Hpr
    · iframe #
    iapply HΦ
    iexact Hpr

/-- `handleFetchRequest(message)`: registered batches. -/
theorem wp_handleFetchRequest (γ : QNames) (cf : QConf) (k : Nat) (p : Loc) (msg : FetchRequest) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proposerP γ cf k p ∗ fetchReqP msg }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"handleFetchRequest")) (Val #msg))
    {{ (r : FetchResposne), RET #r; fetchRespP γ r }} := by
  wp_start as ⟨#Hprop, #Hreq⟩
  ihave #Hprop' := Hprop
  iunfold proposerP at Hprop'
  icases Hprop' with ⟨%pv, %γ1, %γ2, %γ4, %γ5, %γ6, #Hp, %Hpv, #Hconf, -, -, -, -, -, -, #Hinv⟩
  iunfold fetchReqP at Hreq
  icases Hreq with ⟨%ids, #Hids, %Hidsok⟩
  wp_auto
  wp_apply wp_slice_make2 (V := Loc) (W64 0) as %c0 ⟨Hc0, Hc0c⟩
  · ipureintro; decide
  simp only [List.replicate_zero]
  ipersist Hc0
  ipersist message
  ipersist prop
  iStructNamed message
  ihave HI : (∃ (f : Bool) (c : GoSlice) (cps : List Loc) (cbs : List Batch),
      "found" ∷ found_ptr ↦ f ∗ "cltBatches" ∷ cltBatches_ptr ↦ c ∗ "#Hc" ∷ c ↦*□ cps ∗
      "Hcc" ∷ ownSliceCap Loc c (DFrac.own 1) ∗
      "#Hcr" ∷ repList repDRBatch cps .discard cbs ∗
      "#Hcreg" ∷ ([∗list] b ∈ cbs, batchReg γ b.id b) ∗
      "%Hcfit" ∷ ⌜∀ b ∈ cbs, batchFit b⌝ : IProp GF) $$ [found cltBatches Hc0c]
  · iexists false, c0, [], []
    iframe
    iframe #
    isplitr
    · iapply repList_nil
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; simp
  wp_for HI
  cases f
  · simp only [Bool.not_false, _root_.decide_true, ↓reduceIte]
    wp_auto
    wp_apply wp_getRandomClient γ cf k p $$ [] as %pr ⟨%jr, Hpr⟩
    · iframe #
    unfold peerOk
    icases Hpr with ⟨%l, %cc, ⟨%Hj, %Hprc⟩, #Hl, #Hccc⟩
    wp_apply context.wp_Background
    wp_apply context.wp_WithTimeout_Background as %ctx %γctx %cancel %dl ⟨#Hcancel, #Hctx, -⟩
    rw [Hprc]
    wp_auto
    ipersist «$a1»
    have Hr : 1 ≤ jr + 1 ∧ jr + 1 ≤ 5 := by omega
    wp_apply wp_FetchBatches γ (jr + 1) l cc ctx _ _ .discard ids slice.nil $$ [] as %out %err Hres
    · iframe #
      isplitr
      · ipureintro; exact Hr
      unfold repDReq
      iexists _
      iframe #
      ipureintro; rfl
    wp_bind (If _ _ _)
    iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ ∃ (f : Bool) (c : GoSlice)
        (cps : List Loc) (cbs : List Batch),
        found_ptr ↦ f ∗ cltBatches_ptr ↦ c ∗ c ↦*□ cps ∗ ownSliceCap Loc c (DFrac.own 1) ∗
        repList repDRBatch cps .discard cbs ∗ ([∗list] b ∈ cbs, batchReg γ b.id b) ∗
        ⌜∀ b ∈ cbs, batchFit b⌝ ∗ numBtches_ptr ↦ msg.ids'.len)) $$ [found cltBatches Hcc resp numBtches Hres]
    · icases Hres with (⟨%Herr, %bs, Hrr, %Hbfit, #Hbreg⟩ | %Herr)
      · subst Herr
        imod repDResp_persist _ _ $$ Hrr with #Hrr
        wp_auto
        by_cases hnull : out = null
        · subst hnull
          wp_auto
          isplitr
          · ipureintro; rfl
          iexists false, c, cps, cbs
          iframe
          iframe #
          ipureintro; exact Hcfit
        · rw [_root_.decide_eq_false hnull]
          iunfold repDResp at Hrr
          icases Hrr with ⟨%xr, %rps, #Hxr, %Hxu, #Hrps, #Hrpr⟩
          iStructNamed Hxr
          ihave %Hrpsl := ownSlice_len _ _ _ $$ Hrps
          ihave %Hrpl := repList_length _ _ _ _ $$ Hrpr
          wp_auto
          ihave HI2 : (∃ (i : w64) (c : GoSlice) (cps : List Loc) (cbs : List Batch),
              "i" ∷ i_ptr ↦ i ∗ "cltBatches" ∷ cltBatches_ptr ↦ c ∗ "#Hc" ∷ c ↦*□ cps ∗
              "Hcc" ∷ ownSliceCap Loc c (DFrac.own 1) ∗
              "#Hcr" ∷ repList repDRBatch cps .discard cbs ∗
              "#Hcreg" ∷ ([∗list] b ∈ cbs, batchReg γ b.id b) ∗
              "%Hcfit" ∷ ⌜(∀ b ∈ cbs, batchFit b) ∧ 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z xr.ClientBatches'.len⌝
              : IProp GF) $$ [i cltBatches Hcc]
          · iexists W64 0, c, cps, cbs
            iframe
            iframe #
            ipureintro; exact ⟨Hcfit, by decide, by word⟩
          wp_for HI2
          by_cases hi2 : sint.Z i < sint.Z xr.ClientBatches'.len
          · rw [_root_.decide_eq_true hi2]
            list_elem rps (sint.nat i) as q
            simp only [_root_.decide_true, ↓reduceIte]
            ihave ⟨%b, %Hb, #Hqb⟩ := repList_lookup _ _ _ _ _ _ Hq_lookup $$ Hrpr
            ihave #Hqb0 := Hqb
            have hb : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z xr.ClientBatches'.len := ⟨Hcfit.2.1, hi2⟩
            wp_auto
            ihave %Hcl := ownSlice_len _ _ _ $$ Hc
            wp_bind (App (App (App (Val doFor) _) _) _)
            iapply wp_wand (Φ := fun v => iprop(⌜v = executeVal⌝ ∗ (∃ j : w64, j_ptr ↦ j) ∗
                (∃ fb : Bool, foundBtch_ptr ↦ fb) ∗ cltBatches_ptr ↦ c ∗ resp_ptr ↦ out ∗ i_ptr ↦ i))
                $$ [j foundBtch cltBatches resp i]
            · ihave HI3 : (∃ (j : w64) (fb : Bool), "j" ∷ j_ptr ↦ j ∗ "fb" ∷ foundBtch_ptr ↦ fb ∗
                  "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z c.len⌝ : IProp GF) $$ [j foundBtch]
              · iexists W64 0, false
                iframe
                ipureintro; constructor <;> word
              unfold repDRBatch
              icases Hqb with ⟨%qx, %qms, #Hqx, %Hqxf, -⟩
              iStructNamed Hqx
              wp_for HI3
              by_cases hj : sint.Z j < sint.Z c.len
              · rw [_root_.decide_eq_true hj]
                list_elem cps (sint.nat j) as cq
                simp only [_root_.decide_true, ↓reduceIte]
                ihave ⟨%cb, %Hcb, #Hcqb⟩ := repList_lookup _ _ _ _ _ _ Hcq_lookup $$ Hcr
                icases Hcqb with ⟨%cx, %cms, #Hcx, %Hcxf, -⟩
                iStructNamed Hcx
                have hbj : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z c.len := ⟨Hj.1, hj⟩
                repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] |
                  rw [ite_eq_left_of_eq_true _ _ (eq_true hbj)] |
                  (wp_apply wp_load_slice_index _ (sint.Z i) rps _ q hb.1 $$ [Hrps] as -;
                    · iframe #; ipureintro; exact Hq_lookup) |
                  (wp_apply wp_load_slice_index _ (sint.Z j) cps _ cq hbj.1 $$ [Hc] as -;
                    · iframe #; ipureintro; exact Hcq_lookup) | wp_auto)
                by_cases hid : qx.Id' = cx.Id'
                · rw [_root_.decide_eq_true hid]
                  wp_auto
                  wp_for_post
                  iframe
                  ipureintro; rfl
                · rw [_root_.decide_eq_false hid]
                  wp_auto
                  wp_for_post
                  iframe
                  iexists j + W64 1, fb
                  iframe
                  ipureintro; constructor <;> word
              · rw [_root_.decide_eq_false hj]
                simp only [intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte,
                  _root_.decide_true]
                iframe
            iintro %v ⟨%Hv, ⟨%jv, j⟩, ⟨%fb, foundBtch⟩, cltBatches, resp, i⟩
            subst Hv
            wp_auto
            have Hi1 : sint.Z (i + W64 1) = sint.Z i + 1 := by word
            cases fb
            · simp only [Bool.not_false]
              wp_auto
              repeat (first | rw [ite_eq_left_of_eq_true _ _ (eq_true hb)] |
                (wp_apply wp_load_slice_index _ (sint.Z i) rps _ q hb.1 $$ [Hrps] as -;
                  · iframe #; ipureintro; exact Hq_lookup) | wp_auto)
              wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
              iapply wp_slice_literal (V := Loc) [q]
              wp_auto
              rw [show go.arrayLiteralSize [KeyedElement none
                (ElementExpression (go.GoType.PointerType DecideResponse_ClientBatch.ty) #q)] = 1 from rfl]
              isplitr
              · ipureintro; rfl
              iintro %sp ⟨Hsp, -⟩
              wp_apply wp_slice_append_persistent (V := Loc) c cps _ [q] (DFrac.own 1)
                $$ [$Hc $Hcc Hsp] as %c'' ⟨#Hc'', Hcc'', -⟩
              · iexact Hsp
              ihave #Hreg1 := BigSepL.bigSepL_lookup (Φ := fun _ b => iprop(batchReg γ b.id b)) Hb $$ Hbreg
              wp_for_post
              iframe
              iexists i + W64 1, c'', cps ++ [q], cbs ++ [b]
              iframe
              iframe #
              isplitr
              · iapply repList_snoc $$ Hcr Hqb0
              isplitr
              · iapply BigSepL.bigSepL_nil.2; iempintro
              ipureintro
              refine ⟨fun b' hb' => ?_, by word, by word⟩
              rcases List.mem_append.1 hb' with h | h
              · exact Hcfit.1 b' h
              · simp at h; subst h; exact Hbfit b' (List.mem_of_getElem? Hb)
            · simp only [Bool.not_true]
              wp_auto
              wp_for_post
              iframe
              iexists i + W64 1, c, cps, cbs
              iframe
              iframe #
              ipureintro; exact ⟨Hcfit.1, by word, by word⟩
          · rw [_root_.decide_eq_false hi2]
            simp only [intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte,
              _root_.decide_true]
            wp_auto
            by_cases hl : c.len = msg.ids'.len
            · rw [_root_.decide_eq_true hl]
              wp_auto
              isplitr
              · ipureintro; rfl
              iexists true, c, cps, cbs
              iframe
              iframe #
              ipureintro; exact Hcfit.1
            · rw [_root_.decide_eq_false hl]
              wp_auto
              isplitr
              · ipureintro; rfl
              iexists false, c, cps, cbs
              iframe
              iframe #
              ipureintro; exact Hcfit.1
      · rcases err with e | _
        · wp_auto
          isplitr
          · ipureintro; rfl
          iexists false, c, cps, cbs
          iframe
          iframe #
          ipureintro; exact Hcfit
        · exact absurd rfl Herr
    iintro %v ⟨%Hv, %f', %c', %cps', %cbs', found, cltBatches, #Hc', Hcc', #Hcr', #Hcreg', %Hcfit', numBtches⟩
    subst Hv
    wp_auto
    wp_apply Hcancel
    wp_for_post
    iframe
    iexists f', c', cps', cbs'
    iframe
    iframe #
    ipureintro; exact Hcfit'
  · simp only [Bool.not_true, intoVal_eq_iff, Bool.false_eq_true, _root_.decide_false, ↓reduceIte,
      _root_.decide_true]
    wp_auto
    wp_apply wp_convertToClientBatches p c cps cbs $$ [] as %r ⟨%vs, #Hvs, %Hvl, #Hvr⟩
    · iframe #
    iapply HΦ
    unfold fetchRespP
    iexists vs, cbs
    iframe #
    unfold batchesP
    isplitr
    · ipureintro; exact ⟨Hvl, Hcfit⟩
    iapply BigSepL.bigSepL_impl $$ Hvr
    imodintro
    iintro %n %v %Hv ⟨%b, %Hb, #Hrep⟩
    iexists b
    iframe #
    isplitr
    · ipureintro; exact Hb
    iapply BigSepL.bigSepL_lookup (Φ := fun _ b => iprop(batchReg γ b.id b)) Hb $$ Hcreg

/-- `handleDecisionRequest(decision)`. -/
theorem wp_handleDecisionRequest (γ : QNames) (cf : QConf) (k : Nat) (p : Loc) (d : Decision) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗ proposerP γ cf k p ∗ decisionP γ d }}
      (App (Val (p @!! go.GoType.PointerType Proposer.ty @!! go!"handleDecisionRequest")) (Val #d))
    {{ RET #(); True }} := by
  wp_start as ⟨#Hprop, #Hd⟩
  ihave #Hprop' := Hprop
  iunfold proposerP at Hprop'
  icases Hprop' with ⟨%pv, %γ1, %γ2, %γ4, %γ5, %γ6, #Hp, %Hpv, #Hconf, #Hpeers, -, -, -, -,
    -, #Hinv⟩
  obtain ⟨Hc, Hk1, Hkn, Hnr, Hname, Hhi, Hsm, Hasync⟩ := Hpv
  have Hcn := conf_n_sint cf Hc
  iStructNamed Hp
  iunfold decisionP at Hd
  icases Hd with ⟨#Hd, -⟩
  wp_auto
  wp_apply context.wp_Background
  wp_apply context.wp_WithTimeout_Background as %ctx %γctx %cancel %dl ⟨#Hcancel, #Hctx, -⟩
  wp_apply wp_extractDecisionSlots γ p _ _ _ $$ [] as %dsl ⟨%sps, %ds, #Hsps, #Hspsr, #Hdec⟩
  · iframe #
  imod sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr $$ wg with ⟨%γwg, Hwg⟩
  imod sync.join.init wg_ptr γwg $$ Hwg with Hwg
  ipersist ctx
  ipersist cancel
  ipersist decidedSlots
  ipersist prop
  iunfold peersP at Hpeers
  icases Hpeers with ⟨%ps, #Hps, %Hpsl, #Hpsr⟩
  ihave %Hpsl' := ownSlice_len _ _ _ $$ Hps
  ihave HI : (∃ (n : w64) (na : w32), "i" ∷ i_ptr ↦ n ∗
      "Hwg" ∷ sync.join.ownAdder wg_ptr na iprop(True) ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ cf.n ∧ sint.Z na = sint.Z n⌝ : IProp GF) $$ [i Hwg]
  · iexists W64 0, W32 0
    iframe
    ipureintro
    refine ⟨by decide, by rw [show sint.Z (W64 0) = 0 from rfl]; omega, by decide⟩
  rw [Hnr]
  wp_for HI
  wp_if_destruct
  · have Hlt : sint.Z n < cf.n := by rw [← Hcn.1]; first | exact Hif | exact dec_true Hif
    wp_apply sync.join.WaitGroup.wp_Add iprop(True) wg_ptr _ na $$ [Hwg] as ⟨Hwg, Hdone⟩
    · iframe; ipureintro; word
    list_elem ps (sint.nat n) as pr
    have hb : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z pv.peers'.len := ⟨Hn.1, by word⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
    wp_apply wp_load_slice_index _ (sint.Z n) ps _ pr Hn.1 $$ [Hps] as -
    · iframe #; ipureintro; exact Hpr_lookup
    ihave ⟨%Hprn, %lc, %cc, %Hprc, #Hlc, #Hcc⟩ :=
      BigSepL.bigSepL_lookup (Φ := fun j p => iprop(⌜sint.Z p.name' = j + 1⌝ ∗
        ∃ (l cc : Loc), ⌜p.client' = interface.mkOk (go.GoType.PointerType consensusClient.ty) #l⌝ ∗
          l ↦□ (consensusClient.mk
            (interface.mkOk (go.GoType.PointerType google_golang_org.grpc.ClientConn.ty) #cc)) ∗
          qv.grpc.isClientConn cc (world γ) (recAddr (j + 1)))) Hpr_lookup $$ Hpsr
    wp_apply wp_fork $$ [Hdone]
    · wp_pures
      wp_apply wp_with_defer as %defer Hdefer
      ipersist «$a1»
      rw [Hprc]
      wp_auto
      have Hr : 1 ≤ sint.nat n + 1 ∧ sint.nat n + 1 ≤ 5 := by word
      wp_apply wp_InformDecision γ (sint.nat n + 1) lc cc ctx _ _ .discard ds slice.nil $$ [] as %o %e -
      · iframe #
        isplitr
        · ipureintro; exact Hr
        unfold repDecs
        iexists _, sps
        iframe #
        ipureintro; rfl
      wp_apply sync.join.WaitGroup.wp_Done iprop(True) wg_ptr $$ [Hdone]
      · iframe
      itrivial
    wp_for_post
    iframe
    iexists n + W64 1, na + W32 1
    iframe
    isplitl [Hwg]
    · iapply sync.join.ownAdder_wand $$ [] Hwg
      iintro -; itrivial
    ipureintro; word
  wp_apply wp_fork $$ [Hwg]
  · wp_auto
    wp_apply sync.join.WaitGroup.wp_Wait iprop(True) na wg_ptr $$ [$Hwg] as -
    wp_apply Hcancel
    itrivial
  iapply HΦ
  itrivial

end fetch

end prop

end Perennial.raxos
