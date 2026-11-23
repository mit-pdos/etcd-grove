/-
`Op(s, in)` (`kit.go`), client machine `c`'s operation, as remote's `op` (the lab's
`Kit/{OpMain,OpLemmas}.lean`, re-based on remote): given the slot's update of the input `i`
(`slotUpd (qR γ) i Φ`: a put's one-shot `lin`, a get's persistent one, `lin_opAU`), it takes the
sequence number `n = s.next` under `s.mu` and, if `n < 20`, registers request `opId c n` there with
the update (`op_register`: the lock invariant holds client `c`'s half of the registry counter), and
takes the request's five tickets; it sends the batch to every replica (`wp_send`) and waits for the
first answer on its future (`ansContract`), or times out. An answer's result is the committed
output (`op_collect`, `resultOf_ansOf`), which the codec encodes (`qOutOk_of_ans`); no answer, or
`n = 20` (the budget spent: nothing registered, nothing sent), is the unknown output.

Overlapping calls (remote's `op` is persistent and `Do` retries reads) are fine: each takes its
own sequence number under the lock.
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitOpLib
public import Dsverify.Proof.raxos.Proxy.SliceLit
public import Perennial.Spec.time.After

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure raxos.msg

/-! ## The update registered -/

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS HasLC.hasLC GF]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- The postcondition registered for remote's `Φ`: `Φ` of the clamped output, and the output is a
step's. -/
def regPost (i : QIn) (Φ : QOut → IProp GF) (o : KOut) : IProp GF :=
  iprop(Φ (clampO qOut0 o) ∗ ⌜∃ σ, o = (kvB.step i.1 σ).2⌝)

theorem opAU_step (γ : QNames) (i : QIn) (Φ : QOut → IProp GF) :
    opAU (GF := GF) γ i.1 (fun o => Φ (clampO qOut0 o)) ⊢ opAU γ i.1 (regPost i Φ) := by
  unfold opAU regPost
  iintro H
  imod H with ⟨%σ, Hown, Hclose⟩
  imodintro
  iexists σ
  iframe Hown
  iintro Hown
  imod Hclose $$ Hown with HΦ
  imodintro
  iframe HΦ
  ipureintro; exact ⟨σ, rfl⟩

/-- The slot's update of `i` is QuePaxa's request update with the registered postcondition. -/
theorem slotUpd_opUpd (γ : QNames) (i : QIn) (Φ : QOut → IProp GF) :
    slotUpd (Gg := Gg) (qR γ) i Φ ⊢ opUpd γ i.1 (regPost i Φ) := by
  cases h : i.1.put
  · have hw : (qR (Gg := Gg) γ).B.isWrite i = false := by
      simp [qR, qB, outB, subB, kvB, h]
    rw [slotUpd_read _ hw]
    unfold opUpd
    rw [h]
    simp only [Bool.false_eq_true, ↓reduceIte]
    iintro #H
    iintro !>
    iapply opAU_step
    iapply (lin_opAU γ i Φ).1 $$ H
  · have hw : (qR (Gg := Gg) γ).B.isWrite i = true := by
      simp [qR, qB, outB, subB, kvB, h]
    rw [slotUpd_write _ hw]
    unfold opUpd
    rw [h]
    simp only [↓reduceIte]
    iintro H
    iapply opAU_step
    iapply (lin_opAU γ i Φ).1 $$ H

end ghost

section op
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem' : raxos.examples.quepaxanet.Assumptions]
variable [π : NetProtoGS] [ρ : RemoteGS] [qv : hyp.QpVocab GF]
variable [net.Assumptions] [net.FieldAssumptions] [_root_.Perennial.bufio.Assumptions]
variable [_root_.Perennial.io.Assumptions] [time.Assumptions]
variable [raxos.proto.client.Assumptions] [raxos.replica.src.Assumptions] [pb : hyp.PbHyp GF]

attribute [local instance] HeapGS.goose_globalGS

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

/-- `op_register` at the full mask. -/
theorem op_register_top (γ : QNames) (c n : Nat) (hcn : c < 6 ∧ n < 20) (inp : KIn)
    (hinp : inputOk inp) (Φ : KOut → IProp GF) :
    ⊢@{IProp GF} inv smrN (smrInv γ) -∗ cntHalf γ c n -∗ opUpd γ inp Φ ={⊤}=∗
      cntHalf γ c (n + 1) ∗ batchReg γ (opId c n) ⟨opId c n, clientName c, [cmdOf inp]⟩ ∗
      opPending γ (opId c n) inp Φ :=
  op_register γ ⊤ (by simp) c n hcn inp hinp Φ

/-- `op_collect` at the full mask. -/
theorem op_collect_top (γ : QNames) (x r : GoString) (inp : KIn) (Φ : KOut → IProp GF) :
    ⊢@{IProp GF} inv smrN (smrInv γ) -∗ £ 2 -∗ opPending γ x inp Φ -∗ opAns γ x r ={⊤}=∗
      ∃ o, ⌜r = ansOf inp o ∧ ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil"⌝ ∗ Φ o :=
  op_collect γ ⊤ (by simp) x r inp Φ

/-- `wait_promise` at the program logic's instances. -/
theorem wait_promise_top (γ : QNames) (x : GoString) (ch : Loc) (γc : ChanNames) :
    ⊢ isChan (GF := GF) ch γc Loc -∗ ownChan γc Loc (ChanState.Buffered ([] : List Loc)) ={⊤}=∗
      ∃ γf : FutureNames, waitEntry γ x ch ∗ isFuture Loc γf ch ∗
        Await γf [ansContract γ x] :=
  wait_promise γ x ch γc

theorem op_id_eq (c n : Nat) (hc : c < 6) (hn : n < 20) :
    opid.bstr (toString (uint.nat (W64 ((21 + c : Nat) : Int)))) ++ [46#8] ++
      opid.bstr (toString (uint.nat (W64 (n : Int)))) = opId c n := by
  have h1 : uint.nat (W64 (n : Int)) = n := by word
  have h2 : uint.nat (W64 ((21 + c : Nat) : Int)) = 21 + c := by word
  rw [h1, h2, opid.opId_eq]

theorem name_sender (c : Nat) (hc : c < 6) :
    sint.Z (W64 ((21 + c : Nat) : Int)) = clientName c := by
  unfold clientName
  word

theorem qIn_inputOk (i : QIn) : inputOk i.1 := i.2.1

/-- **`Op(s, in)`**: remote's operation (see the file header). -/
theorem wp_Op (wp_Dial : net.Dial.spec (GF := GF) (hG := hG))
    (wp_Write : net.Conn.Write.spec (GF := GF) (hG := hG))
    (wp_Close : net.Conn.Close.spec (GF := GF) (hG := hG))
    (wp_After : time.After.spec (GF := GF) (hG := hG))
    (γ : QNames) (c : Nat) (s : Loc) (i : QIn) (Ψ : QOut → IProp GF) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ isSysL γ c s ∗
        slotUpd (Gg := hG.goose_globalGS) (qR γ) i Ψ }}
      (App (App (Val (@! raxos.examples.quepaxanet.Op)) (Val #s))
        (Val #(In.mk i.1.put i.1.k i.1.v)))
    {{ (v : Out), RET #v; (∃ o : QOut, ⌜v = Out.mk false o.1.found o.1.v⌝ ∗ Ψ o) ∨
        ⌜v = Out.mk true false []⌝ }} := by
  wp_start as ⟨#Hsys, HU⟩
  ihave HU := slotUpd_opUpd γ i Ψ $$ HU
  iunfold isSysL at Hsys
  icases Hsys with ⟨%rs, %rls, %Hcl, #Hf, #Hmu, #Hreps, #Hsh⟩
  obtain ⟨hc, hrl⟩ := Hcl
  ihave #Hsh2 := Hsh
  iunfold sharedRes at Hsh2
  icases Hsh2 with ⟨#Hcons, #Hsmr, -⟩
  ihave #Hf2 := Hf
  iunfold sysFields at Hf2
  icases Hf2 with ⟨#Hname, #Hcf, #Hck, #Hrs, #Hrls⟩
  wp_auto
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, Hinv⟩
  iunfold sysInv at Hinv
  icases Hinv with ⟨%m, %mv, %n, Hw, Hm, Hchs, Hnext, %Hn, Hcnt, Htix⟩
  wp_auto
  by_cases hn20 : n < 20
  rotate_left
  · have hn' : n = 20 := by omega
    subst hn'
    have hd : decide (uint.Z (W64 ((20 : Nat) : Int)) < uint.Z (W64 20)) = false := by decide
    rw [hd]
    wp_auto
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hw Hm Hchs Hnext Hcnt Htix]
    · unfold sysInv; iexists m, mv, 20; iframe; ipureintro; omega
    wp_end
    iright; ipureintro; rfl
  have hd : decide (uint.Z (W64 (n : Int)) < uint.Z (W64 20)) = true := by
    simp only [decide_eq_true_eq]; word
  rw [hd]
  imod op_register_top γ c n ⟨hc, hn20⟩ i.1 (qIn_inputOk i) (regPost i Ψ) $$ Hsmr Hcnt HU
    with ⟨Hcnt, #Hreg, Hpend⟩
  iunfold ticketsFrom at Htix
  rw [ticketsFromL_succ c n hn20] at *
  icases BigSepL.bigSepL_append.1 $$ Htix with ⟨Hts, Htix⟩
  wp_auto
  have hsucc : W64 (n : Int) + W64 1 = W64 ((n + 1 : Nat) : Int) := by word
  rw [hsucc]
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hw Hm Hchs Hnext Hcnt Htix]
  · unfold sysInv ticketsFrom; iexists m, mv, n + 1; iframe; ipureintro; omega
  have hd2 : decide (uint.Z (W64 20) ≤ uint.Z (W64 (n : Int))) = false := by
    simp only [decide_eq_false_iff_not]; word
  rw [hd2]
  wp_auto
  wp_if_destruct
  all_goals (try (wp_apply time.wp_Sleep))
  all_goals
    wp_apply wp_digits
    wp_apply wp_digits
    rw [op_id_eq c n hc hn20]
    wp_apply chan.wp_make2 (V := Loc) $$ [] as %ch %γc ⟨#Hch, -, Hoc⟩
    · ipureintro; decide
    imod wait_promise_top γ (opId c n) ch γc $$ Hch Hoc with ⟨%γf, Hent, #Hfut, Haw⟩
    wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, Hinv⟩
    iunfold sysInv at Hinv
    icases Hinv with ⟨%m', %mv', %n', Hw, Hm, Hchs, Hnext, %Hn', Hcnt, Htix⟩
    wp_auto
    wp_apply wp_mapInsert $$ Hm as Hm
    wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hw Hm Hchs Hnext Hcnt Htix Hent]
    · unfold sysInv; iexists m', _, n'; iframe Hw Hm Hnext Hcnt Htix
      isplitl
      · iapply waitChans_insert $$ [$Hchs $Hent]
      · ipureintro; exact Hn'
    wp_apply (lc := 3) wp_command
    irename Hlc1 => Hlc3; irename Hlc2 => Hlc4; irename Hlc3 => Hlc5
    wp_bind (App (Val (GoInstruction (CompositeLiteral _))) (Val (LiteralValueV _)))
    iapply wp_slice_literal_ex (V := Loc)
    wp_auto
    wp_alloc pm as Hpm
    wp_auto
    iexists [pm]
    simp only [go.arrayLiteralSize, List.foldl_cons, List.foldl_nil]
    simp only [Int.zero_add, Int.max_def]
    isplitr
    · itrivial
    iintro %slp ⟨Hsl, -⟩
    simp only [show ¬ ((1 : Int) ≤ 0) from by decide, ite_false]
    wp_auto
    irename «$r0» => Hbp
    ihave HCB : repCB «$r0_ptr» (DFrac.own 1) ⟨opId c n, clientName c, [cmdOf i.1]⟩ $$ [Hbp Hsl Hpm]
    · unfold repCB repCBVal repList
      iexists _
      iframe Hbp
      iexists [pm]
      iframe Hsl
      isplitr
      · ipureintro; exact ⟨name_sender c hc, rfl, rfl⟩
      isplitr
      · ipureintro; rfl
      iapply BigSepL.bigSepL_cons.2
      isplitl
      · iexists cmdOf i.1
        isplitr
        · ipureintro; rfl
        unfold repCSingle
        iexists _
        iframe Hpm
        ipureintro; exact ⟨rfl, rfl⟩
      · iapply BigSepL.bigSepL_nil.2; iempintro
    ihave %Hrl := ownSlice_len _ _ _ $$ Hrls
    rw [BigSepL.bigSepL_map] at *
    ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "r" ∷ (∃ rl : Loc, r_ptr ↦ rl) ∗
        "HCB" ∷ repCB «$r0_ptr» (DFrac.own 1) ⟨opId c n, clientName c, [cmdOf i.1]⟩ ∗
        "Hts" ∷ ([∗list] k ∈ List.range' (sint.nat j + 1) (5 - sint.nat j),
          ticketTok γ (((k : Nat) : Int), c, n)) ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z rs.len⌝ : IProp GF) $$ [i r HCB Hts]
    · iexists W64 0
      rw [show sint.nat (W64 0) = 0 from rfl,
        show List.range' (0 + 1) (5 - 0) = [1, 2, 3, 4, 5] from rfl]
      iframe i HCB Hts
      isplitl [r]
      · iexists _; iexact r
      ipureintro; constructor <;> word
    irename «in» => Hin
    wp_for HI
    wp_if_destruct
    · have Hif' : sint.Z j < sint.Z rs.len := by
        first | exact Hif | (have h := go.IntoValInj.intoVal_inj (V := Bool) Hif; simpa using h)
      have hidx : 0 ≤ sint.Z j ∧ sint.Z j < sint.Z rs.len := ⟨Hj.1, Hif'⟩
      simp only [hidx, _root_.and_self, ↓reduceIte]
      list_elem rls (sint.Z j).toNat as rl
      wp_apply wp_load_slice_index rs (sint.Z j) rls DFrac.discard rl hidx.1 $$ [Hrls] as -
      · iframe Hrls; ipureintro; exact Hrl_lookup
      iunfold repsOk at Hreps
      ihave #Hrep := BigSepL.bigSepL_lookup (Φ := fun i rl => iprop(isReplica γ c (i + 1) rl))
        Hrl_lookup $$ Hreps
      have hn3 : sint.nat j < 5 := by word
      rw [show 5 - sint.nat j = (5 - (sint.nat j + 1)) + 1 by omega, List.range'_succ]
      icases BigSepL.bigSepL_cons.1 $$ Hts with ⟨Ht, Hts⟩
      icases r with ⟨%rl0, r⟩
      wp_auto
      wp_apply wp_send wp_Dial wp_Write wp_Close γ ((sint.Z j).toNat + 1) rl «$r0_ptr» (DFrac.own 1)
        _ c n $$ [$Hrep $HCB $Hreg Ht] as HCB
      · rw [show (sint.Z j).toNat = sint.nat j from rfl]
        iframe Ht
        ipureintro; exact tix_mem _ _ _ ⟨by omega, by omega⟩ hc hn20
      wp_for_post
      iframe
      iapply to_named
      iexists j + W64 1
      rw [show sint.nat (j + W64 1) = sint.nat j + 1 by word]
      iframe i HCB Hts
      isplitl [r]
      · iexists _; iexact r
      ipureintro; word
    have Hif' : ¬ sint.Z j < sint.Z rs.len := by
      intro h; apply Hif; first | exact h | simp [h]
    (try rw [if_pos (by simp [Hif'])])
    (try wp_auto)
    ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
    · iPkgInit
    wp_apply (lc := 2) (time.After.spec_pkgInit wp_After _) as %tch %γt #Htch
    wp_apply_core chan.wp_select_blocking
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the answer
      dsimp only [chan.blockingClausePre]
      iexists Loc, inferInstance, inferInstance, inferInstance, inferInstance, ch, γf.chanName
      isplitr
      · ipureintro; rfl
      ihave #Hisch : isChan ch γf.chanName Loc $$ [Hfut]
      · unfold isFuture; icases Hfut with ⟨$, -⟩
      iframe Hisch
      iapply future_await_au γf ch _ _ $$ Hfut [$Hlc3 $Hlc4 $Hlc5 $Haw]
      inext
      iintro %p %P %pre %post %Hsplit HP -
      have hP : P = ansContract γ (opId c n) := by
        rcases pre with _ | ⟨a, pre⟩
        · simp only [List.nil_append, List.cons.injEq] at Hsplit; exact Hsplit.1.symm
        · simp at Hsplit
      subst hP
      iunfold ansContract at HP
      icases HP with ⟨%b, %r, HCBa, %hbr, #Hans⟩
      ihave Hlc := (lc_split (n := 1) (m := 1)).2 $$ [Hlc1 Hlc2]
      · iframe
      imod op_collect_top γ (opId c n) r i.1 (regPost i Ψ) $$ Hsmr Hlc Hpend Hans
        with ⟨%o, %ho, HQ⟩
      iunfold regPost at HQ
      icases HQ with ⟨HQ, %hstep⟩
      obtain ⟨σ, rfl⟩ := hstep
      obtain ⟨hlen, hres⟩ := resultOf_ansOf i.1 (qIn_inputOk i) σ ho.2
      have hok := qOutOk_of_ans i.1 (qIn_inputOk i) σ b (by rw [hbr.2.1, ho.1]) hbr.2.2
      rw [← ho.1] at hlen hres
      wp_auto
      wp_apply wp_result i.1 p (DFrac.own 1) b r hbr.2.1 hlen $$ [HCBa]
      · iexact HCBa
      iapply HΦ
      ileft
      iexists ⟨(kvB.step i.1 σ).2, hok⟩
      rw [clampO_of qOut0 hok]
      iframe HQ
      ipureintro
      rw [hres]
    iapply BigAndL.bigAndL_cons.2
    isplit
    · -- the timeout
      dsimp only [chan.blockingClausePre]
      ihave #Htch_chan := is_bag_is_chan _ _ _ $$ Htch
      iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
      isplitr
      · ipureintro; rfl
      iframe Htch_chan
      iapply bag_recv_au $$ [$Hlc1 $Hlc2] Htch
      inext
      iintro %v -
      wp_auto
      wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlk, Hinv⟩
      iunfold sysInv at Hinv
      icases Hinv with ⟨%m2, %mv2, %n2, Hw, Hm, Hchs, Hnext, %Hn2, Hcnt, Htix⟩
      wp_auto
      wp_apply wp_mapDelete $$ Hm as Hm
      wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlk Hw Hm Hchs Hnext Hcnt Htix]
      · unfold sysInv; iexists m2, _, n2; iframe Hw Hm Hnext Hcnt Htix
        isplitl
        · iapply waitChans_delete $$ Hchs
        · ipureintro; exact Hn2
      iapply HΦ
      iright
      ipureintro; rfl
    · iapply BigAndL.bigAndL_nil.2
      itrivial

end op

end raxos.examples.quepaxanet
end Perennial
