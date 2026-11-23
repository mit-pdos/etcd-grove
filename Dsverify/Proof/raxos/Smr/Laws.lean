/-
The SMR ghost state's laws (interface statements of stages 2-3, `notes/stage2-plan.md`; proofs: package `smr`. Stage 1's
proofs are at the project's tag `mode1-final`).
-/
module

public import Dsverify.Proof.raxos.Ghost
public import Dsverify.Proof.raxos.Cons.Laws
public import Dsverify.Proof.raxos.Smr.Step
public import Dsverify.Proof.raxos.Smr.Register

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode BigSepM BigSepL Net
open Perennial.raxos.pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable {GF : BundledGFunctors} [G : GooseGlobalGS HasLC.hasLC GF]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ### SMR laws -/

/-- The batch with id `x` is the same in every fact. -/
theorem batchReg_agree (γ : QNames) (x : GoString) (b1 b2 : Batch) :
    ⊢@{IProp GF} batchReg γ x b1 -∗ batchReg γ x b2 -∗ ⌜b1 = b2⌝ := by
  unfold batchReg
  iintro ⟨%e1, H1, %h1⟩ ⟨%e2, H2, %h2⟩
  ihave %he := ghostMapElem_agree $$ H1 H2
  ipureintro
  rw [h1.1, h2.1, he]

/-- A registered batch is `"nil"`'s, an epoch summary's (its id is the summary of an order, its
one command the id itself, sender -1), or a request of the client, one command of an input the
kit makes, with id `x` (an ASCII id). -/
theorem batchReg_shape (γ : QNames) (x : GoString) (b : Batch) :
    ⊢@{IProp GF} batchReg γ x b -∗
      ⌜msg.asciiOk x ∧ ((x = go!"nil" ∧ b = nilBatch) ∨
        (b = ⟨x, -1, [x]⟩ ∧ ∃ p, x = summaryId p ∧ sumPerm p) ∨
        (b.id = x ∧ (∃ c : Nat, c < 6 ∧ b.sender = clientName c) ∧ ∃ inp, inputOk inp ∧ b.cmds = [cmdOf inp]))⌝ := by
  unfold batchReg
  iintro ⟨%e, -, %h⟩
  ipureintro
  obtain ⟨hb, hnil, hsum, hop⟩ := h
  subst hb
  cases e with
  | nil =>
    have hx := hnil rfl
    subst hx
    exact ⟨fun b hb => by revert b; decide, Or.inl ⟨rfl, rfl⟩⟩
  | sum =>
    obtain ⟨p, hx, hp⟩ := hsum rfl
    refine ⟨by rw [hx]; exact sumid.summaryId_ascii p, Or.inr (Or.inl ⟨rfl, p, hx, hp⟩)⟩
  | op c j inp q t =>
    obtain ⟨hx, hc, hinp⟩ := hop c j inp q t rfl
    subst hx
    exact ⟨opid.opId_ascii c j, Or.inr (Or.inr ⟨rfl, ⟨c, hc, rfl⟩, inp, hinp, rfl⟩)⟩

/-- `batchReg_shape` under the SMR invariant. -/
theorem batchReg_shape_inv (γ : QNames) (E : CoPset) (hE : ↑smrN ⊆ E) (x : GoString) (b : Batch) :
    ⊢@{IProp GF} inv smrN (smrInv γ) -∗ batchReg γ x b ={E}=∗
      ⌜msg.asciiOk x ∧ ((x = go!"nil" ∧ b = nilBatch) ∨
        (b = ⟨x, -1, [x]⟩ ∧ ∃ p, x = summaryId p ∧ sumPerm p) ∨
        (b.id = x ∧ (∃ c : Nat, c < 6 ∧ b.sender = clientName c) ∧ ∃ inp, inputOk inp ∧ b.cmds = [cmdOf inp]))⌝ := by
  iintro #Hsmr Hb
  ihave %h := batchReg_shape γ x b $$ Hb
  imodintro
  ipureintro; exact h

/-- A proxy registers its epoch summary's batch (`proposePreviousEpochSummary`; a summary id
names the same batch every time). -/
theorem sum_register (γ : QNames) (E : CoPset) (hE : ↑smrN ⊆ E) (c : QConf) (p : List Nat)
    (hc : c.ok) (hp : isPerm c.n p) :
    ⊢@{IProp GF} inv smrN (smrInv γ) ={E}=∗
      batchReg γ (summaryId p) ⟨summaryId p, -1, [summaryId p]⟩ := by
  iintro #Hsmr
  iinv Hsmr with Hi Hclose
  iunfold smrInv at Hi
  icases Hi with ⟨%D, %Reg, %Res, %Cnt, >Hauth, #Hdecs, >Hputs, >Hra, >#Hre, >Hsa, #Hse, >Hca, >Hce,
    >%hf, Hbody⟩
  have hsp : sumPerm p := by
    rcases hc.1 with h | h
    · left; rw [← h]; exact hp
    · right; rw [← h]; exact hp
  cases hR : Reg !! summaryId p with
  | some e =>
    have he : e = .sum := by
      cases e with
      | nil => exact absurd (hf.2.2.1 _ _ hR rfl) (sumid.summaryId_ne_nil p)
      | sum => rfl
      | op c j inp q t => exact absurd (hf.2.2.2.2.1 _ _ _ _ _ _ hR).1 (sumid.summaryId_ne_opId p c j)
    subst he
    ihave #Hel := bigSepM_lookup (Φ := fun x e => iprop(ghostMapElem γ.reg x .discard e))
      (i := summaryId p) hR $$ Hre
    imod Hclose $$ [Hauth Hputs Hra Hsa Hca Hce Hbody] with _
    · inext
      iunfold smrInv
      iexists D, Reg, Res, Cnt
      iframe # ∗
      ipureintro; exact hf
    imodintro
    unfold batchReg
    iexists RegEntry.sum
    iframe Hel
    ipureintro
    exact ⟨rfl, (fun h => by cases h), fun _ => ⟨p, rfl, hsp⟩, fun c j inp q t h => by cases h⟩
  | none =>
    imod ghost_map_insert_persist (summaryId p) RegEntry.sum hR $$ Hra with ⟨Hra, #Hel⟩
    have hf' := facts_register_sum D Reg Res Cnt p hsp hf hR
    have hnd := fresh_not_done D Reg Res Cnt _ hf hR
    imod Hclose $$ [Hauth Hputs Hra Hsa Hca Hce Hbody] with _
    · inext
      iunfold smrInv
      iexists D, <[summaryId p := RegEntry.sum]> Reg, Res, Cnt
      unfold putsOf
      rw [execLog_insert D Reg _ _ hnd]
      iframe Hauth Hdecs Hputs Hra Hsa Hse Hca Hce
      isplitl []
      · iapply (bigSepM_insert (Φ := fun x e => iprop(x ↪[γ.reg]□ e)) hR).2
        iframe # ∗
      isplitl []
      · ipureintro
        unfold SmrFacts at hf'
        rw [execLog_insert D Reg _ _ hnd] at hf'
        exact hf'
      iapply (bigSepM_insert hR).2
      iframe Hbody
    imodintro
    unfold batchReg
    iexists RegEntry.sum
    iframe Hel
    ipureintro
    exact ⟨rfl, (fun h => by cases h), fun _ => ⟨p, rfl, hsp⟩, fun c j inp q t h => by cases h⟩

/-- A replica executes its next decided slot `|D| + 1`, decided `ids`, with the batches `B` of
its store (each the registered one, for every id of the slots `1..|D|+1`): the executed prefix
grows to `D ++ [ids]` (another replica may have executed it first: then the requests are
committed already); every request first executed in that slot is committed (its atomic update,
at its turn) and has its answer: for each request `x` of `ids` (a batch with a sender other than
-1: not `"nil"`, not a summary) not executed by `D`, its results in the execution of `D ++ [ids]`
are one answer `r` with `opAns γ x r`. Two later credits strip the invariant's and the stored
update's laters. -/
theorem smr_exec_slot (γ : QNames) (D : List (List GoString)) (ids : List GoString)
    (B : GoString → Option Batch) :
    ⊢@{IProp GF} inv consN (consInv γ) -∗ inv smrN (smrInv γ) -∗ £ 2 -∗ execLb γ D -∗
      decided γ (D.length + 1) ids -∗
      ([∗list] x ∈ (D ++ [ids]).flatten, ∃ b, ⌜B x = some b ∧ msg.batchFit b⌝ ∗ batchReg γ x b) ={⊤}=∗
      execLb γ (D ++ [ids]) ∗
      ∀ x, ⌜x ∈ ids ∧ x ∉ (execLog B D).done ∧ ∃ b, B x = some b ∧ b.sender ≠ -1⌝ -∗
        ∃ r, ⌜(execLog B (D ++ [ids])).results x = some [r]⌝ ∗ opAns γ x r := by
  iintro #Hcons #Hsmr Hlc #Hlb #Hdec Hregs
  ihave ⟨Hlc1, Hlc2⟩ := (lc_split (n := 1) (m := 1)).1 $$ Hlc
  iinv Hsmr with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iunfold smrInv at Hi
  icases Hi with ⟨%Dg, %Reg, %Res, %Cnt, Hauth, #Hdecs, Hputs, Hra, #Hre, Hsa, #Hse, Hca, Hce,
    %hf, Hbody⟩
  iunfold execLb at Hlb
  ihave %hpre := mono_list_auth_lb_valid $$ Hauth Hlb
  ihave %hregs := regs_of_list γ Reg B _ $$ Hra Hregs
  obtain ⟨hf0, hf1, hf2, hfs, hf3, hf4, hf5, hf6⟩ := hf
  have hReg : RegOk Reg := ⟨hf2, fun x c j inp q t h => (hf3 x c j inp q t h).2.1,
    fun x h => by obtain ⟨p, rfl, -⟩ := hfs x h; exact sumid.summaryId_cmdPut p⟩
  -- `B` is the registry's on the log's ids
  have hB : ∀ x ∈ (D ++ [ids]).flatten, B x = regB Reg x := by
    intro x hx
    obtain ⟨e, he, hBx, _⟩ := hregs x hx
    simp [regB, he, hBx]
  have hexec : execLog B (D ++ [ids]) = execLog (regB Reg) (D ++ [ids]) :=
    execLog_congr _ _ _ hB
  have hexecD : execLog B D = execLog (regB Reg) D :=
    execLog_congr _ _ _ (fun x hx => hB x (by simp only [List.flatten_append, List.mem_append]; exact Or.inl hx))
  -- a new request of the slot is a registered request
  have hreq : ∀ x, x ∈ ids → (∃ b, B x = some b ∧ b.sender ≠ -1) →
      ∃ c j inp q tok, Reg !! x = some (.op c j inp q tok) := by
    intro x hx ⟨b, hBx, hsnd⟩
    obtain ⟨e, he, hBe, _⟩ := hregs x (by simp [hx])
    rw [hBx] at hBe; cases hBe
    cases e with
    | nil => exact absurd rfl hsnd
    | sum => exact absurd rfl hsnd
    | op c j inp q tok => exact ⟨c, j, inp, q, tok, he⟩
  obtain ⟨rest, hrest⟩ := hpre.2
  cases rest with
  | cons ids' rest =>
    -- another replica executed the slot already: it is `ids` (agreement)
    subst hrest
    ihave Hd' := bigSepL_lookup (Φ := fun k ids => iprop(decided γ (↑k + 1) ids)) (i := D.length)
      (x := ids') (by simp) $$ Hdecs
    imod decided_agree γ _ (by unfold consN smrN; solve_ndisj) _ _ _ $$ Hcons Hdec Hd' with %heq
    subst heq
    ihave #Hlb' := monoListLbOwn_get $$ Hauth
    imod Hclose $$ [Hauth Hputs Hra Hsa Hca Hce Hbody] with _
    · inext
      iunfold smrInv
      iexists _, Reg, Res, Cnt
      iframe # ∗
      ipureintro
      exact ⟨hf0, hf1, hf2, hfs, hf3, hf4, hf5, hf6⟩
    imodintro
    have happ : D ++ ids :: rest = (D ++ [ids]) ++ rest := by simp
    isplitr
    · iunfold execLb
      iapply monoListLbOwn_le (D ++ [ids]) (by rw [happ]; exact List.prefix_append _ _) $$ Hlb'
    iintro %x %hx'
    obtain ⟨hx, _, hsnd⟩ := hx'
    obtain ⟨c, j, inp, q, tok, hR⟩ := hreq x hx hsnd
    have hdone : x ∈ (execLog (regB Reg) (D ++ [ids])).done := (execLog_done _ _ _).2 (by simp [hx])
    have hdoneg : x ∈ (execLog (regB Reg) (D ++ ids :: rest)).done :=
      (execLog_done _ _ _).2 (by simp [hx])
    obtain ⟨o, hRes⟩ : ∃ o, Res !! x = some o :=
      Option.isSome_iff_exists.1 ((hf4 x).2 ⟨⟨c, j, inp, q, tok, hR⟩, hdoneg⟩)
    obtain ⟨c', j', inp', q', tok', hR', hres, hv⟩ := hf6 x o hRes
    rw [hR] at hR'
    cases hR'
    iexists ansOf inp o
    isplitr
    · ipureintro
      rw [hexec, ← execLog_results_prefix (regB Reg) (D ++ [ids]) rest x hdone, ← happ]
      exact hres
    iapply ans_of_res γ Reg Res x o c j inp q tok hR hRes hv $$ Hre Hse
  | nil =>
    -- this replica extends the global prefix: execute the slot under the invariant
    simp only [List.append_nil] at hrest
    subst hrest
    have hI0 := execInv_init Reg Res D hReg hf4 hf5 hf6
    have hids : ∀ x ∈ ids, ∃ e, Reg !! x = some e ∧ msg.batchFit (e.batch x) := by
      intro x hx
      obtain ⟨e, he, _, hok⟩ := hregs x (by simp [hx])
      exact ⟨e, he, hok⟩
    ihave Hbody := regBody_later γ Reg Res $$ Hbody
    imod lc_fupd_elim_later $$ Hlc2 Hbody with Hbody
    rw [putsOf_eq]
    imod exec_ids γ (⊤ \ ↑smrN) (raxos_mask smrN (.inl rfl)) Reg hReg ids Res _ hI0 hids
      $$ [Hputs Hsa Hbody] with ⟨%Res', %hI', H⟩
    · iunfold execRes
      iframe # ∗
    rw [← execLog_snoc] at hI'
    iunfold execRes at H
    icases H with ⟨Hputs, Hsa, #Hse', Hbody⟩
    imod monoListAuthOwn_update_app [ids] $$ Hauth with ⟨Hauth, #Hlb'⟩
    imod Hclose $$ [Hauth Hputs Hra Hsa Hca Hce Hbody] with _
    · inext
      iunfold smrInv
      iexists D ++ [ids], Reg, Res', Cnt
      rw [putsOf_eq, execLog_snoc]
      iframe Hauth Hputs Hra Hsa Hca Hce Hre Hse'
      isplitr
      · iapply (bigSepL_snoc (Φ := fun k ids => iprop(decided γ (↑k + 1) ids))).2
        iframe # ∗
      isplitr
      · ipureintro
        rw [← execLog_snoc]
        exact ⟨hf0, hf1, hf2, hfs, hf3, hI'.res_iff, hI'.done_ok, hI'.res_ok⟩
      iapply regBody_unlater $$ Hbody
    imodintro
    isplitr
    · iunfold execLb
      iexact Hlb'
    iintro %x %hx'
    obtain ⟨hx, _, hsnd⟩ := hx'
    obtain ⟨c, j, inp, q, tok, hR⟩ := hreq x hx hsnd
    have hdone : x ∈ (execLog (regB Reg) (D ++ [ids])).done := (execLog_done _ _ _).2 (by simp [hx])
    obtain ⟨o, hRes⟩ : ∃ o, Res' !! x = some o :=
      Option.isSome_iff_exists.1 ((hI'.res_iff x).2 ⟨⟨c, j, inp, q, tok, hR⟩, hdone⟩)
    obtain ⟨c', j', inp', q', tok', hR', hres, hv⟩ := hI'.res_ok x o hRes
    rw [hR] at hR'
    cases hR'
    iexists ansOf inp o
    isplitr
    · ipureintro
      rw [hexec]
      exact hres
    iapply ans_of_res γ Reg Res' x o c j inp q tok hR hRes hv $$ Hre Hse'

/-- Client `c`'s request counter's half (`n` requests registered). -/
def cntHalf (γ : QNames) (c n : Nat) : IProp GF := ghostMapElem γ.cnt c (DFrac.own (1 : Qp).half) n

/-- Request `x`, input `inp`, registered by the client with postcondition `Φ` of its output (saved); the
client's token to collect its output (exclusive). -/
def opPending (γ : QNames) (x : GoString) (inp : KIn)
    (Φ : KOut → IProp GF) :
    IProp GF :=
  iprop(∃ (c j : Nat) (q tok : GName), ghostMapElem γ.reg x .discard (RegEntry.op c j inp q tok) ∗
    savedPredOwn q .discard Φ ∗ token tok)

/-- `Op`: client `c` registers its `n`-th request (`opId c n`), an input the kit makes, with its
atomic update: its batch is registered. -/
theorem op_register (γ : QNames) (E : CoPset) (hE : ↑smrN ⊆ E) (c n : Nat)
    (hcn : c < 6 ∧ n < 20) (inp : KIn) (hinp : inputOk inp)
    (Φ : KOut → IProp GF) :
    ⊢@{IProp GF} inv smrN (smrInv γ) -∗ cntHalf γ c n -∗ opUpd γ inp Φ ={E}=∗
      cntHalf γ c (n + 1) ∗ batchReg γ (opId c n) ⟨opId c n, clientName c, [cmdOf inp]⟩ ∗
      opPending γ (opId c n) inp Φ := by
  iintro #Hsmr Hc HAU
  iinv Hsmr with Hi Hclose
  iunfold smrInv at Hi
  icases Hi with ⟨%D, %Reg, %Res, %Cnt, >Hauth, #Hdecs, >Hputs, >Hra, #Hre, >Hsa, #Hse, >Hca, >Hce,
    >%hf, Hbody⟩
  iunfold cntHalf at Hc
  ihave %hc := ghost_map_lookup $$ Hca Hc
  have hfr := reg_fresh D Reg Res Cnt c n hf hc
  have hf' := facts_register D Reg Res Cnt c n hcn inp hinp
  -- the counter: both halves, updated
  ihave ⟨Hc', Hce⟩ := (bigSepM_delete (Φ := fun c n => iprop(c ↪[γ.cnt]{#(1 : Qp).half} n))
    (i := c) hc).1 $$ Hce
  ihave Hcf : (c ↪[γ.cnt] n : IProp GF) $$ [Hc Hc']
  · iapply (ghostMapElem_halves γ.cnt c n).2
    iframe
  imod ghost_map_update (n + 1) $$ Hca Hcf with ⟨Hca, Hcf⟩
  ihave ⟨Hc, Hc'⟩ := (ghostMapElem_halves γ.cnt c (n + 1)).1 $$ Hcf
  -- the request's saved postcondition and collection token
  imod saved_pred_alloc Φ DFrac.discard
    DFrac.valid_discard with ⟨%q, #Hq⟩
  imod token_alloc with ⟨%tok, Htok⟩
  imod ghost_map_insert_persist (opId c n) (RegEntry.op c n inp q tok) hfr $$ Hra with ⟨Hra, #Hel⟩
  imod Hclose $$ [Hauth Hputs Hra Hsa Hca Hce Hc' Hbody HAU] with _
  · inext
    iunfold smrInv
    iexists D, <[opId c n := RegEntry.op c n inp q tok]> Reg, Res, <[c := n + 1]> Cnt
    have hnd := fresh_not_done D Reg Res Cnt _ hf hfr
    have hRes : Res !! opId c n = none := by
      cases h : Res !! opId c n with
      | none => rfl
      | some o =>
        obtain ⟨_, _, _, _, _, he⟩ := ((hf.2.2.2.2.2.1 _).1 (by rw [h]; rfl)).1
        rw [hfr] at he; cases he
    unfold putsOf
    rw [execLog_insert D Reg _ _ hnd]
    iframe Hauth Hdecs Hputs Hra Hsa Hse Hca
    isplitl []
    · iapply (bigSepM_insert (Φ := fun x e => iprop(x ↪[γ.reg]□ e)) hfr).2
      iframe # ∗
    isplitl [Hc' Hce]
    · iapply (bigSepM_insert_delete (Φ := fun c n => iprop(c ↪[γ.cnt]{#(1 : Qp).half} n))).2
      iframe
    isplitl []
    · ipureintro
      have := hf' q tok hf hc
      unfold SmrFacts at this
      rw [execLog_insert D Reg _ _ hnd] at this
      exact this
    iapply (bigSepM_insert hfr).2
    iframe Hbody
    iexists Φ
    iframe Hq
    rw [hRes]
    inext
    iexact HAU
  imodintro
  unfold cntHalf opPending batchReg
  iframe Hc
  isplitr
  · iexists _
    iframe Hel
    ipureintro
    refine ⟨rfl, (fun h => by cases h), (fun h => by cases h), ?_⟩
    intro c' j' inp' q' t' h
    cases h
    exact ⟨rfl, hcn.1, hinp⟩
  iexists c, n, q, tok
  iframe # ∗

/-- `Op` on an answer `r` to its request: the output `o` whose answer `r` is, and the commit's
postcondition (two later credits strip the invariant's and the stored postcondition's laters). -/
theorem op_collect (γ : QNames) (E : CoPset) (hE : ↑smrN ⊆ E) (x r : GoString)
    (inp : KIn)
    (Φ : KOut → IProp GF) :
    ⊢@{IProp GF} inv smrN (smrInv γ) -∗ £ 2 -∗ opPending γ x inp Φ -∗ opAns γ x r ={E}=∗
      ∃ o, ⌜r = ansOf inp o ∧ ∀ v, o = ⟨true, v⟩ → v ≠ [] ∧ v ≠ go!"nil"⌝ ∗ Φ o := by
  iintro #Hsmr Hlc HP HA
  ihave ⟨Hlc1, Hlc2⟩ := (lc_split (n := 1) (m := 1)).1 $$ Hlc
  unfold opPending opAns opDone
  icases HP with ⟨%c, %j, %q, %tok, #Hel, #Hq, Htok⟩
  icases HA with ⟨%c', %j', %inp', %q', %tok', %o, #Hel', #Hdone, %hr⟩
  ihave %he := ghostMapElem_agree $$ Hel Hel'
  cases he
  iinv Hsmr with Hi Hclose
  imod lc_fupd_elim_later $$ Hlc1 Hi with Hi
  iunfold smrInv at Hi
  icases Hi with ⟨%D, %Reg, %Res, %Cnt, Hauth, #Hdecs, Hputs, Hra, #Hre, Hsa, #Hse, Hca, Hce,
    %hf, Hbody⟩
  ihave %hR := ghost_map_lookup $$ Hra Hel
  ihave %hRes := ghost_map_lookup $$ Hsa Hdone
  ihave Hbody := regBodyL_of γ Reg Res $$ Hbody
  ihave ⟨Hx, Hbody⟩ := (bigSepM_delete (Φ := regBodyL γ Res) (i := x) hR).1 $$ Hbody
  iunfold regBodyL at Hx
  rw [show Res !! x = some o from hRes]
  icases Hx with ⟨%Φ', #Hq', (HQ | Htok')⟩
  · imod Hclose $$ [Hauth Hputs Hra Hsa Hca Hce Hbody Htok] with _
    · inext
      iunfold smrInv
      iexists D, Reg, Res, Cnt
      iframe # ∗
      isplitl []
      · ipureintro; exact hf
      iapply regBodyL_to
      iapply (bigSepM_delete (Φ := regBodyL γ Res) (i := x) hR).2
      iframe Hbody
      iunfold regBodyL
      rw [show Res !! x = some o from hRes]
      iexists Φ'
      iframe Hq'
      iright
      iexact Htok
    ihave Heq := saved_pred_agree q _ _ Φ Φ' o $$ Hq Hq'
    ihave HQ' : (▷ Φ o : IProp GF) $$ [Heq HQ]
    · inext
      iapply kit_internal_eq_rewrite_wand $$ Heq
      iexact HQ
    imod lc_fupd_elim_later $$ Hlc2 HQ' with HQ'
    imodintro
    iexists o
    iframe HQ'
    ipureintro
    exact ⟨hr.1, hr.2⟩
  · iexfalso
    iapply token_exclusive $$ Htok Htok'

end laws

end Perennial.raxos
