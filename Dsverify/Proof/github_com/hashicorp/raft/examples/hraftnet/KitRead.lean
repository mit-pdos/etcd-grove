/-
# Reads outside the log at the frontier (notes/dsv-hraft.md, S6)

A read outside the log (`API.Read`) returns the register of its server's store, the register after some
committed prefix `es_r` that the frontier has passed, possibly long ago. Its update (a read's `□ lin`) must
fire when the model's state is that register, which is when the frontier passed `es_r`, on another thread.
So reads are helped: a read registers in the frontier's read escrow (`KitQ.lean`, `rdsQ`) at the frontier
`es0` (`kit_rdReg`, on the server's thread, after the client's call began), fired there; every frontier step
fires it again (`rds_step`), recording the outputs; once the server has read its store, the read claims
the output recorded at `es_r` (`kit_rdClaim`), which is `Φ` of `es_r`'s register: `es_r` is at least as long
as `es0`, by the read bound the server proves (`API.Read`: its `noCmdBetween` premise).

`kit_rdReg` also gives a gprot snapshot `sc` that covers the frontier (`|es0| ≤ sc.maxDur`, from `frDur`), the
snapshot the server gives `Barrier` (or `CurrentTerm`, then `VerifyLeader`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.KitQ
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open github_com.hashicorp.raft github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot
open service (regOf cIdxs)

section pure
variable [GooseExts]

/-- A read's output is the register's answer (found, value), when the register is short. -/
theorem readOut_eq (i : HIn) (hw : i.1.1 = false) (st : service.Reg) (h : regShort st) :
    (regB.step i st).2.1 = (st.isSome, st.getD []) := by
  simp only [regB, hw, Bool.false_eq_true, ↓reduceIte]
  have hlen : (regOut st).2.length < 256 := by
    unfold regOut
    cases hs : st with
    | none => simp
    | some v => exact h v hs
  rw [bndO_of hlen]
  rfl

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **A registered read's claim** (input `i`, continuation `Φ`, registered at the frontier of length
`n0`): its entry in the read escrow (persistent), the saved continuation and the reader's token. -/
def rdTicket (g : KG) (i : HIn) (Φ : HOut → IProp GF) (n0 : Nat) : IProp GF :=
  iprop(∃ (j : Nat) (γt γΦ : GName), monoListIdxOwn g.rd j ((γt, γΦ, i, n0) : RdX) ∗
    savedPredOwn γΦ .discard Φ ∗ token γt)

/-- **A snapshot of now covers the frontier** (`frDur`: a server's durable prefix covers it). -/
theorem frDur_snap (γ : GNames) (es : RLog) :
    Inv (GF := GF) γ ∗ service.frDur γ es ⊢
      |={⊤ \ ↑service.frN}=> ∃ sc : Snap, histLb γ sc ∗ ⌜es.length ≤ sc.maxDur⌝ := by
  iintro ⟨#Hinv, #Hfd⟩
  unfold service.frDur
  icases Hfd with (%h0 | ⟨%j, #Hj, #Hd⟩)
  · subst h0
    imod histLb_now γ _ frN_gprotN [] [] (by simp) $$ [Hinv] with ⟨%sc, #Hsc, -⟩
    · iframe Hinv
      isplitl
      · iapply BigSepL.bigSepL_nil.2; itrivial
      · iapply BigSepL.bigSepL_nil.2; itrivial
    imodintro
    iexists sc
    iframe Hsc
    ipureintro; simp
  · imod isSrv_mem γ _ frN_gprotN j $$ [Hinv Hj] with %hj
    · iframe #
    imod histLb_now γ _ frN_gprotN [] [(j, es.length)] (by simp [hj]) $$ [Hinv Hd] with
      ⟨%sc, #Hsc, %hsc⟩
    · iframe Hinv
      isplitl
      · iapply BigSepL.bigSepL_nil.2; itrivial
      · iapply BigSepL.bigSepL_singleton.2; iexact Hd
    imodintro
    iexists sc
    iframe Hsc
    ipureintro
    have h1 := hsc.2 (j, es.length) (by simp)
    have h2 := Snap.dur_le_maxDur sc j
    simp only at h1
    omega

/-- **A read registers at the frontier** `es0` (on the server's thread, in the API's deposit, after the
client's call began): fired at `es0`'s register, its entry appended to the read escrow; with a snapshot of
now covering the frontier (for `Barrier`/`VerifyLeader`), and `es0`'s facts (committed, ending with a
command), for the claim. -/
theorem kit_rdReg (γ : GNames) (g : KG) (fr : GName) (i : HIn) (Φ : HOut → IProp GF)
    (hw : i.1.1 = false) :
    service.frInv γ (kitFC γ g fr) ∗ £ 1 ∗ □ lin (Gg := hG.goose_globalGS) (regR g.st) i Φ ⊢
      |={⊤}=> ∃ (es0 : RLog) (sc : Snap), histLb γ sc ∗
        ⌜es0.length ≤ sc.maxDur ∧ service.lastCmd es0⌝ ∗ cIdxs γ es0 ∗ rdTicket g i Φ es0.length := by
  iintro ⟨#Hfr, Hlc, #Hlin⟩
  unfold service.frInv
  iinv Hfr with ⟨%es, >Hauth, >#Hc, >%Hlast, >#Hfd, HQ⟩ Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑service.frN) $$ Hlc HQ with HQ
  simp only [kitFC]
  unfold kitQ
  icases HQ with ⟨%M, %E, #Hinv, Hops, HE, Hst, %hpure, Hents, HR⟩
  iunfold rdsQ at HR
  icases HR with ⟨%RS, HRa, HRs⟩
  imod frDur_snap γ es $$ [Hinv Hfd] with ⟨%sc, #Hsc, %hsc⟩
  · iframe #
  have hmask : (⊤ \ kitE : CoPset) ⊆ ⊤ \ ↑service.frN := by unfold kitE; solve_ndisj
  imod fupd_mask_subseteq (PROP := IProp GF) hmask with Hcm
  imod read_fire g.st i Φ (regOf es) hw $$ [$Hlin $Hst] with ⟨Hst, HΦ0⟩
  imod Hcm
  imod token_alloc (GF := GF) with ⟨%γt, Ht⟩
  imod saved_pred_alloc (GF := GF) Φ DFrac.discard DFrac.valid_discard with ⟨%γΦ, #HΦ⟩
  imod monoListAuthOwn_update_app (A := RdX) [((γt, γΦ, i, es.length) : RdX)] $$ HRa with ⟨HRa, #Hlb⟩
  ihave #Hidx := monoListIdxOwn_get (A := RdX) RS.length ((γt, γΦ, i, es.length) : RdX)
    (by simp) $$ Hlb
  imod Hclose $$ [Hauth Hops HE Hst Hents HRa HRs HΦ0] with -
  · inext
    iexists es
    iframe Hauth Hc Hfd
    isplitr
    · ipureintro; exact Hlast
    iexists M, E
    iframe Hinv Hops HE Hst Hents
    isplitr
    · ipureintro; exact hpure
    unfold rdsQ
    iexists RS ++ [((γt, γΦ, i, es.length) : RdX)]
    iframe HRa
    iapply BigSepL.bigSepL_snoc.2
    iframe HRs
    unfold rdEnt
    iexists Φ, [es.length]
    iframe HΦ Hlin
    isplitr
    · ipureintro
      refine ⟨hw, ?_, ?_⟩
      · intro k hk; simp at hk; omega
      · intro k h1 h2 _; simp at h1 ⊢; omega
    iright
    iapply BigSepL.bigSepL_singleton.2
    rw [List.take_length]
    iexact HΦ0
  imodintro
  iexists es, sc
  iframe Hsc Hc
  isplitr
  · ipureintro; exact ⟨hsc, Hlast⟩
  unfold rdTicket
  iexists RS.length, γt, γΦ
  iframe Hidx HΦ Ht

/-- **A read claims its output** at the store's prefix `es` (which the frontier has passed, ending with
a command): the read bound says no command lies in `(k0, k]`, `k0 ≤ |es|` and the registration frontier
`es0` is within `k`, so `|es0| ≤ k0 ≤ |es|` (`cmd_not_between`) and the read was fired at `es`: `Φ` of
`es`'s register. -/
theorem kit_rdClaim (γ : GNames) (g : KG) (fr : GName) (i : HIn) (Φ : HOut → IProp GF)
    (es0 es : RLog) (k0 k : Nat) (h0 : service.lastCmd es0)
    (h : service.lastCmd es ∧ k0 ≤ es.length ∧ es0.length ≤ k) :
    service.frInv γ (kitFC γ g fr) ∗ £ 1 ∗ £ 1 ∗ cIdxs γ es0 ∗ rdTicket g i Φ es0.length ∗
      noCmdBetween γ k0 (k + 1) ∗ service.frLb (kitFC γ g fr) es ⊢
      |={⊤}=> ∃ out : HOut, ⌜out.1 = ((regOf es).isSome, (regOf es).getD [])⌝ ∗ Φ out := by
  iintro ⟨#Hfr, Hlc1, Hlc2, #Hc0, Htk, #Hnc, #Hlb⟩
  obtain ⟨hl, hk0, hk⟩ := h
  ihave %hle := service.cmd_not_between γ es0 k0 k h0 hk $$ [Hc0 Hnc]
  · iframe #
  unfold rdTicket
  icases Htk with ⟨%j, %γt, %γΦ, #Hidx, #HΦ, Ht⟩
  unfold service.frInv
  iinv Hfr with ⟨%esf, >Hauth, >#Hc, >%Hlast, >#Hfd, HQ⟩ Hclose
  imod lc_fupd_elim_later (E := ⊤ \ ↑service.frN) $$ Hlc1 HQ with HQ
  unfold service.frLb
  simp only [kitFC]
  ihave %Hpre := mono_list_auth_lb_valid fr 1 esf es $$ Hauth Hlb
  obtain ⟨-, hpre⟩ := Hpre
  unfold kitQ
  icases HQ with ⟨%M, %E, #Hinv, Hops, HE, Hst, %hpure, Hents, HR⟩
  iunfold rdsQ at HR
  icases HR with ⟨%RS, HRa, HRs⟩
  ihave %hx := mono_list_auth_idx_lookup g.rd 1 RS j _ $$ HRa Hidx
  icases (BigSepL.bigSepL_lookup_acc hx).1 $$ HRs with ⟨Hx, Hback⟩
  unfold rdEnt
  icases Hx with ⟨%Φ', %ks, #HΦ', #Hlin', %hp, Hr⟩
  simp only at hp
  obtain ⟨hw, hks, hall⟩ := hp
  have hm : es.length ∈ ks := by
    have hlen := hpre.length_le
    have htake : esf.take es.length = es := by
      rw [List.prefix_iff_eq_take] at hpre; exact hpre.symm
    exact hall es.length (by omega) hlen (by rw [htake]; exact hl)
  icases Hr with (Ht' | Hks)
  · iexfalso
    iapply token_exclusive $$ Ht Ht'
  ihave HΦo := BigSepL.bigSepL_mem hm $$ Hks
  have htake : esf.take es.length = es := by
    rw [List.prefix_iff_eq_take] at hpre; exact hpre.symm
  rw [htake]
  have hjl : j < RS.length := (List.getElem?_eq_some_iff.1 hx).1
  have hset : RS.set j ((γt, γΦ, i, es0.length) : RdX) = RS := by
    have := (List.getElem?_eq_some_iff.1 hx).2
    rw [← this]; exact List.set_getElem_self hjl
  imod Hclose $$ [Hauth Hops HE Hst Hents HRa Hback Ht] with -
  · inext
    iexists esf
    iframe Hauth Hc Hfd
    isplitr
    · ipureintro; exact Hlast
    iexists M, E
    iframe Hinv Hops HE Hst Hents
    isplitr
    · ipureintro; exact hpure
    unfold rdsQ
    iexists RS
    iframe HRa
    ispecialize Hback $$ %((γt, γΦ, i, es0.length) : RdX)
    rw [hset]
    unfold rdEnt
    iapply Hback
    iexists Φ', ks
    simp only
    iframe HΦ' Hlin'
    isplitr
    · ipureintro; exact ⟨hw, hks, hall⟩
    ileft; iexact Ht
  ihave Heq := saved_pred_agree γΦ _ _ Φ Φ' (regB.step i (regOf es)).2 $$ HΦ HΦ'
  ihave HΦ1 : (▷ Φ (regB.step i (regOf es)).2 : IProp GF) $$ [Heq HΦo]
  · inext
    iapply kit_internal_eq_rewrite $$ Heq
    iexact HΦo
  imod lc_fupd_elim_later $$ Hlc2 HΦ1 with HΦ1
  imodintro
  iexists (regB.step i (regOf es)).2
  iframe HΦ1
  ipureintro
  exact readOut_eq i hw _ (regShort_of_putsShort _ (putsShort_prefix hpre hpure.2))

end defs

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
