/-
The delivery step (`ep_deliver`, over the bodies): the run loop takes message `n` from `fr`
(its `msgSent` fact and delivery token) and the ghost `Sys` takes the model's `deliver` step.
The variant also returns what the pre-state knows (`deliverPre`: the invariant, the message sent,
the replica's state), from which each handler's well-formedness facts follow purely.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostStep
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.NoReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecFacts

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem sendsToB_eq (outs : List Out) (to : Nat) :
    sendsToB outs to = outs.filterMap (Out.sendTo to) := by
  unfold sendsToB; congr 1

/-- What a delivery's ghost step knows of the system before the step. -/
def deliverPre [GooseExts] [GoGlobalContext] (fr i n : Nat) (m : Msg) (σ : RState) : Prop :=
  ∃ S : Sys, Inv S ∧ i < nR ∧ fr < nR ∧ S.idle i ∧ S.rep i = σ ∧ (S.sent fr i)[n]? = some m ∧
    (fr, i, n) ∉ S.delivered ∧ InvX S ∧ opsPre S

/-- A replica step `S' = S.applyStep i r` (after changes to untracked fields: `S1`) leaves the
other replicas' tracked fields. -/
theorem applyStep_sameAt (S S1 : Sys) (i j : Nat) (r : RState × List Out) (hj : j ≠ i)
    (h1 : sameAt S S1 j) : sameAt S (S1.applyStep i r) j := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h1
  obtain ⟨σ', os⟩ := r
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [upd_other _ _ _ _ hj, h1]
  · funext to; simp [hj, h2]
  · simp [hj, h3]
  · simp [h4]
  · simp [h5]
  · simp [hj, h6]

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The ops' inputs meet the premise (read off their connections; as `ops_pre`). -/
theorem ops_preD (γ : EpNames) (S : Sys) :
    ([∗list] o ∈ S.ops, connFresh o.2.cid true ∗
      ∃ (c : w64) (inp : KvI), clientConn (GF := GF) γ o.2.cid c inp ∗ ⌜o.2.cmd = cmdOf inp⌝) -∗
    ⌜opsPre S⌝ := by
  unfold opsPre
  generalize S.ops = ops
  induction ops with
  | nil => iintro -; ipureintro; simp
  | cons o os ih =>
    iintro H
    ihave ⟨⟨-, %c, %inp, Hc, %hc⟩, Hs⟩ := BigSepL.bigSepL_cons.1 $$ H
    iunfold clientConn at Hc
    icases Hc with ⟨%hpre, -⟩
    ihave %hs := ih $$ Hs
    ipureintro
    intro o' ho'
    rcases List.mem_cons.mp ho' with rfl | ho'
    · exact ⟨inp, hpre, hc⟩
    · exact hs o' ho'

theorem outOkB_of_toks (γ : EpNames) (i : Nat) (hi : i < nR) : ∀ (outs : List Out), noRep outs →
    ([∗list] p ∈ outs.filterMap Out.reprop, chanTok (GF := GF) γ i p) ⊢ [∗list] o ∈ outs, outOkB γ i o
  | [], _ => by iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | o :: os, h => by
    have hos : noRep os := fun o' ho' => h o' (List.mem_cons_of_mem _ ho')
    have ih := outOkB_of_toks γ i hi os hos
    cases o with
    | repropose p =>
      rw [show (Out.repropose p :: os).filterMap Out.reprop = p :: os.filterMap Out.reprop from rfl]
      iintro H
      ihave ⟨Hp, Hs⟩ := BigSepL.bigSepL_cons.1 $$ H
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hp]
      · unfold outOkB inChanB
        isplitr; · ipureintro; exact hi
        iexact Hp
      · iapply ih $$ Hs
    | reply p v => exact absurd (h (Out.reply p v) (by simp)) (by simp [Out.isReply])
    | send t m =>
      rw [show (Out.send t m :: os).filterMap Out.reprop = os.filterMap Out.reprop from rfl]
      iintro H
      iapply BigSepL.bigSepL_cons.2
      isplitr; · unfold outOkB; itrivial
      iapply ih $$ H
    | bcast b =>
      rw [show (Out.bcast b :: os).filterMap Out.reprop = os.filterMap Out.reprop from rfl]
      iintro H
      iapply BigSepL.bigSepL_cons.2
      isplitr; · unfold outOkB; itrivial
      iapply ih $$ H
    | ev e =>
      rw [show (Out.ev e :: os).filterMap Out.reprop = os.filterMap Out.reprop from rfl]
      iintro H
      iapply BigSepL.bigSepL_cons.2
      isplitr; · unfold outOkB; itrivial
      iapply ih $$ H

theorem sysAuthB_rep (γ : EpNames) (S : Sys) (i : Nat) (σ : RState) (hi : i < nR) :
    sysAuthB (GF := GF) γ S -∗ repFragB γ i σ -∗ ⌜S.rep i = σ⌝ := by
  iintro Ha Hf
  ihave ⟨Hi, -⟩ := sysAuthB_acc γ S i hi $$ Ha
  iapply rep_agree $$ Hi Hf

theorem sysAuthB_idle (γ : EpNames) (S : Sys) (i : Nat) (hi : i < nR) :
    sysAuthB (GF := GF) γ S -∗ repIdleB γ i -∗
      ⌜S.pending i = none ∧ S.execCur i = [] ∧ S.execIdx i = 0⌝ := by
  iintro Ha Hidle
  ihave ⟨Hi, -⟩ := sysAuthB_acc γ S i hi $$ Ha
  iunfold sysAuthRepB at Hi
  iunfold repIdleB at Hidle
  icases Hi with ⟨-, -, Hpd, Hcu, -⟩
  icases Hidle with ⟨-, Hpdf, Hcuf⟩
  iunfold pendFragB at Hpdf
  iunfold curFragB at Hcuf
  icases Hpdf with ⟨-, Hpdf⟩
  icases Hcuf with ⟨-, Hcuf⟩
  ihave %h1 := gvar_agree _ _ _ $$ Hpd Hpdf
  ihave %h2 := gvar_agree _ _ _ $$ Hcu Hcuf
  ipureintro
  exact ⟨h1, (Prod.mk.inj h2).1, (Prod.mk.inj h2).2⟩

theorem sents_lookup (γ : EpNames) (S : Sys) (fr to n : Nat) (m : Msg) (hfr : fr < nR)
    (hto : to < nR) (hne : fr ≠ to) :
    ([∗list] fr' ∈ List.range nR, [∗list] to' ∈ List.range nR,
      if fr' = to' then iprop(True) else sentHalf (GF := GF) γ fr' to' (S.sent fr' to')) -∗
      msgSent γ fr to n m -∗ ⌜(S.sent fr to)[n]? = some m⌝ := by
  iintro H #Hs
  ihave Hrow := BigSepL.bigSepL_lookup (range_getElem? hfr) $$ H
  ihave Hc := BigSepL.bigSepL_lookup (range_getElem? hto) $$ Hrow
  rw [if_neg hne]
  iapply sentHalf_lookup $$ Hc Hs

theorem deliv_fresh (γ : EpNames) (S : Sys) (fr to n : Nat) :
    ([∗list] d ∈ S.delivered, delivTok (GF := GF) γ d.2.1 d.1 d.2.2) -∗ delivTok γ to fr n -∗
      ⌜(fr, to, n) ∉ S.delivered⌝ := by
  iintro H Ht %hmem
  ihave ⟨Hd, -⟩ := BigSepL.bigSepL_mem_acc hmem $$ H
  iapply delivTok_excl $$ Hd Ht

theorem ep_deliverB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (fr n : Nat) (m : Msg) (hE : ↑N ⊆ E) (hi : i < nR) (hfr : fr < nR) (hne : fr ≠ i) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ repIdleB γ i -∗ msgSent γ fr i n m -∗
      delivTok γ i fr n -∗ £ 1 ={E}=∗
      ⌜deliverPre fr i n m σ⌝ ∗ repFragB γ i (hMsg σ m).1 ∗ outsOkB γ i (hMsg σ m).2 := by
  iintro #Hinv Hf Hidle #Hsent Htok Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hid := sysAuthB_idle γ S i hi $$ Ha Hidle
  ihave %hm := sents_lookup γ S fr i n m hfr hi hne $$ Hsents Hsent
  ihave %hnd := deliv_fresh γ S fr i n $$ Hdel Htok
  have hidle : S.idle i := ⟨hid.1, hid.2.1⟩
  have hstep : Step S (S.deliver fr i n m) := Step.deliver S fr i n m hi hfr hidle hm hnd
  have hS' : Inv (S.deliver fr i n m) := inv_step_deliver S fr i n m hS hi hfr hidle hm hnd
  have hX' : InvX (S.deliver fr i n m) :=
    ⟨NR_step hstep hX.1, fun y ps hy => hX.2 y ps (by
      unfold Sys.deliver at hy; rwa [applyStep_owner'] at hy)⟩
  ihave %hops := ops_preD γ S $$ Hops
  have hcrt := step_crt_mono S _ hS hstep i
  generalize hS'def : S.deliver fr i n m = S' at hstep hS' hX' hcrt
  have eS' : S' = { S with delivered := S.delivered ++ [(fr, i, n)] }.applyStep i
      ((hMsg σ m).1, (hMsg σ m).2) := by rw [← hS'def, ← hσ]; rfl
  have hrest : ∀ j, j ≠ i → sameAt S S' j := fun j hj => by
    rw [eS']
    exact applyStep_sameAt _ _ i j _ hj ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hrep : S'.rep i = (hMsg σ m).1 := by rw [eS']; simp
  have hcrt' : ∀ q, zz (σ.crtInstance q) ≤ zz ((hMsg σ m).1.crtInstance q) := fun q => by
    have := hcrt q; rwa [hσ, hrep] at this
  have hout : ∀ to, S'.outbox i to = S.outbox i to ++ sendsToB (hMsg σ m).2 to := fun to => by
    rw [eS', sendsToB_eq]; simp
  have hpend : S'.pending i = pendOf (hMsg σ m).2 := by
    rw [eS', pendOf_eq]; simp [hid.1]
  have hcur : S'.execCur i = S.execCur i ∧ S'.execIdx i = S.execIdx i := by
    rw [eS']; simp
  have hchan : S'.proposeChan i = S.proposeChan i ++ (hMsg σ m).2.filterMap Out.reprop := by
    rw [eS']; simp
  imod ghost_step_idle γ i S S' σ (hMsg σ m).1 (hMsg σ m).2 hi hrest hrep hcrt' hout hpend hcur
    hchan $$ Ha Hf Hidle with ⟨-, Ha, Hf, Hob, Hpd, Hcu, Htoks⟩
  have ekv : S'.kv = S.kv := by rw [eS']; unfold Sys.kv; simp
  have efired : S'.fired = S.fired := by rw [eS']; simp
  have esent : S'.sent = S.sent := by rw [eS']; simp
  have edel : S'.delivered = S.delivered ++ [(fr, i, n)] := by rw [eS']; simp
  have eops : S'.ops = S.ops := by rw [eS']; simp
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Htok Hops] with -
  · inext
    iunfold epInvB
    iexists S'
    iframe Ha
    isplitr; · ipureintro; exact hS'
    isplitr; · ipureintro; exact hX'
    rw [ekv, efired, esent, edel, eops]
    iframe Hkv Hfired Hsents Hops
    iapply BigSepL.bigSepL_snoc.2
    iframe
  imodintro
  isplitr
  · ipureintro; exact ⟨S, hS, hi, hfr, hidle, hσ, hm, hnd, hX, hops⟩
  iframe Hf
  iunfold outsOkB
  iframe Hob Hpd Hcu
  iapply outOkB_of_toks γ i hi _ (hMsg_noRep σ m) $$ Htoks

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
