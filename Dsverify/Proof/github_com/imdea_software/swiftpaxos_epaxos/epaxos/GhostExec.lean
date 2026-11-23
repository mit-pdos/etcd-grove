/-
The executor's command step over the bodies (`ep_execCmd`, fix B8): the model's `execCmd`; if the
slot's op fires here (its first execution anywhere), its escrow fires from the abstract state
(`escrow_fire`, the second credit) and the reply carries the fired output; otherwise the reply
carries the output recorded at the first execution.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostSend
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecFacts

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

theorem clientConn_pre (γ : EpNames) (cid : Nat) (c : w64) (inp : KvI) :
    clientConn (GF := GF) γ cid c inp -∗ ⌜inPre inp⌝ := by
  iintro H; iunfold clientConn at H; icases H with ⟨%h, -⟩; ipureintro; exact h

/-- The ops' inputs meet the premise (read off their connections). -/
theorem ops_pre (γ : EpNames) (S : Sys) :
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

/-- The replies of a step that fired nothing carry fired outputs. -/
theorem replies_fired (γ : EpNames) (i : Nat) (F : GMap Nat KvO) (fd : Nat → Option KvO)
    (hF : ∀ cid, F.lookup cid = fd cid) (outs : List Out)
    (houts : ∀ o ∈ outs, ∃ p v, o = Out.reply p v)
    (hrep : ∀ p v, Out.reply p v ∈ outs → ∃ o, fd p.cid = some o ∧ replyValOk o v) :
    ([∗map] cid ↦ o ∈ F, fired (GF := GF) γ cid o) -∗
      ([∗map] cid ↦ o ∈ F, fired γ cid o) ∗ [∗list] o ∈ outs, outOkB γ i o := by
  induction outs with
  | nil => iintro H; iframe H; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons o os ih =>
    iintro H
    obtain ⟨p, v, rfl⟩ := houts o (by simp)
    obtain ⟨fo, hfo, hv⟩ := hrep p v (by simp)
    have hl : F.lookup p.cid = some fo := by rw [hF]; exact hfo
    ihave ⟨#Hf, Hcl⟩ := (BigSepM.bigSepM_lookup_acc hl).1 $$ H
    ihave H := Hcl $$ Hf
    ihave ⟨H, Hs⟩ := ih (fun o ho => houts o (List.mem_cons_of_mem _ ho))
      (fun p v h => hrep p v (List.mem_cons_of_mem _ h)) $$ H
    iframe H
    iapply BigSepL.bigSepL_cons.2
    iframe Hs
    unfold outOkB
    iexists fo
    iframe Hf
    ipureintro; exact hv

theorem replies_one (γ : EpNames) (i : Nat) (p : Proposal) (o' : KvO) :
    ∀ (outs : List Out), (∀ o ∈ outs, ∃ v, o = Out.reply p v ∧ replyValOk o' v) →
    fired (GF := GF) γ p.cid o' ⊢ [∗list] o ∈ outs, outOkB γ i o
  | [], _ => by iintro -; iapply BigSepL.bigSepL_nil.2; iempintro
  | o :: os, h => by
    obtain ⟨v, rfl, hv⟩ := h o (by simp)
    iintro #Hfo
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · unfold outOkB
      iexists o'
      iframe Hfo
      ipureintro; exact hv
    iapply replies_one γ i p o' os (fun o ho => h o (List.mem_cons_of_mem _ ho)) $$ Hfo

/-- A fact hidden from `simp [*]` (`iinv`'s side-condition solver). -/
@[irreducible] def hideP (P : Prop) : Prop := P

theorem ep_execCmdB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (x : InstId) (rest : List InstId) (w : InstRec) (idx : Nat)
    (hE : ↑N ⊆ E) (hEe : ↑escrowN ⊆ E) (hEc : ⊤ \ epEop ⊆ E)
    (hNe : (↑N : CoPset) ## ↑escrowN) (hNc : (↑N : CoPset) ⊆ epEop) (hi : i < nR)
    (hw : σ.inst x = some w) (hidx : idx < (w.cmds.getD []).length) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ curFragB γ i (x :: rest) idx -∗ £ 2 ={E}=∗
      repFragB γ i (execCmdAt σ w idx).1 ∗ curFragB γ i (x :: rest) (idx + 1) ∗
        [∗list] o ∈ (execCmdAt σ w idx).2, outOkB γ i o := by
  iintro #Hinv Hf Hc Hlc
  icases Hlc with ⟨Hlc1, Hlc2⟩
  have hk : hideP (σ.inst x = some w ∧ idx < (w.cmds.getD []).length ∧ ↑escrowN ⊆ E ∧
      (↑N : CoPset) ## ↑escrowN) := by
    unfold hideP; exact ⟨hw, hidx, hEe, hNe⟩
  clear hw hidx hEe hNe
  iinv Hinv with Hi Hclose
  obtain ⟨hw, hidx, hEe, hNe⟩ : σ.inst x = some w ∧ idx < (w.cmds.getD []).length ∧
      ↑escrowN ⊆ E ∧ (↑N : CoPset) ## ↑escrowN := by
    unfold hideP at hk; exact hk
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc1 Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, ⟨%F, HF, %hF, Hfm⟩, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hc := cur_agreeB γ S i _ _ $$ Ha Hc
  ihave %hops := ops_pre γ S $$ Hops
  subst hσ
  obtain ⟨hcur, hidx'⟩ := hc
  have hstep : Step S (S.execCmd i x w) :=
    Step.execCmd S i x rest w hi hcur hw (by rw [hidx']; exact hidx)
  have hS' := inv_step_execCmd S i x rest w hS hi hcur hw (by rw [hidx']; exact hidx)
  have hX' : InvX (S.execCmd i x w) :=
    ⟨NR_step hstep hX.1, fun y ps hy => hX.2 y ps (by rwa [execCmd_owner] at hy)⟩
  have hcrt := step_crt_mono S _ hS hstep i
  have hout := exec_outcome S i x rest w hS hS' hi hcur hw (by rw [hidx']; exact hidx) hops
  have hf := execCmd_fields S i x w
  rw [hidx'] at hout hf
  generalize S.execCmd i x w = S' at hS' hX' hcrt hout hf
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hf
  have hrep : S'.rep i = (execCmdAt (S.rep i) w idx).1 := by rw [f1]; simp
  imod ghost_rep_cur_step γ i S S' (S.rep i) (execCmdAt (S.rep i) w idx).1 (x :: rest)
    (x :: rest) idx (idx + 1) hi
    (fun j hj => ⟨by rw [f1]; simp [upd_other _ _ _ _ hj], by rw [f2], by rw [f3], by rw [f4],
      by rw [f5]; simp [upd_other _ _ _ _ hj], by rw [f6]⟩) hrep
    (fun q => by have := hcrt q; rwa [hrep] at this) (by rw [f2]) (by rw [f3])
    (by rw [f4, hcur]) (by rw [f5]; simp) (by rw [f6]) $$ Ha Hf Hc with ⟨Ha, Hf, Hc⟩
  have houts := execCmdAt_outs (S.rep i) w idx
  rcases hout with ⟨hkv, hfd, hrp⟩ | ⟨r, p, o, hpo, hnf, hfd, hkv, hrp⟩
  · -- nothing fired
    ihave ⟨Hfm, Houts⟩ := replies_fired γ i F S.fired hF _ houts hrp $$ Hfm
    imod Hclose $$ [Ha Hkv HF Hfm Hsents Hdel Hops] with -
    · inext
      iapply epInvB_close γ S S' hS' hX' hkv hfd f7 f8 f9 $$ Ha Hkv [HF Hfm] Hsents Hdel Hops
      iexists F
      iframe HF Hfm
      ipureintro; exact hF
    imodintro
    iframe
  · -- the slot's op fires here
    ihave ⟨⟨Hfr, %c, %inp, #Hcc, %hcmd⟩, Hops⟩ := BigSepL.bigSepL_mem_acc hpo $$ Hops
    have hFn : F.lookup p.cid = none := by rw [hF]; exact hnf
    have hEe' : ↑escrowN ⊆ E \ ↑N := fun q hq =>
      CoPset.in_diff.2 ⟨hEe q hq, fun h => hNe q ⟨h, hq⟩⟩
    have hEc' : ⊤ \ epEop ⊆ E \ ↑N := fun q hq =>
      CoPset.in_diff.2 ⟨hEc q hq, fun h => (CoPset.in_diff.1 hq).2 (hNc q h)⟩
    ihave %hpre := clientConn_pre γ p.cid c inp $$ Hcc
    imod escrow_fire γ (E \ ↑N) p.cid c inp S.kv F hEe' hEc' hFn $$ Hcc HF Hkv Hlc2
      with ⟨%σ', %o', %hst, Hkv, HF, Hfo⟩
    have hdet := kv_step_det S.kv inp _ _ _ _ hst (hkv inp hcmd hpre)
    obtain ⟨rfl, ho⟩ := hdet
    subst o'
    ihave #Hfo := (fired_persistent γ p.cid o).persistent $$ Hfo
    ihave Hops := Hops $$ [Hfr]
    · iframe Hfr
      iexists c, inp
      iframe Hcc
      ipureintro; exact hcmd
    imod Hclose $$ [Ha Hkv HF Hfm Hsents Hdel Hops] with -
    · inext
      iunfold epInvB
      iexists S'
      iframe Ha
      isplitr; · ipureintro; exact hS'
      isplitr; · ipureintro; exact hX'
      iframe Hkv
      rw [f7, f8, f9]
      iframe Hsents Hdel Hops
      iexists F.insert p.cid o
      iframe HF
      isplitr
      · ipureintro
        intro cid
        rw [hfd, upd_apply]
        by_cases e : cid = p.cid
        · subst e; rw [if_pos rfl]; exact GMap.lookup_insert F _ _
        · rw [if_neg e, GMap.lookup_insert_ne F o (Ne.symm e)]; exact hF cid
      iapply (BigSepM.bigSepM_insert (x := o) (show get? F p.cid = none from hFn)).2
      iframe Hfo Hfm
    imodintro
    iframe Hf Hc
    have : ∀ o' ∈ (execCmdAt (S.rep i) w idx).2, ∃ v, o' = Out.reply p v ∧ replyValOk o v := by
      intro o ho
      obtain ⟨p', v, rfl⟩ := houts o ho
      obtain ⟨rfl, hv⟩ := hrp p' v ho
      exact ⟨v, rfl, hv⟩
    iapply replies_one γ i p o _ this $$ Hfo

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
