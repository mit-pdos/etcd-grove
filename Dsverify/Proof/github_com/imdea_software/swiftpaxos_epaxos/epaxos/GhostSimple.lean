/-
The ghost steps that change only a replica's state and its executor's progress: `BeTheLeader`,
the peer order, the executor's component start, instance end and `ExecedUpTo` bump (over the
bodies).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostRep

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- Close the invariant at a system `S'` that agrees with `S` on what the invariant's other parts
speak of. -/
theorem epInvB_close (γ : EpNames) (S S' : Sys) (hS' : Inv S') (hX' : InvX S') (hkv : S'.kv = S.kv)
    (hf : S'.fired = S.fired) (hs : S'.sent = S.sent) (hd : S'.delivered = S.delivered)
    (ho : S'.ops = S.ops) :
    sysAuthB (GF := GF) γ S' -∗ kvHalf γ S.kv -∗
    (∃ F : GMap Nat KvO, firedAuth γ F ∗ ⌜∀ cid, F.lookup cid = S.fired cid⌝ ∗
      [∗map] cid ↦ o ∈ F, fired γ cid o) -∗
    ([∗list] fr ∈ List.range nR, [∗list] to ∈ List.range nR,
      if fr = to then iprop(True) else sentHalf γ fr to (S.sent fr to)) -∗
    ([∗list] d ∈ S.delivered, delivTok γ d.2.1 d.1 d.2.2) -∗
    ([∗list] o ∈ S.ops, connFresh o.2.cid true ∗
      ∃ (c : w64) (inp : KvI), clientConn γ o.2.cid c inp ∗ ⌜o.2.cmd = cmdOf inp⌝) -∗
    epInvB γ := by
  iintro Ha Hkv Hf Hs Hd Ho
  iunfold epInvB
  iexists S'
  iframe Ha
  isplitr; · ipureintro; exact hS'
  isplitr; · ipureintro; exact hX'
  rw [hkv, hf, hs, hd, ho]
  iframe

theorem ep_beTheLeaderB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (hE : ↑N ⊆ E) (hi : i < nR) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ £ 1 ={E}=∗ repFragB γ i (hBeTheLeader σ) := by
  iintro #Hinv Hf Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  subst hσ
  have hS' := inv_step_beTheLeader S i hS hi
  imod ghost_rep_step γ i S { S with rep := upd S.rep i (hBeTheLeader (S.rep i)) } (S.rep i)
    (hBeTheLeader (S.rep i)) hi
    (fun j hj => ⟨by simp [upd_other _ _ _ _ hj], rfl, rfl, rfl, rfl, rfl⟩) (by simp)
    (fun q => Int.le_refl _) rfl rfl rfl rfl rfl $$ Ha Hf with ⟨Ha, Hf⟩
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S _ hS' (InvX_rep_upd (σ' := hBeTheLeader (S.rep i)) hX (NoneRec.NR_of_inst rfl (hX.1 i)) rfl rfl) rfl rfl rfl rfl rfl $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  iexact Hf

theorem ep_peerOrderB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (o : List Nat) (hE : ↑N ⊆ E) (hi : i < nR) (ho : Sys.peerOrderOk i o) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ £ 1 ={E}=∗
      repFragB γ i { σ with peerOrder := o } := by
  iintro #Hinv Hf Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  subst hσ
  have hS' := inv_step_peerOrder S i o hS hi ho
  imod ghost_rep_step γ i S { S with rep := upd S.rep i { S.rep i with peerOrder := o } } (S.rep i)
    { S.rep i with peerOrder := o } hi
    (fun j hj => ⟨by simp [upd_other _ _ _ _ hj], rfl, rfl, rfl, rfl, rfl⟩) (by simp)
    (fun q => Int.le_refl _) rfl rfl rfl rfl rfl $$ Ha Hf with ⟨Ha, Hf⟩
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S _ hS' (InvX_rep_upd (σ' := { S.rep i with peerOrder := o }) hX (NoneRec.NR_of_inst rfl (hX.1 i)) rfl rfl) rfl rfl rfl rfl rfl $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  iexact Hf

theorem ep_execBumpB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState) (q : Nat)
    (hE : ↑N ⊆ E) (hi : i < nR) (hq : q < nR)
    (he : σ.executed ⟨q, toN (σ.execedUpTo q + 1)⟩) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ £ 1 ={E}=∗ repFragB γ i (execBump σ q) := by
  iintro #Hinv Hf Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  subst hσ
  have hS' := inv_step_execBump S i q hS hi hq he
  imod ghost_rep_step γ i S { S with rep := upd S.rep i (execBump (S.rep i) q) } (S.rep i)
    (execBump (S.rep i) q) hi
    (fun j hj => ⟨by simp [upd_other _ _ _ _ hj], rfl, rfl, rfl, rfl, rfl⟩) (by simp)
    (fun q => Int.le_refl _) rfl rfl rfl rfl rfl $$ Ha Hf with ⟨Ha, Hf⟩
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S _ hS' (InvX_rep_upd (σ' := execBump (S.rep i) q) hX (NoneRec.NR_of_inst rfl (hX.1 i)) rfl rfl) rfl rfl rfl rfl rfl $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  iexact Hf

theorem ep_execSCCB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (C : List InstId) (hE : ↑N ⊆ E) (hi : i < nR) (hC : sccReady σ C) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗ pendFragB γ i none -∗ curFragB γ i [] 0 -∗
      £ 1 ={E}=∗ repFragB γ i σ ∗ pendFragB γ i none ∗ curFragB γ i (sccSort σ C) 0 := by
  iintro #Hinv Hf Hp Hc Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hp := pend_agreeB γ S i none $$ Ha Hp
  ihave %hc := cur_agreeB γ S i [] 0 $$ Ha Hc
  subst hσ
  have hS' := inv_step_execSCC S i C hS hi ⟨hp, hc.1⟩ hC
  imod ghost_rep_cur_step γ i S (S.startSCC i C) (S.rep i) (S.rep i) [] (sccSort (S.rep i) C) 0 0
    hi (fun j hj => ⟨rfl, rfl, rfl, by simp [Sys.startSCC, upd_other _ _ _ _ hj],
      by simp [Sys.startSCC, upd_other _ _ _ _ hj], rfl⟩) rfl (fun q => Int.le_refl _) rfl rfl
    (by simp [Sys.startSCC]) (by simp [Sys.startSCC]) rfl $$ Ha Hf Hc with ⟨Ha, Hf, Hc⟩
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S _ hS' (InvX_rep_eq hX rfl rfl) rfl rfl rfl rfl rfl $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  iframe

theorem ep_instDoneB (γ : EpNames) (N : Namespace) (E : CoPset) (i : Nat) (σ : RState)
    (x : InstId) (rest : List InstId) (w : InstRec) (hE : ↑N ⊆ E) (hi : i < nR)
    (hw : σ.inst x = some w) :
    ⊢ inv N (epInvB (GF := GF) γ) -∗ repFragB γ i σ -∗
      curFragB γ i (x :: rest) (w.cmds.getD []).length -∗ £ 1 ={E}=∗
      repFragB γ i (execDone σ x) ∗ curFragB γ i rest 0 := by
  iintro #Hinv Hf Hc Hlc
  iinv Hinv with Hi Hclose
  imod lc_fupd_elim_later (E := E \ ↑N) $$ Hlc Hi with Hi
  iunfold epInvB at Hi
  icases Hi with ⟨%S, Ha, %hS, %hX, Hkv, Hfired, Hsents, Hdel, Hops⟩
  ihave %hσ := sysAuthB_rep γ S i σ hi $$ Ha Hf
  ihave %hc := cur_agreeB γ S i _ _ $$ Ha Hc
  subst hσ
  have hS' := inv_step_instDone S i x rest w hS hi hc.1 hw hc.2
  have hcrt : ∀ q, zz ((S.rep i).crtInstance q) ≤ zz ((execDone (S.rep i) x).crtInstance q) := by
    intro q; unfold execDone; rw [hw]; exact Int.le_refl _
  imod ghost_rep_cur_step γ i S (S.instDone i x rest) (S.rep i) (execDone (S.rep i) x) _ rest _ 0
    hi (fun j hj => ⟨by simp [Sys.instDone, upd_other _ _ _ _ hj], rfl, rfl,
      by simp [Sys.instDone, upd_other _ _ _ _ hj], by simp [Sys.instDone, upd_other _ _ _ _ hj],
      rfl⟩) (by simp [Sys.instDone]) hcrt rfl rfl
    (by simp [Sys.instDone]) (by simp [Sys.instDone]) rfl $$ Ha Hf Hc with ⟨Ha, Hf, Hc⟩
  imod Hclose $$ [Ha Hkv Hfired Hsents Hdel Hops] with -
  · inext
    iapply epInvB_close γ S _ hS' (InvX_rep_upd hX (NoneRec.execDone_NR (hX.1 i) x) rfl rfl) rfl rfl rfl rfl rfl $$ Ha Hkv Hfired Hsents Hdel Hops
  imodintro
  iframe

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
