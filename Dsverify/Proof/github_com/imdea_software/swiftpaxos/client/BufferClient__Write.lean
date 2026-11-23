/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/BufferClient__Write.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.client.BufferClient__Write
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.AuLemmas
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Ghost

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [client.Assumptions]

theorem client.BufferClient.Write.wp_proofI
    (wp_SendWrite : client.Client.SendWrite.specI (hG := hG))
    (wp_theGhost : client.theGhost.specG (hG := hG))
    (wp_Invoke : client.Ghost.Invoke.specG (hG := hG))
    (wp_Accept : client.Ghost.Accept.specG (hG := hG)) :
    client.BufferClient.Write.specI (hG := hG) := by
  intro b γ γc γm γl cid s key vsl v
  iintro #Hpkg Hready #Hv %Hb
  unfold atomic_wp
  iintro %Φ AU
  ihave Hready := (client.ready_unfold _ _ _ _ _ _ _).1 $$ Hready
  icases Hready with ⟨%bv, %cl, %N, %γch, %γd, #Hbv, %Hcl, Hseq, Hsend, #Hinv, Hcs, Htoks, #Hbag, #Hng, #Hreg⟩
  ihave HAU : sp.cmdAU γl (sp.Cmd.put key v)
      (fun _ => iprop(client.ready b γ γc γm γl cid (s + 1) -∗ Φ #())) $$ [AU]
  · unfold sp.cmdAU
    iapply aupd_mono ?_ ?_ $$ AU
    · rintro ⟨σ, ⟨⟩⟩ ⟨⟩; exact .rfl
    · rintro ⟨σ, ⟨⟩⟩ ⟨⟩; exact .rfl
  have hs : (W32 (s : Int)).toNat = s := by word
  ihave Hcs : sp.clientSeq γ cid (W32 (s : Int)).toNat $$ [Hcs]
  · rw [hs]; iexact Hcs
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_theGhost γ (sp.PNode.cl (cid.toNat - 1)) $$ [] as %g #Hg
  · iframe #
  ihave #Hg1 : client.isNodeGhost γ (sp.PNode.cl (sp.clOf (⟨cid, W32 (s : Int)⟩ : sp.CmdId))) g $$ []
  · rw [show sp.clOf (⟨cid, W32 (s : Int)⟩ : sp.CmdId) = cid.toNat - 1 from rfl]; iexact Hg
  try wp_auto
  ihave #Hbf := Hbv
  iStructNamed Hbf
  obtain ⟨Hcl1, Hcl2, Hcid⟩ := Hcl
  subst Hcl1
  iunfold client.sendSt at Hsend
  icases Hsend with ⟨%lg, %ld, %ssl, %wsl, %wrs, #Hcidf, Hrest⟩
  wp_auto
  have hs1 : W32 ((s : Int) - 1) + W32 1 = W32 (s : Int) := by word
  rw [hs1]
  rw [show (#(W8 1) : val) = #(sp.Cmd.put key v).op from rfl,
    show (#cid : val) = #(⟨cid, W32 (s : Int)⟩ : sp.CmdId).cl from rfl,
    show (#(W32 (s : Int)) : val) = #(⟨cid, W32 (s : Int)⟩ : sp.CmdId).seq from rfl,
    show (#key : val) = #(sp.Cmd.put key v).key from rfl]
  wp_apply wp_Invoke g γ γc γm γl (⟨cid, W32 (s : Int)⟩ : sp.CmdId) (sp.Cmd.put key v) vsl
    (fun _ => iprop(client.ready b γ γc γm γl cid (s + 1) -∗ Φ #())) $$ [Hcs HAU]
    as ⟨#Hcmd, Hcs, Hrcpt⟩
  · iframe; iframe #
    isplitr
    · simp only [sp.Cmd.put]; iexact Hv
    ipureintro
    exact ⟨Hcid, Or.inl rfl, Hb.1, by word, by rw [hs]; exact Hb.2⟩
  wp_method_call
  wp_call
  try wp_auto
  wp_apply wp_SendWrite bv.Client' γ γc γm cid N s key vsl v $$ [Hseq Hrest] as ⟨Hseq, Hsend⟩
  · iframe; iframe #
    isplitl [Hrest]
    · unfold client.sendSt; iexists lg, ld, ssl, wsl, wrs; iframe; iframe #
    ipureintro; exact Hb.1
  iapply wp_fupd
  wp_apply (lc := 1) wp_bag_receive γch bv.Reply' (client.replyP γ cid γd) $$ Hbag as %p Hp
  ihave Hp := (client.replyP_unfold _ _ _ _).1 $$ Hp
  icases Hp with ⟨%rr, %bs, %n, #Hp, #Hval, %Hn, #Hdone, Htokn⟩
  ihave %Hsn := client.toks_fresh γd s n $$ [Htoks Htokn]
  · iframe
  have es : (W32 (s : Int)).toNat + 1 = s + 1 := by rw [hs]
  ihave Hcs : sp.clientSeq γ cid (s + 1) $$ [Hcs]
  · rw [← es]; iexact Hcs
  iapply fupd_wp
  imod (sp.doneRes_seq (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by solve_ndisj)
    (⟨cid, W32 (n : Int)⟩ : sp.CmdId) bs (s + 1)) $$ [Hcs] with ⟨%Hlt, Hcs⟩
  · iframe; iframe #
  have hns : n = s := by
    have h1 : (W32 (n : Int)).toNat = n := by word
    simp only at Hlt
    omega
  subst hns
  imod (sp.doneRes_put (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by solve_ndisj)
    (⟨cid, W32 (n : Int)⟩ : sp.CmdId) (sp.Cmd.put key v) bs (by show (sp.opPUT == sp.opGET) = false; decide)) $$ [] with %Hbs
  · iframe #
  subst Hbs
  imodintro
  try wp_auto
  rw [show (#cid : val) = #(⟨cid, W32 (n : Int)⟩ : sp.CmdId).cl from rfl,
    show (#(W32 (n : Int)) : val) = #(⟨cid, W32 (n : Int)⟩ : sp.CmdId).seq from rfl]
  wp_apply wp_Accept g γ γc γm γl (⟨cid, W32 (n : Int)⟩ : sp.CmdId) []
    slice.nil (fun _ => iprop(client.ready b γ γc γm γl cid (n + 1) -∗ Φ #())) $$ [Hrcpt]
    as HΨ
  · iframe; iframe #
    iapply ownSlice_nil
  imod lc_fupd_elim_later $$ Hlc1 HΨ with HΨ
  imodintro
  iapply HΨ
  iapply (client.ready_unfold _ _ _ _ _ _ _).2
  iexists bv, bv.Client', N, γch, γd
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨rfl, Hcl2, Hcid⟩
  isplitl [Hseq]
  · have h1 : ((↑(n + 1) : Int) - 1) = (n : Int) := by omega
    rw [h1]; iexact Hseq
  iapply client.toks_snoc
  iframe

/-- The spec (`specI` is its text, over the changed `ready`, change log C4). -/
theorem client.BufferClient.Write.wp_proof (wp_SendWrite : client.Client.SendWrite.specI (hG := hG))
    (wp_theGhost : client.theGhost.specG (hG := hG))
    (wp_Invoke : client.Ghost.Invoke.specG (hG := hG))
    (wp_Accept : client.Ghost.Accept.specG (hG := hG)) :
    client.BufferClient.Write.spec (hG := hG) := by
  exact client.BufferClient.Write.wp_proofI wp_SendWrite wp_theGhost wp_Invoke wp_Accept

end proof

end Perennial.github_com.imdea_software.swiftpaxos

/- The proof before the GHOST code (fork a650254) and change log C12, for reference: it
registered the command and deposited the update with `sp.client_register` before `SendWrite`,
and collected the continuation with `sp.client_collect` after the reply (both laws are gone:
the linearization is the client node's, `Proof/client/Ghost.lean`).
theorem client.BufferClient.Write.wp_proofI
    (wp_SendWrite : client.Client.SendWrite.specI (hG := hG)) :
    client.BufferClient.Write.specI (hG := hG) := by
  intro b γ γc γm γl cid s key vsl v
  iintro #Hpkg Hready #Hv %Hb
  unfold atomic_wp
  iintro %Φ AU
  ihave Hready := (client.ready_unfold _ _ _ _ _ _ _).1 $$ Hready
  icases Hready with ⟨%bv, %cl, %N, %γch, %γd, #Hbv, %Hcl, Hseq, Hsend, #Hinv, Hcs, Htoks, #Hbag⟩
  ihave HAU : sp.cmdAU γl (sp.Cmd.put key v)
      (fun _ => iprop(client.ready b γ γc γm γl cid (s + 1) -∗ Φ #())) $$ [AU]
  · unfold sp.cmdAU
    iapply aupd_mono ?_ ?_ $$ AU
    · rintro ⟨σ, ⟨⟩⟩ ⟨⟩; exact .rfl
    · rintro ⟨σ, ⟨⟩⟩ ⟨⟩; exact .rfl
  have hs : (W32 (s : Int)).toNat = s := by word
  have hreg := sp.client_register (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by solve_ndisj)
    (⟨cid, W32 (s : Int)⟩ : sp.CmdId) (sp.Cmd.put key v)
    (fun _ => iprop(client.ready b γ γc γm γl cid (s + 1) -∗ Φ #()))
  simp only [hs] at hreg
  ihave Hreg := hreg $$ [Hcs HAU]
  · iframe
    isplitr
    · ipureintro
      exact ⟨Hcl.2.2, Or.inl rfl, Hb.1, by have := Hb.2; word⟩  -- change log C8
    iexact Hinv
  iapply fupd_wp
  imod Hreg with ⟨#Hcmd, Htok, Hcs, %γΨ, #Hslot, #Hsaved⟩
  imodintro
  wp_method_call
  wp_call
  wp_auto
  wp_method_call
  wp_call
  ihave #Hbf := Hbv
  iStructNamed Hbf
  wp_auto
  obtain ⟨Hcl1, Hcl2, Hcid⟩ := Hcl
  subst Hcl1
  wp_apply wp_SendWrite bv.Client' γ γc γm cid N s key vsl v $$ [Hseq Hsend] as ⟨Hseq, Hsend⟩
  · iframe; iframe #; ipureintro; exact Hb.1
  iapply wp_fupd
  wp_apply (lc := 1) wp_bag_receive γch bv.Reply' (client.replyP γ cid γd) $$ Hbag as %p Hp
  ihave Hp := (client.replyP_unfold _ _ _ _).1 $$ Hp
  icases Hp with ⟨%rr, %bs, %n, #Hp, #Hval, %Hn, #Hdone, Htokn⟩
  ihave %Hsn := client.toks_fresh γd s n $$ [Htoks Htokn]
  · iframe
  imod (sp.doneRes_seq (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by solve_ndisj)
    (⟨cid, W32 (n : Int)⟩ : sp.CmdId) bs (s + 1)) $$ [Hcs] with ⟨%Hlt, Hcs⟩
  · iframe; iframe #
  have hns : n = s := by
    have h1 : (W32 (n : Int)).toNat = n := by word
    simp only at Hlt
    omega
  subst hns
  imod (sp.client_collect (γ := γ) (γc := γc) (γm := γm) (γl := γl) ⊤ (by solve_ndisj)
    (⟨cid, W32 (n : Int)⟩ : sp.CmdId) bs γΨ _) $$ [Htok] with HΨ
  · iframe; iframe #
  imod lc_fupd_elim_later $$ Hlc1 HΨ with HΨ
  imodintro
  iapply HΨ
  iapply (client.ready_unfold _ _ _ _ _ _ _).2
  iexists bv, bv.Client', N, γch, γd
  iframe; iframe #
  isplitr
  · ipureintro; exact ⟨rfl, Hcl2, Hcid⟩
  isplitl [Hseq]
  · have h1 : ((↑(n + 1) : Int) - 1) = (n : Int) := by omega
    rw [h1]; iexact Hseq
  iapply client.toks_snoc
  iframe

-/
