/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/client/Client__SendProposal.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.ISpecs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.client.Marshal
public import Dsverify.Spec.github_com.imdea_software.swiftpaxos.dlog.Logger__Println

-- PORT: lab imports dropped: Harness.Proof.bufio.Net

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv wire

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [client.Assumptions] [net.Assumptions] [net.FieldAssumptions]
variable [bufio.Assumptions] [state.Assumptions] [encoding.binary.Assumptions]
variable [replica.defs.Assumptions] [dlog.Assumptions]

theorem framesOf_snoc (ms : List sp.Msg) (m : sp.Msg) :
    sp.framesOf (ms ++ [m]) = sp.framesOf ms ++ m.frame := by
  simp [sp.framesOf]

/-- Whole frames of a client's registered proposals are in `inP` on its connection. -/
theorem inP_aligned (γ : sp.Names) (γc γm : GName) (cn : Nat) (cid : w32) (ms : List sp.Msg)
    (hms : ∀ m ∈ ms, sp.Msg.isProposeOf cid m ∧ sp.Msg.wf m) :
    sp.connKind γ cn (.client cid) ∗ ([∗list] m ∈ ms, sp.msgOk γ γc γm m) ⊢
      sp.inP γ γc γm cn (sp.framesOf ms) := by
  iintro ⟨#Hk, Hms⟩
  iapply sp.inP_client
  iframe Hk
  unfold sp.framesProto
  iexists ms
  iframe Hms
  ipureintro
  exact ⟨by simp, hms⟩

set_option hygiene false in
/-- Load `c.writers[rep]` (the bounds check first). -/
local macro "loadw" : tactic => `(tactic| (
  (try wp_auto)
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
  wp_apply wp_load_slice_index wsl (sint.Z i) wrs DFrac.discard w Hi.1 $$ [Hwsl] as -
  · iframe #; ipureintro; exact Hw_lookup))

theorem client.Client.SendProposal.wp_proof
    (wp_Println : dlog.Logger.Println.spec (GF := netDistGF) (hG := hG)) :
    client.Client.SendProposal.specI (hG := hG) := by
  intro cl γ γc γm cid N pv seq c
  wp_start as ⟨Hsend, #Hv, #Hcmd, %Hpv⟩
  unfold client.sendSt
  icases Hsend with ⟨%lg, %ld, %ssl, %wsl, %wrs, #Hcid, #Hfast, #Hll, #Hlg, #Hq, #Hld, #Hsrv,
    #Hwrs, #Hwsl, %Hlen, Hws⟩
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨-, -⟩
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_Println $$ Hq
  ihave %Hwl := ownSlice_len _ _ _ $$ Hwsl
  obtain ⟨hN, hssl0, hwN⟩ := Hlen
  ihave HI : (∃ i : w64, "rep" ∷ rep_ptr ↦ i ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z ssl.len⌝ : IProp netDistGF) $$ [rep]
  · iexists _; iframe; ipureintro; word
  wp_for HI
  wp_if_destruct
  · have hiN : sint.nat i < wrs.length := by word
    list_elem wrs (sint.nat i) as w
    rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
    wp_apply wp_load_slice_index wsl (sint.Z i) wrs DFrac.discard w Hi.1 $$ [$Hwsl] as -
    · ipureintro; exact Hw_lookup
    ihave Hacc := (BigSepL.bigSepL_lookup_acc Hw_lookup).1 $$ Hws
    icases Hacc with ⟨Hw, Hback⟩
    by_cases hw0 : w = null
    case pos =>
      rw [decide_eq_true hw0]
      wp_auto
      ihave Hws := Hback $$ Hw
      rw [list_set_lookup_self wrs (sint.nat i) w Hw_lookup]
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; word
    case neg =>
      -- a writer: frame the proposal on it
      rw [decide_eq_false hw0]
      wp_auto
      iunfold client.wrOk at Hw
      icases Hw with (%Hnull | ⟨%srv, %cn, %sent, %pend, %err, #Hconn, #Hkind, Hown, Hal⟩)
      · exact absurd Hnull hw0
      ihave #Hpc : bufio.prefixClosed (sp.inP γ γc γm cn) $$ []
      · iunfold bufio.prefixClosed; iapply sp.inP_prefixClosed
      ihave #Hwok := bufio.writerOk_conn srv cn false (sp.inP γ γc γm) $$ [$Hconn $Hpc]
      · iPkgInit
      ihave Hs : (∃ (W : List w8) (ms : List sp.Msg),
          wsink w srv (sendTok cn false (sp.inP γ γc γm)) (sp.inP γ γc γm cn) W ∗
          ⌜W = sp.framesOf ms ∧ ∀ m ∈ ms, sp.Msg.isProposeOf cid m ∧ sp.Msg.wf m⌝ ∗
          [∗list] m ∈ ms, sp.msgOk γ γc γm m : IProp netDistGF) $$ [Hown Hal]
      · icases Hal with (%Herr | ⟨%Hpend, Hal⟩)
        · iexists [], []
          unfold wsink
          isplitl [Hown]
          · iexists sent, pend, err; iframe; ipureintro; intro h; exact absurd h Herr
          isplitr
          · ipureintro; simp [sp.framesOf]
          iapply BigSepL.bigSepL_nil.2; iempintro
        · unfold client.wrAligned
          icases Hal with ⟨%ms, %Hms, Hmsok⟩
          iexists sent, ms
          unfold wsink
          isplitl [Hown]
          · iexists sent, pend, err; iframe; ipureintro; intro _; simp [Hpend]
          iframe
          ipureintro; exact Hms
      icases Hs with ⟨%W, %ms, Hs, %Hms, #Hmsok⟩
      have hm : sp.Msg.isProposeOf cid (sp.Msg.propose seq cid c (W64 0)) ∧
          sp.Msg.wf (sp.Msg.propose seq cid c (W64 0)) := ⟨rfl, Hpv.2.2.2.2.2⟩
      ihave #HQf : (□ sp.inP γ γc γm cn (sp.framesOf (ms ++ [sp.Msg.propose seq cid c (W64 0)])) :
          IProp netDistGF) $$ []
      · imodintro
        iapply inP_aligned γ γc γm cn cid _ (by
          intro m hmem; rcases List.mem_append.1 hmem with h | h
          · exact Hms.2 m h
          · simp at h; subst h; exact hm)
        iframe Hkind
        iapply BigSepL.bigSepL_snoc.2
        iframe Hmsok
        unfold sp.msgOk; iexact Hcmd
      rw [framesOf_snoc, ← Hms.1]
      have hfr : W ++ (sp.Msg.propose seq cid c (W64 0)).frame =
          W ++ [W8 0] ++ (sp.Msg.propose seq cid c (W64 0)).body := by
        simp [sp.Msg.frame, sp.Msg.code]
      rw [hfr]
      ihave #Hpc0 := Hpc
      iunfold bufio.prefixClosed at Hpc
      ihave #HQ1 := Hpc $$ %_ %_ HQf
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi.1, by word⟩)]
      wp_apply wp_load_slice_index wsl (sint.Z i) wrs DFrac.discard w Hi.1 $$ [Hwsl] as -
      · iframe #; ipureintro; exact Hw_lookup
      wp_apply wp_WriteByte_sink w srv _ _ W (W8 0) $$ [$Hwok $Hs $HQ1] as %e1 Hs
      loadw
      ihave #Hsink := bufio_sinkOk w srv _ _ $$ [Hwok]
      · iframe #; iPkgInit
      obtain ⟨hpseq, hpcl, hpop, hpk, hpts, -⟩ := Hpv
      wp_apply wp_Propose_Marshal cmd_ptr (DFrac.own 1) pv seq cid c (W64 0) _ _ _ (W ++ [W8 0])
        $$ [$Hsink $Hs $Hpc0 $HQf $cmd $Hv] as ⟨Hs, cmd⟩
      · ipureintro; exact ⟨hpseq, hpcl, hpop, hpk, hpts⟩
      loadw
      wp_apply wp_Flush_sink w srv _ _ _ $$ [$Hwok $Hs] as %e2 ⟨%sent', %pend', %err', Hown, %Hfl⟩
      ihave Hw' : client.wrOk γ γc γm cid w $$ [Hown]
      · iunfold client.wrOk
        iright
        iexists srv, cn, sent', pend', err'
        iframe Hconn Hkind Hown
        by_cases herr' : err' = interface.nil
        · iright
          obtain ⟨hs', hp'⟩ := Hfl herr'
          isplitr
          · ipureintro; exact hp'
          unfold client.wrAligned
          iexists ms ++ [sp.Msg.propose seq cid c (W64 0)]
          isplitr
          · ipureintro
            refine ⟨?_, ?_⟩
            · rw [hs', framesOf_snoc, ← hfr, Hms.1]
            · intro m hmem; rcases List.mem_append.1 hmem with h | h
              · exact Hms.2 m h
              · simp at h; subst h; exact hm
          iapply BigSepL.bigSepL_snoc.2
          iframe Hmsok
          unfold sp.msgOk; iexact Hcmd
        · ileft; ipureintro; exact herr'
      ihave Hws := Hback $$ Hw'
      rw [list_set_lookup_self wrs (sint.nat i) w Hw_lookup]
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro; word
  · iapply HΦ
    iexists lg, ld, ssl, wsl, wrs
    iframe; iframe #
    ipureintro; exact ⟨hN, hssl0, hwN⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos
