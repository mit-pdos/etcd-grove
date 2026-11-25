/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/OrchNew.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The orchestrator's `New(addrs)` (`kit.go`): `choose`, `plan`, and `configure`, which sends the
configuration to the master and the configuration's replicas (`Conf.encode(nil)`, protocol
`conf.dialP`) and to every client node (`Conf.encode(mine(cs, c))`, protocol `conf.dialPC`),
each until it acknowledges. The configuration is written (`conf.write`) before the first
message; each acknowledgment of a replica node's or a client node's configuration port carries
its prediction's registration (`conf.ackQP`), so `New` ends with every registration of the
configuration (`sp.allPredsReg`); then it sends the configuration again to every client node's
start port (`conf.startP`, which carries the registrations: the client nodes connect only after
it). `sendConf` is a callee (`sendConf.spec`, `OrchSend.lean`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchPartsDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Addr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.KitDeps
public import Perennial.Proof.time
public import Perennial.Proof.log
public import Perennial.Spec.log.Println

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace orch


/-! ## `configure` and `New` -/

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [SwiftBufioDeps netDistGF] [SwiftNetDeps netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions]

set_option goose.wp.extras true

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- Every predicted node of the configuration `c` registered. -/
theorem allPredsReg_of (γ : SwiftNames netDistGF) (c : Conf) :
    conf.is γ c ∗ ([∗list] k ∈ List.range c.n, sp.predReg γ.sp (sp.PNode.rep k)) ∗
      ([∗list] cl ∈ List.range 6, sp.predReg γ.sp (sp.PNode.cl cl)) ⊢
      sp.allPredsReg γ.sp γ.conf := by
  iintro ⟨#Hc, #Hr, #Hcl⟩
  unfold sp.allPredsReg
  iexists c
  iframe Hr Hcl
  iapply (conf.is_confIs γ c).1
  iexact Hc

/-- `configure(addrs, conf, cs)`: every node of the configuration and every client node
acknowledged; the replicas' and the clients' registrations. -/
abbrev configure.spec (γ : SwiftNames netDistGF) : Prop :=
  ∀ (asl csl : GoSlice) (c : Conf) (cs : List examples.swiftnet.change),
  c.valid → cs.length ≤ maxChanges → (∀ ch ∈ cs, planOk c ch) →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ asl ↦*□ addrs ∗ csl ↦* cs ∗
      conf.is γ c ∗ confEnv γ }}
    (App (App (App (Val (@! examples.swiftnet.configure)) (Val #asl)) (Val #(confV c)))
      (Val #csl))
  {{ RET #(); sp.allPredsReg γ.sp γ.conf }}

theorem configure.wp_proof (γ : SwiftNames netDistGF) (wp_send : sendConf.spec (hG := hG))
    (wp_Println : log.Println.spec (GF := netDistGF) (hG := hG))
    (wp_String : Conf.String.spec (hG := hG)) (wp_encode : Conf.encode.spec (hG := hG))
    (wp_mine : mine.spec (hG := hG)) :
    configure.spec γ := by
  intro asl csl c cs hc hcs hok
  wp_start as ⟨#Hasl, Hcsl, #Hconfis, #Henv⟩
  wp_auto
  wp_apply wp_String conf_ptr (confV c) (DFrac.own 1) $$ [conf] as %str conf
  · iexact conf
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.GoType.InterfaceType [])))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.GoType.InterfaceType [])
    [interface.mkOk go.string #(go!"swiftnet: configuration: " ++ str)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_auto
  wp_apply wp_Println _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hlit] as -
  · iexact Hlit
  iunfold confEnv at Henv
  icases Henv with ⟨#HconfP, #HclP, #HstP⟩
  have hcn : c.n = 3 ∨ c.n = 5 := hc.1
  have hcn32 : c.n < 2 ^ 32 := by rcases hcn with h | h <;> rw [h] <;> decide
  ihave HI : (∃ id : w64, "id" ∷ id_ptr ↦ id ∗
      "Hregs" ∷ ([∗list] k ∈ List.range (uint.nat id - 2), sp.predReg γ.sp (sp.PNode.rep k)) ∗
      "%Hid" ∷ ⌜1 ≤ uint.nat id ∧ uint.nat id ≤ c.n + 2⌝ : IProp netDistGF) $$ [id]
  · iexists _; iframe
    isplitl
    · rw [show uint.nat (W64 1) - 2 = 0 from rfl, List.range_zero]
      iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; rcases hcn with h | h <;> rw [h] <;> decide
  wp_for HI
  wp_if_destruct
  · have hle : uint.Z id ≤ uint.Z (W64 (c.n : Int) + W64 1) := Hif
    have hid : uint.nat id ≤ c.n + 1 := by
      rcases hcn with h | h <;> rw [h] at hle ⊢ <;> word
    wp_for
    wp_apply wp_at asl DFrac.discard (W64 6 + id) (W64 2000) (by word) $$ []
      as -
    · iexact Hasl
    ihave Hnil := ownSlice_nil (V := examples.swiftnet.change) (GF := netDistGF) (DFrac.own 1)
    wp_apply wp_encode conf_ptr c (DFrac.own 1) slice.nil (DFrac.own 1) [] hc
      (by simp) $$ [conf Hnil] as %bsl ⟨Hb, conf, -⟩
    · iframe conf Hnil
    have hk : uint.nat id - 1 < 6 := by omega
    have hidx := atStr_conf (uint.nat id - 1) hk
    rw [show 7 + (uint.nat id - 1) = uint.nat (W64 6 + id) by word] at hidx
    ihave #Hpr := BigSepL.bigSepL_lookup
      (Φ := fun k a => addrProto a (conf.dialP γ) (srvAckQ γ k)) hidx $$ HconfP
    wp_apply wp_send (atStr (uint.nat (W64 6 + id)) (W64 2000)) bsl c.encode
      (conf.dialP γ) (srvAckQ γ (uint.nat id - 1)) $$ [Hb] as %ok Hok
    · iframe Hpr
      isplitr [Hb]
      · imodintro
        iintro %cid
        unfold conf.dialP
        iright
        iexists c
        iframe Hconfis
        ipureintro; exact List.prefix_refl _
      simp only [List.map_nil]
      unfold Conf.encode
      iexact Hb
    cases ok
    · iclear Hok
      rw [if_pos (by simp)]
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · rw [if_pos (rfl : true = true)]
      icases Hok with ⟨%cid, %ext, %Hext, #HQ⟩
      rw [if_neg (by
        intro h
        have h' := of_decide_eq_true h
        simp only [Bool.not_true] at h'
        exact absurd (go.intoVal_inj h') (by decide))]
      rw [if_pos (by simp)]
      wp_for_post
      iframe
      iexists id + W64 1
      iframe
      isplitl [Hregs]
      · by_cases h1 : uint.nat id = 1
        · rw [show uint.nat (id + W64 1) - 2 = uint.nat id - 2 by word]
          iexact Hregs
        · unfold srvAckQ
          rw [if_neg (by omega)]
          ihave #Hr := ackQP_reg γ _ cid ext Hext $$ HQ
          rw [show uint.nat (id + W64 1) - 2 = (uint.nat id - 2) + 1 by word, List.range_succ]
          iapply BigSepL.bigSepL_append.2
          iframe Hregs
          iapply BigSepL.bigSepL_singleton.2
          rw [show uint.nat id - 1 - 1 = uint.nat id - 2 by omega]
          iexact Hr
      ipureintro
      constructor <;> word
  · have hgt : ¬ uint.Z id ≤ uint.Z (W64 (c.n : Int) + W64 1) := Hif
    have hid : uint.nat id = c.n + 2 := by
      rcases hcn with h | h <;> rw [h] at hgt Hid ⊢ <;> word
    rw [hid, show c.n + 2 - 2 = c.n by omega]
    ihave HJ : (∃ cv : w64, "c" ∷ c_ptr ↦ cv ∗ "Hcsl" ∷ csl ↦* cs ∗
        "Hcregs" ∷ ([∗list] k ∈ List.range (uint.nat cv), sp.predReg γ.sp (sp.PNode.cl k)) ∗
        "%Hcv" ∷ ⌜uint.nat cv ≤ 6⌝ : IProp netDistGF) $$ [c Hcsl]
    · iexists _; iframe
      isplitl
      · rw [show uint.nat (W64 0) = 0 from rfl, List.range_zero]
        iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro; decide
    wp_for HJ
    wp_if_destruct
    · have hcv : uint.nat cv < 6 := by
        have h : uint.Z cv < uint.Z (W64 6) := Hif
        word
      wp_for
      wp_apply wp_at asl DFrac.discard (W64 1 + cv) (W64 2000) (by word) $$ []
        as -
      · iexact Hasl
      wp_apply wp_mine csl (DFrac.own 1) cs cv $$ [Hcsl] as %msl ⟨Hm, Hcsl⟩
      · iexact Hcsl
      have hmok := mineL_ok c cs cv hcs hok
      wp_apply wp_encode conf_ptr c (DFrac.own 1) msl (DFrac.own 1) (mineL cs cv) hc
        (by simpa using hmok.1) $$ [conf Hm] as %bsl ⟨Hb, conf, -⟩
      · iframe conf Hm
      have hidx := atStr_cconf (uint.nat cv) hcv
      rw [show 1 + uint.nat cv = uint.nat (W64 1 + cv) by word] at hidx
      ihave #Hpr := BigSepL.bigSepL_lookup
        (Φ := fun k a => addrProto a (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl k)))
        hidx $$ HclP
      wp_apply wp_send (atStr (uint.nat (W64 1 + cv)) (W64 2000)) bsl
        (c.encodeC ((mineL cs cv).map toChange))
        (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl (uint.nat cv))) $$ [Hb] as %ok Hok
      · iframe Hpr Hb
        imodintro
        iintro %cid
        unfold conf.dialPC
        iright
        iexists c, (mineL cs cv).map toChange
        iframe Hconfis
        ipureintro; exact ⟨hmok, List.prefix_refl _⟩
      cases ok
      · iclear Hok
        rw [if_pos (by simp)]
        wp_auto
        wp_apply time.wp_Sleep
        wp_for_post
        iframe
      · rw [if_pos (rfl : true = true)]
        icases Hok with ⟨%cid, %ext, %Hext, #HQ⟩
        rw [if_neg (by
          intro h
          have h' := of_decide_eq_true h
          simp only [Bool.not_true] at h'
          exact absurd (go.intoVal_inj h') (by decide))]
        rw [if_pos (by simp)]
        wp_for_post
        iframe
        iexists cv + W64 1
        iframe
        isplitl [Hcregs]
        · ihave #Hr := ackQP_reg γ _ cid ext Hext $$ HQ
          rw [show uint.nat (cv + W64 1) = uint.nat cv + 1 by word, List.range_succ]
          iapply BigSepL.bigSepL_append.2
          iframe Hcregs
          iapply BigSepL.bigSepL_singleton.2
          iexact Hr
        ipureintro
        word
    · have hcv : uint.nat cv = 6 := by
        have h : ¬ uint.Z cv < uint.Z (W64 6) := Hif
        word
      rw [hcv]
      ihave #Hall := allPredsReg_of γ c $$ [Hregs Hcregs]
      · iframe Hconfis Hregs Hcregs
      ihave HK : (∃ cv : w64, "c" ∷ c_ptr ↦ cv ∗ "%Hcv" ∷ ⌜uint.nat cv ≤ 6⌝ : IProp netDistGF) $$ [c]
      · iexists _; iframe; ipureintro; decide
      wp_for HK
      wp_if_destruct
      · have hcv : uint.nat cv < 6 := by
          have h : uint.Z cv < uint.Z (W64 6) := Hif
          word
        wp_for
        wp_apply wp_at asl DFrac.discard (W64 1 + cv) (W64 3000) (by word) $$ [] as -
        · iexact Hasl
        ihave Hnil := ownSlice_nil (V := examples.swiftnet.change) (GF := netDistGF) (DFrac.own 1)
        wp_apply wp_encode conf_ptr c (DFrac.own 1) slice.nil (DFrac.own 1) [] hc
          (by simp) $$ [conf Hnil] as %bsl ⟨Hb, conf, -⟩
        · iframe conf Hnil
        have hidx := atStr_cstart (uint.nat cv) hcv
        rw [show 1 + uint.nat cv = uint.nat (W64 1 + cv) by word] at hidx
        ihave #Hpr := BigSepL.bigSepL_lookup
          (Φ := fun _ a => addrProto a (conf.startP γ) conf.ackQ) hidx $$ HstP
        wp_apply wp_send (atStr (uint.nat (W64 1 + cv)) (W64 3000)) bsl c.encode
          (conf.startP γ) conf.ackQ $$ [Hb] as %ok Hok
        · iframe Hpr
          isplitr [Hb]
          · imodintro
            iintro %cid
            unfold conf.startP
            iright
            iexists c
            iframe Hconfis Hall
            ipureintro; exact List.prefix_refl _
          simp only [List.map_nil]
          unfold Conf.encode
          iexact Hb
        cases ok
        · iclear Hok
          rw [if_pos (by simp)]
          wp_auto
          wp_apply time.wp_Sleep
          wp_for_post
          iframe
        · rw [if_pos (rfl : true = true)]
          rw [if_neg (by
            intro h
            have h' := of_decide_eq_true h
            simp only [Bool.not_true] at h'
            exact absurd (go.intoVal_inj h') (by decide))]
          rw [if_pos (by simp)]
          wp_for_post
          iframe
          iexists cv + W64 1
          iframe
          ipureintro
          word
      · iapply HΦ
        iexact Hall

theorem New.wp_proof [RpcHttpAddr netDistGF] (γ : SwiftNames netDistGF)
    (wp_send : sendConf.spec (hG := hG))
    (wp_Println : log.Println.spec (GF := netDistGF) (hG := hG))
    (wp_String : Conf.String.spec (hG := hG)) (wp_encode : Conf.encode.spec (hG := hG))
    (wp_mine : mine.spec (hG := hG)) (wp_choose : choose.spec (hG := hG))
    (wp_plan : plan.spec (hG := hG)) : New.spec γ := by
  intro sl
  wp_start as ⟨Hw, #Hcommon, #Hsl⟩
  ihave #Henv := common_confEnv γ $$ Hcommon
  wp_auto
  wp_apply wp_choose as %c %hc
  imod conf.write γ c $$ [Hw] with #Hconfis
  · iframe Hw; ipureintro; exact hc
  wp_apply wp_plan c hc as %csl %cs ⟨Hcsl, %hcs⟩
  wp_apply configure.wp_proof γ wp_send wp_Println wp_String wp_encode wp_mine sl csl c cs hc hcs.1 hcs.2 $$ [Hcsl] as #Hall
  · iframe Hsl Hcsl Hconfis Henv
  iapply HΦ
  iexact Hall

end proofs

end orch

end Perennial.github_com.imdea_software.swiftpaxos
