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
configuration (`sp.allPredsReg`) and returns `ownState γ init`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchParts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchAddr
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.OrchSend
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.Start
public import Perennial.Proof.time

-- PORT: lab imports dropped: Harness.Proof.log

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

namespace orch

section protos
variable [GoGlobalContext] [G : GooseGlobalGS .hasLC netDistGF]

/-! ## The configuration ports' protocols -/

/-- The acknowledgment protocol of server node `k + 1`'s configuration port (`confAddrs[k]`):
the master's carries nothing, replica node `k - 1`'s its registration. -/
def srvAckQ (γ : SwiftNames netDistGF) (k : Nat) : Proto netDistGF :=
  if k = 0 then conf.ackQ else conf.ackQP γ (sp.PNode.rep (k - 1))

theorem protoP_conf (γ : SwiftNames netDistGF) (k : Nat) (a : GoString) (hk : confAddrs[k]? = some a) :
    protoP γ a = conf.dialP γ ∧ protoQ γ a = srvAckQ γ k := by
  match k, hk with
  | 0, hk | 1, hk | 2, hk | 3, hk | 4, hk | 5, hk =>
    simp only [confAddrs, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hk
    subst hk
    unfold protoP protoQ srvAckQ
    rw [if_pos (by decide)]
    exact ⟨rfl, rfl⟩

theorem protoP_clientConf (γ : SwiftNames netDistGF) (c : Nat) (a : GoString)
    (hc : clientConfAddrs[c]? = some a) :
    protoP γ a = conf.dialPC γ ∧ protoQ γ a = conf.ackQP γ (sp.PNode.cl c) := by
  match c, hc with
  | 0, hc | 1, hc | 2, hc | 3, hc | 4, hc | 5, hc =>
    simp only [clientConfAddrs, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.some.injEq] at hc
    subst hc
    unfold protoP protoQ
    rw [if_neg (by decide), if_pos (by decide)]
    exact ⟨rfl, rfl⟩

/-- What `configure` needs of the run (persistent; from `common`). -/
def confEnv (γ : SwiftNames netDistGF) : IProp netDistGF :=
  iprop(([∗list] k ↦ a ∈ confAddrs, addrProtoG netDistGS a (conf.dialP γ) (srvAckQ γ k)) ∗
    [∗list] c ↦ a ∈ clientConfAddrs, addrProtoG netDistGS a (conf.dialPC γ)
      (conf.ackQP γ (sp.PNode.cl c)))

instance confEnv_persistent (γ : SwiftNames netDistGF) : Persistent (confEnv γ) := by
  unfold confEnv; infer_instance

theorem common_confEnv (γ : SwiftNames netDistGF) : common γ ⊢ confEnv γ := by
  unfold common confEnv
  iintro ⟨#Hpl, -, -, -⟩
  have hpl : plainAddrs = ([orchAddr] ++ clientNodeAddrs ++ clientConfAddrs) ++ confAddrs ++
      replicaAddrs := rfl
  rw [hpl]
  ihave ⟨#H1, -⟩ := BigSepL.bigSepL_append.1 $$ Hpl
  ihave ⟨#H2, #Hc⟩ := BigSepL.bigSepL_append.1 $$ H1
  ihave ⟨-, #Hcc⟩ := BigSepL.bigSepL_append.1 $$ H2
  isplitl
  · iapply BigSepL.bigSepL_mono _ $$ Hc
    intro k a hka
    obtain ⟨h1, h2⟩ := protoP_conf γ k a hka
    rw [h1, h2]
  · iapply BigSepL.bigSepL_mono _ $$ Hcc
    intro k a hka
    obtain ⟨h1, h2⟩ := protoP_clientConf γ k a hka
    rw [h1, h2]

end protos

/-- An acknowledgment of a predicted node's configuration port: its registration. -/
theorem ackQP_reg [GoGlobalContext] [GooseGlobalGS .hasLC netDistGF] (γ : SwiftNames netDistGF)
    (n : sp.PNode) (cid : w64) (ext : List w8) (h : [confAck] <+: ext) :
    conf.ackQP γ n cid ext ⊢ sp.predReg γ.sp n := by
  unfold conf.ackQP
  iintro ⟨-, (%He | #H)⟩
  · subst He; simp at h
  · iexact H

/-! ## `configure` and `New` -/

section proofs
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF]
variable [examples.swiftnet.Assumptions] [net.FieldAssumptions] [io.ExtraAssumptions]

set_option goose.wp.extras true

local notation "swiftnetPkg" => pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet

/-- `configure(addrs, conf, cs)`: every node of the configuration and every client node
acknowledged; the replicas' and the clients' registrations. -/
abbrev configure.spec (γ : SwiftNames netDistGF) : Prop :=
  ∀ (asl csl : GoSlice) (c : Conf) (cs : List examples.swiftnet.change),
  c.valid → cs.length ≤ maxChanges → (∀ ch ∈ cs, planOk c ch) →
  {{ isPkgInit (PROP := IProp netDistGF) swiftnetPkg ∗ asl ↦*□ addrs ∗ csl ↦* cs ∗
      conf.is γ c ∗ confEnv γ }}
    (App (App (App (Val (@! examples.swiftnet.configure)) (Val #asl)) (Val #(confV c)))
      (Val #csl))
  {{ RET #(); ([∗list] k ∈ List.range c.n, sp.predReg γ.sp (sp.PNode.rep k)) ∗
      [∗list] cl ∈ List.range 6, sp.predReg γ.sp (sp.PNode.cl cl) }}

theorem configure.wp_proof (γ : SwiftNames netDistGF) : configure.spec γ := by
  intro asl csl c cs hc hcs hok
  wp_start as ⟨#Hasl, Hcsl, #Hconfis, #Henv⟩
  wp_auto
  wp_apply Conf.String.wp_proof conf_ptr (confV c) (DFrac.own 1) $$ [conf] as %str conf
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
  wp_apply log.wp_Println _ _ _ (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil) $$ [Hlit] as -
  · iexact Hlit
  iunfold confEnv at Henv
  icases Henv with ⟨#HconfP, #HclP⟩
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
    wp_apply at.wp_proof asl DFrac.discard (W64 6 + id) (W64 2000) (by word) $$ []
      as -
    · iexact Hasl
    ihave Hnil := ownSlice_nil (V := examples.swiftnet.change) (GF := netDistGF) (DFrac.own 1)
    wp_apply Conf.encode.wp_proof conf_ptr c (DFrac.own 1) slice.nil (DFrac.own 1) [] hc
      (by simp) $$ [conf Hnil] as %bsl ⟨Hb, conf, -⟩
    · iframe conf Hnil
    have hk : uint.nat id - 1 < 6 := by omega
    have hidx := atStr_conf (uint.nat id - 1) hk
    rw [show 7 + (uint.nat id - 1) = uint.nat (W64 6 + id) by word] at hidx
    ihave #Hpr := BigSepL.bigSepL_lookup
      (Φ := fun k a => addrProtoG netDistGS a (conf.dialP γ) (srvAckQ γ k)) hidx $$ HconfP
    wp_apply sendConf.wp_proof (atStr (uint.nat (W64 6 + id)) (W64 2000)) bsl c.encode
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
      wp_apply at.wp_proof asl DFrac.discard (W64 1 + cv) (W64 2000) (by word) $$ []
        as -
      · iexact Hasl
      wp_apply mine.wp_proof csl (DFrac.own 1) cs cv $$ [Hcsl] as %msl ⟨Hm, Hcsl⟩
      · iexact Hcsl
      have hmok := mineL_ok c cs cv hcs hok
      wp_apply Conf.encode.wp_proof conf_ptr c (DFrac.own 1) msl (DFrac.own 1) (mineL cs cv) hc
        (by simpa using hmok.1) $$ [conf Hm] as %bsl ⟨Hb, conf, -⟩
      · iframe conf Hm
      have hidx := atStr_clientConf (uint.nat cv) hcv
      rw [show 1 + uint.nat cv = uint.nat (W64 1 + cv) by word] at hidx
      ihave #Hpr := BigSepL.bigSepL_lookup
        (Φ := fun k a => addrProtoG netDistGS a (conf.dialPC γ) (conf.ackQP γ (sp.PNode.cl k)))
        hidx $$ HclP
      wp_apply sendConf.wp_proof (atStr (uint.nat (W64 1 + cv)) (W64 2000)) bsl
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
      iapply HΦ
      iframe

/-- `New(addrs)`: from the orchestrator's share, the abstract state at its start with every
registration of the configuration (`ownState γ init`). -/
theorem New.wp_proof (γ : SwiftNames netDistGF) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp netDistGF) kit.pkg ∗ orchShare γ ∗ sl ↦*□ kit.addrs }}
      (App (Val (@! kit.newF)) (Val #sl))
    {{ RET #(); ownState γ (kv GoString GoString).init }} := by
  dsimp only [kit]
  wp_start as ⟨Hsh, #Hsl⟩
  iunfold orchShare at Hsh
  icases Hsh with ⟨-, Hw, Hlin, #Hcommon⟩
  ihave #Henv := common_confEnv γ $$ Hcommon
  wp_auto
  wp_apply choose.wp_proof as %c %hc
  imod conf.write γ c $$ [Hw] with #Hconfis
  · iframe Hw; ipureintro; exact hc
  wp_apply plan.wp_proof c hc as %csl %cs ⟨Hcsl, %hcs⟩
  wp_apply configure.wp_proof γ sl csl c cs hc hcs.1 hcs.2 $$ [Hcsl] as ⟨#Hr, #Hcl⟩
  · iframe Hsl Hcsl Hconfis Henv
  iapply HΦ
  unfold ownState
  iframe Hlin
  isplitr
  · ipureintro
    intro k v h
    simp [kv] at h
  unfold sp.allPredsReg
  iexists c
  iframe Hr Hcl
  iapply (conf.is_confIs γ c).1
  iexact Hconfis

end proofs

end orch

end Perennial.github_com.imdea_software.swiftpaxos
