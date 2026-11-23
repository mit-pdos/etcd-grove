/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/internal/tcp/Hub.lean`, run
`rabia-r1wake-1`. Its links of message's specs are `Basics.lean`'s wrappers over `rdOwn`/`wrOwn`;
the protocols' openers take a non-empty stream, since the protocols allow the empty one outright,
`Core/Proto.lean`.)

The protocols opened (`proxyQ_hub`, `proxyP_hub`, `proxyP_hub0`, `netP_hub0`, `netP_hub`) and the
send channels' predicate (`sendP_open`).
-/
module

public import Dsverify.Proof.rabia.internal.tcp.ProtoLemmas

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.internal.tcp

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia
  rabia.internal.message

section protos
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]

theorem proxyQ_hub (γ : Names) (k : Nat) (cid : Nat) (W : List w8) (hW : W ≠ []) :
    proxyQ (GF := GF) γ k cid W ⊢ ∃ (c : Nat) (rs : List CmdV),
      sentLb (Gg := hG.goose_globalGS) cid false (hsBytes c) ∗
      ⌜c < nC ∧ W <+: frames (rs.map encCmd) ∧ ∀ r ∈ rs, (encCmd r).length < 2 ^ 32⌝ ∗
      [∗list] q ∈ rs, repOk γ c q := by
  unfold proxyQ
  iintro (%Hn | ⟨%c, %rs, #Hs, %Hp, #Hr⟩)
  · exact absurd Hn hW
  iexists c, rs
  iframe Hs Hr
  ipureintro; exact Hp

/-- `proxyP` opened at the recorded configuration `cf`. -/
theorem proxyP_hub (γ : Names) (cf : RCfg) (k : Nat) (cid : Nat) (W : List w8) (hW : W ≠ []) :
    cfgIs γ.rab cf ∗ proxyP (GF := GF) γ k cid W ⊢ proxyP γ k cid W ∗ ∃ (c : Nat) (qs : List CmdV),
      ⌜c < nC ∧ c % cf.n = k ∧ W <+: hsBytes c ++ frames (qs.map encCmd) ∧
        qs.length ≤ opBudget ∧ qs.Pairwise (fun a b => a.cliSeq.toNat < b.cliSeq.toNat) ∧
        ∀ q ∈ qs, q.cliSeq.toNat < opBudget ∧ (encCmd q).length < 2 ^ 32⌝ ∗
      (⌜qs = []⌝ ∨ estab γ c k cid) ∗ [∗list] q ∈ qs, reqOk γ c q := by
  iintro ⟨#Hcf, #H⟩
  iframe H
  unfold proxyP
  icases H with (%Hn | ⟨%cf', %c, %qs, #Hcf', %Hp, #He, #Hr⟩)
  · exact absurd Hn hW
  ihave %Heq := cfgIs_agree γ.rab cf cf' $$ [$Hcf $Hcf']
  subst Heq
  iexists c, qs
  iframe He Hr
  ipureintro; exact Hp

/-- `proxyP` opened, at its own configuration. -/
theorem proxyP_hub0 (γ : Names) (k : Nat) (cid : Nat) (W : List w8) (hW : W ≠ []) :
    proxyP (GF := GF) γ k cid W ⊢ ∃ (cf : RCfg) (c : Nat) (qs : List CmdV),
      ⌜c < nC ∧ c % cf.n = k ∧ W <+: hsBytes c ++ frames (qs.map encCmd) ∧
        qs.length ≤ opBudget ∧ qs.Pairwise (fun a b => a.cliSeq.toNat < b.cliSeq.toNat) ∧
        ∀ q ∈ qs, q.cliSeq.toNat < opBudget ∧ (encCmd q).length < 2 ^ 32⌝ ∗
      (⌜qs = []⌝ ∨ estab γ c k cid) ∗ [∗list] q ∈ qs, reqOk γ c q := by
  unfold proxyP
  iintro (%Hn | ⟨%cf, %c, %qs, -, %Hp, He, Hr⟩)
  · exact absurd Hn hW
  iexists cf, c, qs
  iframe
  ipureintro; exact Hp

/-- `netP` opened, at its own configuration. -/
theorem netP_hub0 (γ : Names) (k : Nat) (cid : Nat) (W : List w8) (hW : W ≠ []) :
    netP (GF := GF) γ k cid W ⊢ ∃ (cf : RCfg) (X : Nat) (fs : List MsgV),
      ⌜X < cf.n ∧ cf.n ≤ maxS ∧ W <+: hsBytes X ++ frames (fs.map encMsg) ∧
        ∀ m ∈ fs, (encMsg m).length < 2 ^ 32⌝ ∗
      bcastLb γ X (bcastPart fs) ∗ [∗list] m ∈ fs.filter (·.ty = tyProposalReply), replyOk γ cf k m := by
  unfold netP
  iintro (%Hn | ⟨%cf, %X, %fs, #Hcf, %Hp, Hb, Hr⟩)
  · exact absurd Hn hW
  ihave %Hok := cfgIs_ok γ.rab cf $$ Hcf
  iexists cf, X, fs
  iframe
  ipureintro; exact ⟨Hp.1, RCfg.n_le_maxS cf Hok, Hp.2⟩

/-- `netP` opened at the recorded configuration `cf`. -/
theorem netP_hub (γ : Names) (cf : RCfg) (k : Nat) (cid : Nat) (W : List w8) (hW : W ≠ []) :
    cfgIs γ.rab cf ∗ netP (GF := GF) γ k cid W ⊢ ∃ (X : Nat) (fs : List MsgV),
      ⌜X < cf.n ∧ W <+: hsBytes X ++ frames (fs.map encMsg) ∧ ∀ m ∈ fs, (encMsg m).length < 2 ^ 32⌝ ∗
      bcastLb γ X (bcastPart fs) ∗ [∗list] m ∈ fs.filter (·.ty = tyProposalReply), replyOk γ cf k m := by
  unfold netP
  iintro ⟨#Hcf, H⟩
  icases H with (%Hn | ⟨%cf', %X, %fs, #Hcf', %Hp, Hb, Hr⟩)
  · exact absurd Hn hW
  ihave %Heq := cfgIs_agree γ.rab cf cf' $$ [$Hcf $Hcf']
  subst Heq
  iexists X, fs
  iframe
  ipureintro; exact Hp

/-- `sendP` opened (not a hub request: its definition). -/
theorem sendP_open (γ : Names) (cf : RCfg) (k j p n : Nat) (v : GoSlice) :
    sendP (GF := GF) γ cf k j p n v ⊢ ∃ m : MsgV, v ↦*□ encMsg m ∗
      (if p = 0 then iprop(∃ l, bcastLb γ k l ∗ ⌜l[n]? = some m⌝) else replyOk γ cf j m) := by
  unfold sendP
  by_cases hp : p = 0
  · simp only [hp, ↓reduceIte]
    iintro ⟨%l, %m, #Hl, %Hm, #Hv⟩
    iexists m; iframe Hv; iexists l; iframe Hl; ipureintro; exact Hm
  · simp only [hp, ↓reduceIte]
    iintro ⟨%m, #Hv, #Hr⟩
    iexists m; iframe Hv Hr

end protos

end Perennial.rabia.internal.tcp
