/- Lean-first (no Rocq counterpart).

# `Client`'s proof

The counter of ids (`isCtr`: its mutex made over `ctrInv` at `start`, the random start, with the
take budget's 132 credits, `ctrBudget`); then at most 4 dials, each followed by `callOn` (32 credits)
and, after `Close` (`cliClosed`), one call on the closed client, which fails with an error that is
not a `ServerError` (`Client.Call.spec_closed`; one credit for its request's id).
-/
module

public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Client
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.callOn
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.dial
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.randomArgs
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.below
public import Net.Spec.net.rpc.Client__Close
public import Net.Spec.net.rpc.Client__Call
public import Perennial.Spec.github_com.goose_lang.primitive.RandomUint64
public import Perennial.Proof.sync.Link

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem Client.wp_proof
    (wp_RandomUint64 : github_com.goose_lang.primitive.RandomUint64.spec (GF := GF) (hG := hG))
    (wp_below : below.spec (GF := GF) (hG := hG))
    (wp_dial : dial.spec (GF := GF) (hG := hG))
    (wp_callOn : callOn.spec (GF := GF) (hG := hG))
    (wp_randomArgs : randomArgs.spec (GF := GF) (hG := hG))
    (wp_Close : net.rpc.Client.Close.spec_closed (GF := GF) (hG := hG))
    (wp_CallClosed : net.rpc.Client.Call.spec_closed (GF := GF) (hG := hG)) :
    Client.spec (GF := GF) (hG := hG) := by
  intro γid reg
  wp_start as ⟨%Hb, Htok, #Hstr, #Hsync, #Hnet, #Hf, #Hset, %Hrb, #Hcli, #Hhttp, #Hcon, #Htcp, #Hha, Hauth⟩
  try wp_auto
  wp_apply wp_RandomUint64 as %start -
  try wp_auto
  irename «$r0» => Hc
  generalize «$r0_ptr» = c at *
  -- the counter's fields (its blank `_` field holds `True`)
  icases typedPointsto_split _ _ _ $$ Hc with Hc
  try simp only [TypedPointsto.typedPointstoDef]
  icases Hc with ⟨mu, next, -⟩
  -- the credits and the counter's mutex
  imod ownTokAuth_alloc (GF := GF) with ⟨%γb, Hba⟩
  imod ownTokAuth_add ctrBudget γb 0 $$ Hba with ⟨Hba, Hcred⟩
  imod sync.init_Mutex (ctrInv γid γb start c) ⊤ (structFieldRef counter go!"mu" c)
    $$ mu [next Hauth Hba] with #Hmu
  · inext
    unfold ctrInv
    iexists 0, 0 + ctrBudget
    rw [show start + W64 ((0 : Nat) : Int) = start by word]
    iframe
    ipureintro; omega
  ihave #Hctr : isCtr γid γb c $$ []
  · unfold isCtr; iframe Hsync; iexists start; iexact Hmu
  wp_apply wp_below (W64 4) as %n0 %Hn0
  have hn0 : uint.Z n0 < 4 := Hn0.2 (by decide)
  try wp_auto
  -- the dials
  have hN : uint.nat (W64 1 + n0) ≤ 4 := by word
  -- drop the credits beyond `33` per dial
  rw [show ctrBudget = 33 * uint.nat (W64 1 + n0) + (ctrBudget - 33 * uint.nat (W64 1 + n0))
    by unfold ctrBudget; omega]
  icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, -⟩
  ihave IH : iprop(∃ k : w64, "k" ∷ k_ptr ↦ k ∗
      "Hcred" ∷ ownToks γb (33 * (uint.nat (W64 1 + n0) - uint.nat k)) ∗
      "Htok" ∷ threadTok ∗ "%Hk" ∷ ⌜uint.nat k ≤ uint.nat (W64 1 + n0)⌝) $$ [k Hcred Htok]
  · iexists W64 0
    iframe k Htok
    rw [show uint.nat (W64 0) = 0 by rfl, Nat.sub_zero]
    iframe Hcred
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · have hk : uint.nat k < uint.nat (W64 1 + n0) := by word
    rw [show 33 * (uint.nat (W64 1 + n0) - uint.nat k) =
      33 * (uint.nat (W64 1 + n0) - uint.nat (k + W64 1)) + 32 + 1 by
        rw [show uint.nat (k + W64 1) = uint.nat k + 1 by word]; omega]
    icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, Hc1⟩
    icases ownToks_add_1 _ _ γb $$ Hcred with ⟨Hcred, Hc32⟩
    wp_apply wp_dial (drvWorld γid reg) $$ [$Hnet $Hcli $Hhttp $Hcon $Htcp $Hha] as %cl %err Hd
    · ipureintro; exact Hrb
    icases Hd with (⟨%He, %a, %Ha, #Hcl⟩ | %He)
    · subst He
      try wp_auto
      have hSS : (drvWorld (GF := GF) γid reg).SS a go!"Svc" = some (echoSvc γid) := by
        rcases Ha with rfl | rfl
        · exact (drvWorld_tcp γid reg).1
        · exact (drvWorld_http γid reg).1
      wp_apply wp_callOn γid γb cl c (drvWorld γid reg) a hSS
        $$ [$Hf $Hstr $Hcl $Hset $Hctr $Hc32 $Htok] as Htok
      · ipureintro; exact Hb
      wp_apply wp_Close cl (drvWorld γid reg) a $$ [$Hcl] as %e2 ⟨-, #Hclosed⟩
      wp_apply wp_randomArgs γid γb c $$ [$Hf $Hctr $Hc1] as %pa -
      try wp_auto
      wp_alloc pr as Hpr
      try wp_auto
      wp_apply wp_CallClosed cl (drvWorld γid reg) a go!"Svc.Echo" _ _ $$ [$Hcl $Hclosed]
        as %err3 %He3
      obtain ⟨hne3, hns3⟩ := He3
      cases err3 with
      | nil => exact absurd rfl hne3
      | ok e3 =>
        have hty : e3.ty ≠ net.rpc.ServerError.ty := hns3 e3 rfl
        try wp_auto
        simp only [hty, ↓reduceIte, decide_false]
        iunfold drvFacts at Hf
        icases Hf with ⟨-, %fr, #Hrg, #Hrf⟩
        try wp_auto
        wp_bind (App (Val #fr) (Val _))
        iapply wp_wand $$ (Hrf $$ %go!"close")
        iintro %v %Hv
        subst Hv
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1
        iframe
        ipureintro; word
    · -- the dial failed: on to the next
      cases err with
      | nil => exact absurd rfl He
      | ok e =>
        try wp_auto
        wp_for_post
        iframe
        iexists k + W64 1
        iframe
        ipureintro; word
  · try wp_auto
    iapply HΦ
    iexact Htok

end proof

end github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
end Perennial
