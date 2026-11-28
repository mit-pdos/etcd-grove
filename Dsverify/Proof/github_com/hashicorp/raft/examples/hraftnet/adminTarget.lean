/-
`hraftnet.adminTarget`'s proof: a random server `j`, or, one time in two, a `Status` call to it
(`status_dep`: the deposit from what the admin knows) and, if it names a leader among the servers,
that one.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.adminTarget
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rnd
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.serverID
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.apiTimeout
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Conn__Call
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.CodecApi

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

open github_com.hashicorp.raft rpctransport service

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS] [rsem : github_com.hashicorp.raft.Assumptions]

set_option goose.wp.extras true

theorem adminTarget.wp_proof (wp_rnd : rnd.spec (GF := GF))
    (wp_serverID : serverID.spec (GF := GF))
    (wp_apiTimeout : apiTimeout.spec (GF := GF))
    (wp_Call : rpctransport.Conn.Call.spec (GF := GF) (hG := hG)) :
    adminTarget.spec (GF := GF) := by
  intro K sl ps
  wp_start as ⟨#Hcod, #Hac, #Hps, %Hpl, #Hcs⟩
  ihave #Hac' := Hac
  iunfold adminCtx at Hac'
  icases Hac' with ⟨%Hss, -⟩
  wp_auto
  wp_apply (wp_rnd (W64 6) (by decide)) as %x %Hx
  have hx : uint.Z x < 6 := Hx
  have hj1 : 1 ≤ uint.Z (W64 1 + x) ∧ uint.Z (W64 1 + x) ≤ 6 := by constructor <;> word
  wp_apply (wp_rnd (W64 2) (by decide)) as %y %Hy
  wp_if_destruct
  · iapply HΦ; ipureintro; exact hj1
  wp_alloc ap as Hap
  wp_auto
  wp_apply wp_apiTimeout as %dd -
  ihave %Hlen := ownSlice_len _ _ _ $$ Hps
  have hjn : uint.nat (W64 1 + x) - 1 < 6 := by word
  obtain ⟨p, hp⟩ : ∃ p, ps[uint.nat (W64 1 + x) - 1]? = some p :=
    ⟨_, List.getElem?_eq_getElem (by rw [Hpl]; exact hjn)⟩
  have hs : 0 ≤ sint.Z (W64 1 + x - W64 1) ∧ sint.Z (W64 1 + x - W64 1) < sint.Z sl.len := by
    have h1 := Hlen.1; rw [Hpl] at h1; constructor <;> word
  rw [ite_eq_left hs]
  have hidx : (sint.Z (W64 1 + x - W64 1)).toNat = uint.nat (W64 1 + x) - 1 := by word
  wp_apply wp_load_slice_index sl (sint.Z (W64 1 + x - W64 1)) _ DfracDiscarded p hs.1 $$ [Hps] as -
  · iframe Hps; ipureintro; rw [hidx]; exact hp
  ihave #Hc := BigSepL.bigSepL_lookup hp $$ Hcs
  ipersist Hap
  wp_apply (wp_Call p K.W (serverAddrs.getD (uint.nat (W64 1 + x) - 1) go!"") go!"API.Status" go!"API"
      go!"Status" (apiSvcK K) (ptrI AdminArgs.ty ap) (ptrI StatusReply.ty «$r0_ptr»)
      statusAns iprop(True) iprop(«$r0_ptr» ↦ (Perennial.zero_val StatusReply))
      (fun _ _ => iprop(∃ w : StatusReply, «$r0_ptr» ↦ w))
      hraftCodec dd iprop(True))
    $$ [$Hc $Hcod «$r0»] as %r Hr
  · isplitr
    · ipureintro
      refine ⟨by decide, ?_, by simp [ptrI, interface.mkOk]⟩
      rw [Hss.1 (uint.nat (W64 1 + x)) go!"API" (by word) (by word)]
      simp [rpctransport.svcName]
    isplitr
    · ipureintro; decide
    isplitr
    · itrivial
    isplitr
    · iintro -
      iapply (enc_AdminArgs ap DfracDiscarded (AdminArgs.mk [] []) ⟨[], []⟩)
      iframe Hap
      isplitr
      · unfold adminArgsOwn; ipureintro; exact ⟨rfl, rfl⟩
      iintro - -
      isplitr
      · ipureintro; exact encAdminArgs_length _ (by simp) (by simp)
      isplitl
      · iapply status_dep K $$ Hac
      itrivial
    iframe «$r0»
    imodintro
    simp only [statusAns]
    iintro HD %rep %Hrep
    obtain ⟨r, rfl⟩ := Hrep (by simp)
    iapply (dec_StatusReply _ r)
    iframe HD
    iintro %w Hw -
    iexists w
    iexact Hw
  icases Hr with (⟨%Hr0, -, %rep, %w, Hw⟩ | ⟨%Hr1, -, -⟩ | %Hr2)
  rotate_left
  · subst Hr1
    (try wp_auto)
    iapply HΦ; ipureintro; exact hj1
  · subst Hr2
    (try wp_auto)
    iapply HΦ; ipureintro; exact hj1
  subst Hr0
  (try wp_auto)
  cases hl : w.Leader'
  · (try wp_auto)
    ihave IH : iprop(∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "%Hk" ∷ ⌜1 ≤ uint.Z k ∧ uint.Z k ≤ 7⌝) $$ [i]
    · iexists _; iframe; ipureintro; constructor <;> word
    wp_for IH
    by_cases Hif : uint.Z k ≤ uint.Z (W64 6)
    · simp only [Hif, decide_true, ↓reduceIte]
      (try wp_auto)
      wp_apply wp_serverID
      (try wp_auto)
      wp_if_destruct
      · wp_for_post
        iapply HΦ; ipureintro; constructor <;> word
      · wp_for_post
        iframe
        iexists _
        iframe
        ipureintro; constructor <;> word
    · simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
      wp_auto
      iapply HΦ; ipureintro; exact hj1
  · (try wp_auto)
    iapply HΦ; ipureintro; exact hj1

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
