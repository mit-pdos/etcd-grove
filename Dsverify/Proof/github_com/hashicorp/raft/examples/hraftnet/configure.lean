/-
`hraftnet.configure`'s proof (vr's `Configure.wp_proof`, `vsrnet/Conf.lean`): `ConfAddrs()`, then for
every server machine `sendConf` of the drawn size until it is acknowledged, `RetryMs` apart.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.configure
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.sendConf
public import Dsverify.Spec.github_com.hashicorp.raft.examples.hraftnet.ConfAddrs
public import Perennial.Proof.time.Link

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace github_com.hashicorp.raft.examples.hraftnet

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]
variable [π : NetProtoGS]

set_option goose.wp.extras true

theorem configure.wp_proof (wp_ConfAddrs : ConfAddrs.spec (GF := GF))
    (wp_sendConf : sendConf.spec (GF := GF)) :
    configure.spec (GF := GF) := by
  intro γc n hn
  wp_start as ⟨#Hps, #Hf⟩
  wp_auto
  wp_apply wp_ConfAddrs as %cfgs ⟨%L, Hcfgs, %HL⟩
  subst HL
  ihave %Hclen := ownSlice_len $$ Hcfgs
  ihave IH : iprop(∃ (k : w64), "i" ∷ i_ptr ↦ k ∗ "Hcfgs" ∷ cfgs ↦* confAddrs ∗
      "%Hk" ∷ ⌜1 ≤ uint.nat k ∧ uint.nat k ≤ 7⌝) $$ [i Hcfgs]
  · iexists _; iframe; ipureintro; exact ⟨by decide, by decide⟩
  wp_for IH
  by_cases Hif : uint.Z k ≤ uint.Z (W64 6)
  · simp only [Hif, decide_true, ↓reduceIte]
    have hk6 : uint.nat k ≤ 6 := by word
    obtain ⟨a, ha⟩ : ∃ a, confAddrs[uint.nat k - 1]? = some a :=
      ⟨_, List.getElem?_eq_getElem (by simp [confAddrs]; omega)⟩
    ihave #Hps' := Hps
    iunfold confProtos at Hps'
    ihave #Hpa := (BigSepL.bigSepL_lookup (PROP := IProp GF)
      (Φ := fun _ a => addrProto (Gg := hG.goose_globalGS) a (confProto γc) ackProto) ha) $$ Hps'
    wp_call
    wp_for
    have hb : 0 ≤ sint.Z (k - W64 1) ∧ sint.Z (k - W64 1) < sint.Z cfgs.len := by
      have : confAddrs.length = 6 := rfl
      rw [this] at Hclen
      constructor <;> word
    rw [ite_eq_left hb]
    wp_apply wp_load_slice_index cfgs (sint.Z (k - W64 1)) _ (DFrac.own 1) a hb.1 $$ [$Hcfgs] as Hcfgs
    · ipureintro; rw [show (sint.Z (k - W64 1)).toNat = uint.nat k - 1 by word]; exact ha
    wp_apply (wp_sendConf γc a n hn) $$ [$Hpa $Hf] as %ok -
    cases ok
    · simp only [Bool.not_false]
      cleanup_bool_decide
      wp_auto
      wp_apply time.wp_Sleep
      wp_for_post
      iframe
    · simp only [Bool.not_true]
      cleanup_bool_decide
      wp_for_post
      iframe
      iexists _
      iframe
      ipureintro
      constructor <;> word
  · simp only [Hif, decide_false, Bool.false_eq_true, ↓reduceIte]
    wp_auto
    iapply HΦ
    itrivial

end proof

end github_com.hashicorp.raft.examples.hraftnet

end Perennial
