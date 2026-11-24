/-
Lean-first (no Rocq counterpart). #33 S3b W3 (2026-11-23): the proof of `x.es()` (B 214-230, `InMem.es`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.inMem__es
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__entries
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Init0Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
set_option linter.unusedSimpArgs false
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem inMem.es.wp_proof
    (wp_has : Event.has.spec (GF := GF) (hG := hG))
    (wp_entries : Event.entries.spec (GF := GF) (hG := hG)) :
    inMem.es.spec (GF := GF) (hG := hG) := by
  intro gx x v
  wp_start as ⟨#Hx, %Hv⟩
  ihave #Hx' := Hx
  iunfold inMemRO at Hx'
  icases Hx' with ⟨#Hs, #He, %Hp⟩
  wp_auto
  unfold InMem.es at Hv
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FEntries : val) = #fEntries from rfl]
  wp_apply wp_has gx.ev' x.ev fEntries x.ev.entries.isSome $$ [He]
  · iframe He; ipureintro; exact Event.hasF_Entries _
  cases h : x.ev.entries.isSome
  · simp only [h, Bool.false_eq_true, ite_false, pure_ok, Except.ok.injEq] at Hv
    subst Hv
    try wp_auto
    iapply HΦ; iapply Init0_logNil
  · simp only [h, ite_true] at Hv
    try wp_auto
    wp_apply wp_entries gx.ev' x.ev v $$ [He] as %u #Hu
    · iframe He; ipureintro; exact Hv
    try wp_auto
    iapply HΦ; iexact Hu

end proof

end AntCheck
end EtcdGrove
end Perennial
