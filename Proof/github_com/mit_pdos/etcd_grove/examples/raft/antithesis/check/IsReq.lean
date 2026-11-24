/-
Lean-first (no Rocq counterpart). #33 S3b W1 (2026-11-23): the proof of `IsReq` (B 75).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.IsReq
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg__typ

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntCheck

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

theorem IsReq.wp_proof (wp_typ : Msg.typ.spec (GF := GF) (hG := hG)) :
    IsReq.spec (GF := GF) (hG := hG) := by
  intro g m b
  wp_start as ⟨#Hm, %Hb⟩
  unfold isReq at Hb
  cases h1 : m.typ with
  | error _ => rw [h1] at Hb; cases Hb
  | ok t =>
  rw [h1] at Hb
  have hb := Except.ok.inj Hb
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
  try wp_auto
  wp_apply wp_typ g m t $$ [Hm]
  · iframe Hm; ipureintro; exact h1
  try wp_auto
  wp_if_destruct
  · try wp_auto
    (cases b <;> first | (iapply HΦ; ipureintro; trivial) | (exfalso; simp_all; done))
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
  try wp_auto
  wp_apply wp_typ g m t $$ [Hm]
  · iframe Hm; ipureintro; exact h1
  try wp_auto
  wp_if_destruct
  · try wp_auto
    (cases b <;> first | (iapply HΦ; ipureintro; trivial) | (exfalso; simp_all; done))
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Msg.TypeAssumptions.ptr_unfold'typ.method_unfold]
  try wp_auto
  wp_apply wp_typ g m t $$ [Hm]
  · iframe Hm; ipureintro; exact h1
  try wp_auto
  wp_if_destruct
  · try wp_auto
    (cases b <;> first | (iapply HΦ; ipureintro; trivial) | (exfalso; simp_all; done))
  try wp_auto
  (cases b <;> first | (iapply HΦ; ipureintro; trivial) | (exfalso; simp_all; done))

end proof

end AntCheck
end EtcdGrove
end Perennial
