/-
Lean-first (no Rocq counterpart). #33 S3b W4a (2026-11-23): the proof of `x.bat()` (B 291-359, `OnDisk.bat`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__bat
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk__w
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Event__has
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.StateLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.EvalLaws

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

theorem onDisk.bat.wp_proof (wp_w : onDisk.w.spec (GF := GF) (hG := hG))
    (wp_has : Event.has.spec (GF := GF) (hG := hG)) :
    onDisk.bat.spec (GF := GF) (hG := hG) := by
  intro g x
  wp_start as #Hx
  wp_auto
  rw [github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.onDisk.TypeAssumptions.ptr_unfold'w.method_unfold]
  try wp_auto
  wp_apply wp_w g x $$ [Hx] as %e #He
  · iexact Hx
  try wp_auto
  rw [show (github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.FEntries : val) = #fEntries from rfl]
  wp_apply wp_has e x.w fEntries x.w.entries.isSome $$ [He]
  · iframe He; ipureintro; exact Event.hasF_Entries _
  try wp_auto
  have : (!x.w.entries.isSome) = x.bat := by unfold OnDisk.bat; cases x.w.entries <;> rfl
  rw [this]
  iapply HΦ; ipureintro; trivial

end proof

end AntCheck
end EtcdGrove
end Perennial
