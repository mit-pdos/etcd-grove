/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8sdaemonset/dsmain/Main.lean` over its callees' specs. Lean-first; Stage 3 of the autoverify run
(track C, `notes/k8s-daemonset-run/design.md`): a stub.

The plan: `serverConfig`, then `run`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.serverConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.run

@[expose] public section

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace dsmain

open Iris Iris.BI Iris.ProofMode apimodel dsctl informers

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8sdaemonset.dsmain.Assumptions]

theorem Main.wp_proof
    (wp_serverConfig : dsmain.serverConfig.spec (GF := GF) (hG := hG))
    (wp_run : dsmain.run.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro nchk
  wp_start as ⟨Htt, %Htb, %Hrb, Hname⟩
  wp_auto
  wp_apply wp_serverConfig
  -- **The one false obligation of the closed theorem** (decision R8): `run`'s premise at
  -- `serverConfig()`, whose model has ambiguous writes on. False of the code as it is: the
  -- D51 bug, `issues/k8s-daemonset-ambiguous-create-duplicate-pod.md` (a create that commits
  -- and reports a timeout leads a later sync to a second pod on the node:
  -- `ambiguous_create_breaks_S1`).
  have hamb : dsCfg.AmbiguousWrites' = false := by
    sorry -- the D51 bug
  try wp_auto
  wp_apply (wp_run dsCfg nchk) $$ [Htt Hname] as %n -
  · iframe #; iframe; ipureintro; exact ⟨Htb, Hrb, hamb⟩
  try wp_auto
  iapply HΦ
  itrivial

end proof

end dsmain
end EtcdGrove
end Perennial
