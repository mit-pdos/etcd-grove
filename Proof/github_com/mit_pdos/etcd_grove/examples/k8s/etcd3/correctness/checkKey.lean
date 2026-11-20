module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.checkKey
public import Spec.k8s_io.apiserver.pkg.storage.PrepareKey

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Assumptions]

theorem checkKey.wp_proof
    (wp_PrepareKey : storage.PrepareKey.spec (GF := GF) (hG := hG)) :
    checkKey.spec (GF := GF) (hG := hG) := by
  intro key r
  wp_start as -
  wp_auto
  wp_apply wp_PrepareKey as %k %err %h
  iapply HΦ
  ipureintro
  revert h
  cases k8s.prepareKeyM [] key r with
  | none => intro h; simp [h]
  | some k' => intro h; simp [h.2]

end proof

end k8s_correctness
end EtcdGrove
end Perennial
