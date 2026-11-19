/-
`state.typedObj`: `AsTyped(NewValueInterface(obj), s.sc, TypeRef{NamedType: &"root"})` on a
conforming object (`isValF_persist`, `isTypeRef_intro`; the schema in scope: `Steps.sc0_wf`).
Lean-first (2026-11-19).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.smd.state__typedObj
public import Spec.sigs_k8s_io.structured_merge_diff.v7.value.NewValueInterface
public import Spec.sigs_k8s_io.structured_merge_diff.v7.typed.AsTyped
public import Proof.sigs_k8s_io.structured_merge_diff.v7.Laws
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.smd.Steps

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_smd

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open smd

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.smd.Assumptions]

theorem state.typedObj.wp_proof_of (hPersist : isValF_persist.law (GF := GF))
    (hTR : isTypeRef_intro.law (GF := GF))
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_AsTyped : smd.typed.AsTyped.spec (GF := GF)) :
    state.typedObj.spec (GF := GF) := fun s sc u lv mfm m kvs hconf => by
  wp_start as ⟨Hs, Hsc, Hm⟩
  wp_auto
  wp_apply (wp_NewValueInterface _ (.map kvs)) $$ [Hm] as %v Hv
  · unfold isUMap; iexact Hm
  imod (hPersist _ _ _) $$ Hv with Hv
  ipersist rootName
  wp_apply (wp_AsTyped v (.map kvs) sc sc0 _ rootRef) $$ [Hsc Hv] as %p %err ⟨%herr, Hp⟩
  · iframe Hsc Hv
    isplitr
    · iapply (hTR _ rootRef rfl rfl rfl rfl rfl)
      iexact rootName
    · ipureintro; exact ⟨sc0_wf, hconf⟩
  subst herr
  wp_auto
  iapply HΦ
  iframe

theorem state.typedObj.wp_proof
    (wp_NewValueInterface : smd.value.NewValueInterface.spec (GF := GF))
    (wp_AsTyped : smd.typed.AsTyped.spec (GF := GF)) :
    state.typedObj.spec (GF := GF) :=
  state.typedObj.wp_proof_of sorry sorry wp_NewValueInterface wp_AsTyped

end proof

end k8s_smd
end EtcdGrove
end Perennial
