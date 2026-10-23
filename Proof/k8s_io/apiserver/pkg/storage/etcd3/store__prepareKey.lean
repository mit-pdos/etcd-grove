/-
Lean-first (no Rocq counterpart).

The proof of `(*store).prepareKey`: `PrepareKey`, then the path prefix.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.store__prepareKey
public import Spec.k8s_io.apiserver.pkg.storage.PrepareKey

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem store.prepareKey.wp_proof
    (wp_PrepareKey : storage.PrepareKey.spec (GF := GF) (hG := hG)) :
    store.prepareKey.spec (GF := GF) (hG := hG) := by
  intro sp rp pp key r
  wp_start as ⟨#Hrp, #Hpp⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage $$ []
  · iPkgInit
  wp_auto
  wp_apply wp_PrepareKey rp key r as %k %err %Hk
  (try wp_auto)
  cases hp : prepareKeyM rp key r with
  | none =>
    rw [hp] at Hk
    cases err with
    | nil => exact absurd rfl Hk
    | ok ei =>
      wp_auto
      iapply HΦ
      ipureintro
      exact Hk
  | some k' =>
    rw [hp] at Hk
    obtain ⟨rfl, rfl⟩ := Hk
    wp_auto
    iapply HΦ
    ipureintro
    exact ⟨rfl, rfl⟩

end proof

end k8s
end EtcdGrove
end Perennial
