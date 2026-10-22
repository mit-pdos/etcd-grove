/-
Lean-first (no Rocq counterpart).

The proof of `refreshOnError` for a current state: the first branch.
-/
module

public import Spec.k8s_io.apiserver.pkg.storage.etcd3.refreshOnError

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option maxRecDepth 16384

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.apiserver.pkg.storage.etcd3.Assumptions]

theorem refreshOnError.wp_proof : refreshOnError.spec (GF := GF) (hG := hG) := by
  intro _ _ Obj _ c st s err f hcur
  wp_start as Hs
  iunfold ownState at Hs
  icases Hs with ⟨%x, %m, %dsl, %Hst, Hst, Hobj, #Hdsl, Hm⟩
  wp_auto
  simp only [hcur]
  wp_auto
  iapply HΦ
  isplitr
  · ipureintro; exact ⟨rfl, rfl⟩
  iunfold ownState
  rw [hcur]
  iexists x, m, dsl
  iframe Hst Hobj Hdsl Hm
  ipureintro; exact Hst

end proof

end k8s
end EtcdGrove
end Perennial
