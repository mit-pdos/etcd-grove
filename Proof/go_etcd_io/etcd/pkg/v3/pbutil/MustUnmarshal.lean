/-
Proof of `pbutil.MustUnmarshal` (`pbutil.go:40`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshal

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.pbutil.Assumptions]

theorem pbutil.MustUnmarshal.wp_proof :
    pbutil.MustUnmarshal.spec (GF := GF) (hG := hG) := by
  intro ty r_ptr data P Q
  wp_start as ⟨HP, Hwp⟩
  wp_auto
  wp_bind (App (Val (r_ptr @!! ty @!! go!"Unmarshal")) (Val #data))
  iapply wp_wand $$ [HP Hwp]
  · iapply Hwp $$ HP
  iintro %err ⟨%Herr, HQ⟩
  subst Herr
  wp_auto
  iapply HΦ $$ HQ

end proof

end EtcdGrove
end Perennial
