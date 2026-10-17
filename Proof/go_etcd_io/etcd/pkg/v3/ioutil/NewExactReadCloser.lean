/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/ioutil/NewExactReadCloser.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.ioutil.NewExactReadCloser

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
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem ioutil.NewExactReadCloser.wp_proof : ioutil.NewExactReadCloser.spec (GF := GF) (hG := hG) := by
  intro rc total
  wp_start as -
  wp_auto
  wp_alloc e as He
  wp_auto
  iapply HΦ
  iexists e
  isplitr
  · ipureintro; rfl
  iexact He

end proof

end EtcdGrove
end Perennial
