/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/ioutil/exactReadCloser__Close.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.ioutil.exactReadCloser__Close

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

theorem ioutil.exactReadCloser.Close.wp_proof : ioutil.exactReadCloser.Close.spec (GF := GF) (hG := hG) := by
  intro e rc C br total
  wp_start as ⟨He, #Hcl, HC⟩
  wp_auto
  iunfold closerSpec at Hcl
  wp_apply Hcl $$ [$HC] as %err -
  ihave Hei : (go_etcd_io.etcd.pkg.v3.ioutil.ioutilInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hei with ⟨%e1, %e2, #Hshort, #Hexp, -⟩
  cases err with
  | ok ei =>
    wp_auto
    iapply HΦ
    iframe He
    ileft
    ipureintro; intro h; cases h
  | nil =>
    wp_auto
    wp_if_destruct
    · iapply HΦ
      iframe He
      iright; ileft
      iframe Hshort
      ipureintro; exact Hif
    · iapply HΦ
      iframe He
      iright; iright
      ipureintro; exact ⟨Hif, rfl⟩

end proof

end EtcdGrove
end Perennial
