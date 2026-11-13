/-
`ioutil.NewPageWriter` (see `LinuxFs/Spec/go_etcd_io/etcd/pkg/v3/ioutil/NewPageWriter.lean`).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.pkg.v3.ioutil.NewPageWriter

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

theorem go_etcd_io.etcd.pkg.v3.ioutil.NewPageWriter.wp_proof :
    go_etcd_io.etcd.pkg.v3.ioutil.NewPageWriter.spec (GF := GF) (hG := hG) := by
  intro wi pB off hpB hpBle hoff0 hoff1
  wp_start
  ihave #Hi : (ioutil.ioutilInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  wp_auto
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %vsl ⟨-, -⟩
  wp_auto
  wp_func_call
  wp_call
  rw [show decide (sint.Z (W64 0) < sint.Z pB) = true by simp only [decide_eq_true_eq]; word]
  wp_auto
  have hsum : sint.Z (W64 131072 + pB) = 131072 + sint.Z pB := by word
  wp_apply wp_slice_make2 (V := w8) (W64 131072 + pB) $$ [] as %buf ⟨Hbuf, -⟩
  · ipureintro; omega
  iapply HΦ
  iunfold ioutil.ownPageWriter
  iexists _, _
  iframe «$r0»
  dsimp only
  iframe
  ipureintro
  refine ⟨rfl, rfl, ioutil.pwOk_of_le hpB hpBle hoff0 hoff1 (by decide) (by decide) ?_, by simp⟩
  rw [List.length_replicate]
  have : sint.nat (W64 131072 + pB) = (sint.Z (W64 131072 + pB)).toNat := rfl
  simp only [ioutil.wmBytes]
  omega

end proof

end EtcdGrove
end Perennial
