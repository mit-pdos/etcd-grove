/-
Proof of `Spec/ExactKey.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.ExactKey

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

set_option linter.unusedSectionVars false

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem ExactKey.wp_proof :
    ExactKey.spec (GF := GF) (hG := hG) := by
  intro sl key
  wp_start as #Hkey
  iapply wp_fupd
  wp_auto
  ipersist key
  imodintro
  simp only [recv_eq_func_mk]
  iapply HΦ
  isplitr
  · ipureintro; intro h; cases h
  unfold keyPredSpec
  iintro %sl' %k
  simp only [exactKeyPred]
  wp_start as #Hk
  wp_auto
  wp_apply bytes.wp_Equal sl' sl DFrac.discard DFrac.discard k key $$ [$Hk $Hkey] as -
  wp_end

end proof

end EtcdGrove
end Perennial
