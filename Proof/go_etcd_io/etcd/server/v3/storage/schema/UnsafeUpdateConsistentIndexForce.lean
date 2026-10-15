/-
Proof of `Spec/schema_UnsafeUpdateConsistentIndexForce.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeUpdateConsistentIndexForce
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.unsafeUpdateConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.schema.Assumptions]

theorem schema.UnsafeUpdateConsistentIndexForce.wp_proof
    (hu : schema.unsafeUpdateConsistentIndex.spec (GF := GF) (hG := hG)) :
    schema.UnsafeUpdateConsistentIndexForce.spec (GF := GF) (hG := hG) := by
  intro tx TM PTi PTt m index term
  wp_start as ⟨#Hw, HTM, HPi, HPt⟩
  wp_auto
  wp_bind (App (App (App (App (Val (@! schema.unsafeUpdateConsistentIndex)) (Val #(GoInterface.ok tx)))
      (Val #index)) (Val #term)) (Val #true))
  iapply (hu tx TM PTi PTt m index term true) $$ [HTM HPi HPt]
  · iframe Hpkg Hw HTM HPi HPt
    ipureintro; intro h; cases h
  inext
  iintro HTM
  wp_auto
  iapply HΦ $$ HTM

end proof

end EtcdGrove
end Perennial
