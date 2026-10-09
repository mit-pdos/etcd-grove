/-
Proof of `Spec/Cache__getWatch.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatch
public import Spec.go_etcd_io.etcd.cache.v3.Cache__get
public import Spec.go_etcd_io.etcd.cache.v3.Cache__watch

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

theorem Cache.getWatch.wp_proof
    (wp_get : Cache.get.spec (GF := GF) (hG := hG))
    (wp_watch : Cache.watch.spec (GF := GF) (hG := hG)) :
    Cache.getWatch.spec (GF := GF) (hG := hG) := by
  -- re-proved for the shared-writer store in the next commit
  sorry

end proof

end EtcdGrove
end Perennial
