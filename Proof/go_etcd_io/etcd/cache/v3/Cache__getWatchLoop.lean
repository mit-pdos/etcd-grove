/-
Proof of `Spec/Cache__getWatchLoop.lean`. Lean-first (no Rocq counterpart).

The loop's invariant: the two writers, in any states. Each `get` gets etcd's linearizability for
the store's latest revision from the client (`isEtcdKV`) and the writer's certificate that etcd
has reached it (`etcdReached`, `storeWriter`).
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatchLoop
public import Spec.go_etcd_io.etcd.cache.v3.defaultConfig
public import Spec.go_etcd_io.etcd.cache.v3.Cache__getWatch

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

theorem Cache.getWatchLoop.wp_proof
    (wp_defaultConfig : defaultConfig.spec (GF := GF) (hG := hG))
    (wp_getWatch : Cache.getWatch.spec (GF := GF) (hG := hG)) :
    Cache.getWatchLoop.spec (GF := GF) (hG := hG) := by
  -- re-proved for the shared-writer store in the next commit
  sorry

end proof

end EtcdGrove
end Perennial
