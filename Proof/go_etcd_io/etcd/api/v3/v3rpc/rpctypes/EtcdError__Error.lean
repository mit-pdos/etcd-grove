/-
Proof of `Spec/go_etcd_io/etcd/api/v3/v3rpc/rpctypes/EtcdError__Error.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError__Error

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.cache.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.api.v3.v3rpc.rpctypes.Assumptions]

theorem rpctypes.EtcdError.Error.wp_proof : rpctypes.EtcdError.Error.spec (GF := GF) (hG := hG) := by
  intro e
  wp_start
  wp_auto
  wp_end

end proof

end EtcdGrove
end Perennial
