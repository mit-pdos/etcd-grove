/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/BackendConfig__mmapSize.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.BackendConfig__mmapSize

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]

theorem backend.BackendConfig.mmapSize.wp_proof :
    backend.BackendConfig.mmapSize.spec (GF := GF) (hG := hG) := by
  intro c cfg
  wp_start as Hm
  wp_auto
  iapply HΦ
  iframe

end proof

end EtcdGrove
end Perennial
