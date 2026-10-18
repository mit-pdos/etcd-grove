/-
`storage.NewBackendQuota`: the trust boundary (`server/v3/storage` is names-only). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Contracts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI 

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.apply.Assumptions]

/-- `NewBackendQuota(lg, cfg, be, name)` (`newQuotaApplierV3`): a `Quota` (`isQuota`: a
`passthroughQuota` for a negative `cfg`, else a `BackendQuota` over `be`; it sets a gauge and
logs once). Its `Available` answers true only under the named workload premise
`apply.backendUnderQuota` (audit phase B3, D19h, 2026-10-18: until then unconditional, false of
Go once the backend reaches the quota). -/
abbrev storage.NewBackendQuota.spec : Prop :=
  ∀ (lg : Loc) (cfg : w64) (be : GoInterface) (name : GoString),
  apply.backendUnderQuota →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage }}
    (App (App (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.NewBackendQuota)) (Val #lg))
      (Val #cfg)) (Val #be)) (Val #name))
  {{ (q : GoInterface), RET #q; apply.isQuota q }}

end spec

end EtcdGrove
end Perennial
