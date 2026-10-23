/-
`NewClient(addr, lg)` (`examples/common/common.go`; 2026-10-22, D33): a client of the one endpoint
`addr` -- `NewClients({addr}, lg)` since 2026-10-23 (`notes/client-timeouts-plan.md` D-T1: the
examples' client configuration, etcdctl's timeouts and keepalive, the default retries; until then
`clientv3.New(Config{Endpoints: {addr}, Logger: lg})` inline). Lean-first (no Rocq counterpart).

**The triple:** `NewClients.spec` at the one-element slice (`plainEndpoints` of it from the plain
endpoint): a new client of `[addr]` at the watch environment `V`, the caller's choice, or an error
and `nil`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.common.NewClients

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.common.Assumptions]

/-- See the file header. -/
abbrev NewClient.spec : Prop :=
  ∀ (addr : GoString) (lg : Loc) (V : client.WEnv GF),
  lg ≠ null → plainEndpoint addr → threadBound GF ≤ 2 ^ 31 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.common }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.common.NewClient))
      (Val #addr)) (Val #lg))
  {{ (cl : Loc) (err : GoInterface), RET (PairV #cl #err);
      (⌜err = GoInterface.nil⌝ ∗ isNewClient cl [addr] V) ∨
      ⌜err ≠ GoInterface.nil ∧ cl = null⌝ }}

end spec

end common
end EtcdGrove
end Perennial
