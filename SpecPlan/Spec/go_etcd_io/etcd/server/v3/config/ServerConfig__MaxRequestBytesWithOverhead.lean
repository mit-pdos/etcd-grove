/-
## `(*ServerConfig).MaxRequestBytesWithOverhead()` (`config.go:354-356`)

**Users.** v3rpc's server options (the gRPC receive limit), the watch server's budget (2a, 2b).
**Proof sketch.** A field read plus `grpcOverheadBytes` (`512 * 1024`), wrapping. **Changes**: from
`specs-ref`. **Margin.** Exact.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.config.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Config

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.config.Assumptions]

/-- **`MaxRequestBytesWithOverhead()`**: `MaxRequestBytes + 512 KiB` (wrapping). -/
def ServerConfig.MaxRequestBytesWithOverhead.spec : Prop :=
  ∀ (c : Loc) (n : w64),
  {{ (typedPointsto (structFieldRef go_etcd_io.etcd.server.v3.config.ServerConfig go!"MaxRequestBytes" c) n DFrac.discard : IProp GF) }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.config.ServerConfig.ty @!! go!"MaxRequestBytesWithOverhead")) (Val #()))
  {{ RET #(n + W64 524288); True }}

end spec

end Config
end EtcdGrove
end Perennial
