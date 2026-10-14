/-
`api.IsCapabilityEnabled` (`etcdserver/api/capability.go`, names-only: the trust boundary of unit
P3b; the server's unary interceptor asks for the v3 RPC capability). Lean-first (no Rocq
counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- `api.IsCapabilityEnabled(c)` returns whether the capability `c` is enabled (some boolean;
it reads the package's `enabledMap` under its `enableMapMu` read lock, which the package's
`UpdateCapability` writes under the lock). -/
abbrev api.IsCapabilityEnabled.spec : Prop :=
  ∀ (c : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api }}
    (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.IsCapabilityEnabled)) (Val c))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
