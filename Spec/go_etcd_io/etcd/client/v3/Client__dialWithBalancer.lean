/-
`c.dialWithBalancer(dopts...)` (`client/v3/client.go`, names only; pr-verify etcd#21714: what `clientv3.newClient` calls. Lean-first (no Rocq counterpart)).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvNewClient

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open go_etcd_io.etcd.cache.v3 (errorStringSpec)

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.dialWithBalancer()` (no extra dial options) of a client at its dial (`clientDialAt`: the fields it
and the connection's interceptors read are fixed) returns a connection, or an error whose `Error()`
returns some string (grpc's `NewClient`'s: it does not connect; a bad target or option). -/
abbrev Client.dialWithBalancer.spec : Prop :=
  ∀ (c : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientDialAt c }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"dialWithBalancer")) (Val #slice.nil))
  {{ (conn : Loc) (err : GoInterface), RET (PairV #conn #err); (⌜err = GoInterface.nil⌝ ∨ ∃ e : GoInterfaceOk, ⌜err = GoInterface.ok e⌝ ∗ errorStringSpec e) }}

end spec

end EtcdGrove
end Perennial
