/-
`c.credentialsForEndpoint(ep)` (`client/v3/client.go`; item 5). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `c.credentialsForEndpoint(ep)` of a plain endpoint: the client's credentials (`c.creds`,
read-only). -/
abbrev Client.credentialsForEndpoint.spec : Prop :=
  ∀ (c : Loc) (ep : GoString) (cr : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientF c go!"creds" ↦□ cr ∗
      ⌜plainEndpoint ep⌝ }}
    (App (Val (c @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty @!! go!"credentialsForEndpoint")) (Val #ep))
  {{ RET #cr; True }}

end spec

end EtcdGrove
end Perennial
