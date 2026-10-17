/-
`endpoint.RequiresCredentials(ep)` (`client/v3/internal/endpoint`, names only; item 5). Lean-first
(no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- `endpoint.RequiresCredentials(ep)`: one of the three requirements, `CredsOptional` for a
plain endpoint. -/
abbrev endpoint.RequiresCredentials.spec : Prop :=
  ∀ (ep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.internal.endpoint }}
    (App (Val (@! go_etcd_io.etcd.client.v3.internal.endpoint.RequiresCredentials)) (Val #ep))
  {{ (r : w64), RET #r; ⌜r = W64 0 ∨ r = W64 1 ∨ r = W64 2⌝ ∗
      ⌜plainEndpoint ep → r = W64 2⌝ }}

end spec

end EtcdGrove
end Perennial
