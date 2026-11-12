/-
`authority(endpoint)` (`client/v3/client.go`; item 5: the authority of `dial`'s target). Lean-first
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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `authority(ep)` of a plain endpoint: some string (it does not panic). (Plain: Perennial's
model has no substring of a `string` (`Slice go.string`), which the `unix:`/`unixs:` branches
take.) -/
abbrev authority.spec : Prop :=
  ∀ (ep : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ ⌜plainEndpoint ep⌝ }}
    (App (Val (@! go_etcd_io.etcd.client.v3.authority)) (Val #ep))
  {{ (s : GoString), RET #s; True }}

end spec

end EtcdGrove
end Perennial
