/-
`clientv3.RetryLeaseClient(c)` (`client/v3/retry.go`; item 1, the client lease). Lean-first (no
Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

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

/-- `RetryLeaseClient(c)` on a `*Client` whose connection is `conn` (read-only): a new
`*retryLeaseClient` over a stub on `conn` (`retryLeaseAt`), as a `LeaseClient`. -/
abbrev RetryLeaseClient.spec : Prop :=
  ∀ (cl conn : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      structFieldRef go_etcd_io.etcd.client.v3.Client go!"conn" cl ↦□ conn }}
    (App (Val (@! go_etcd_io.etcd.client.v3.RetryLeaseClient)) (Val #cl))
  {{ (v : GoInterface), RET #v; ∃ rlc : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty)
        #rlc⌝ ∗
      retryLeaseAt rlc conn }}

end spec

end EtcdGrove
end Perennial
