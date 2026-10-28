/-
`clientv3.NewLeaseFromLeaseClient(remote, c, keepAliveTimeout)` (`client/v3/lease.go`; item 1, the
client lease). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.go_etcd_io.etcd.client.v3.InvLessor

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

/-- `NewLeaseFromLeaseClient(remote, c, d)` with a retry lease client over a connection to `addr`
and a non-nil client (its logger and call options, read-only): a new `*lessor` (`lessorAt`: its
channel, map, mutex and `Once`, `c.GetLogger()`, `c.callOpts`, and the stop context
`WithCancel(WithRequireLeader(context.Background()))`), as a `Lease`. -/
abbrev NewLeaseFromLeaseClient.spec : Prop :=
  ∀ (rlc conn c : Loc) (addr : List GoString) (d : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ retryLeaseAt rlc conn ∗
      isEtcdConn conn addr ∗ ⌜c ≠ null⌝ ∗ isClientLogger c ∗
      (∃ sl : GoSlice, clientF c go!"callOpts" ↦□ sl ∗ callOptsAt sl) }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.NewLeaseFromLeaseClient))
      (Val #(interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.retryLeaseClient.ty) #rlc :
        GoInterface))) (Val #c)) (Val #d))
  {{ (v : GoInterface), RET #v; ∃ l : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l⌝ ∗
      lessorAt l addr }}

end spec

end EtcdGrove
end Perennial
