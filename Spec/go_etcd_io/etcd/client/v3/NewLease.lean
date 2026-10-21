/-
`clientv3.NewLease(c)` (`client/v3/lease.go`; item 5: `newClient` calls it; with its body since
item 1, the client lease). Lean-first (no Rocq counterpart).
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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `NewLease(c)` of a client `New` builds (its connection to the server at `addr`, call options,
configuration and logger, read-only: `clientCoreAt`, `clientKVAt`):
`NewLeaseFromLeaseClient(RetryLeaseClient(c), c, c.cfg.DialTimeout + time.Second)`, a `*lessor`
over the connection (`lessorAt`), as a `Lease`. -/
abbrev NewLease.spec : Prop :=
  ∀ (c : Loc) (addr : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ clientCoreAt c ∗
      clientKVAt c addr }}
    (App (Val (@! go_etcd_io.etcd.client.v3.NewLease)) (Val #c))
  {{ (v : GoInterface), RET #v; ∃ l : Loc,
      ⌜v = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.client.v3.lessor.ty) #l⌝ ∗
      lessorAt l addr }}

end spec

end EtcdGrove
end Perennial
