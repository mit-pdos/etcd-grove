/-
`check(addr, lg)` (`examples/etcd/leaseN/leaseN.go`; `notes/leaseN-plan.md`, 2026-11-16): the lease
example's two reads through a new client of the member at `addr`. Lean-first (no Rocq counterpart).

**The triple:** with etcd's lease reads registered at `addr` (`client.etcdLeaseReadAt`: `TimeToLive` and
`Leases` at etcd's specs, which every served member registers, `etcdstart.kv_lease_served`), a plain
endpoint, `check` returns (`V`: the client's watch environment `NewClient`'s spec takes, which `check`
does not use): it does not panic, so a listing that answered listed no lease twice and a
`TimeToLive(7)` that answered was about lease `7`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Base
public import Proof.go_etcd_io.etcd.client.v3.TimeoutCtx
public import Proof.go_etcd_io.etcd.client.v3.PerTypeLease
public import Proof.go_etcd_io.etcd.client.v3.PerTypeKVRest
public import Proof.go_etcd_io.etcd.client.v3.ServerWatcher
public import Proof.go_etcd_io.etcd.client.v3.LeaseClient
public import Proof.go_etcd_io.etcd.client.v3.PerTypeAuth
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.PerTypeWatch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerRFacts
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.NewServerR
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Append
public import Spec.go_etcd_io.raft.v3.MemoryStorage__SetHardState
public import Spec.go_etcd_io.raft.v3.MemoryStorage__ApplySnapshot
public import Spec.go_etcd_io.raft.v3.MemoryStorage__Compact
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Lemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NetErr
public import Spec.sort.SortAnyLess
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadServer
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ReadRaft
public import Proof.go_etcd_io.etcd.pkg.v3.wait.TimeListIfc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.LessorOk
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.apply.LessorDerive
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAllocOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.AdminEntryOn
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.ApplyAllSnapLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.RunAdapt
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchStep
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.WatchClass
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.AuthService
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLemmas
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRead
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.ServerLeaseRevoke
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.QuotaLeaseLemmas
public import Proof.go_etcd_io.etcd.client.v3.KVServiceOn
public import Proof.go_etcd_io.etcd.client.v3.KeyOps
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseTimeToLive_Handler
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb._Lease_LeaseLeases_Handler
public import Proof.go_etcd_io.etcd.client.v3.InvLeaseRead
public import Proof.go_etcd_io.etcd.client.v3.InvClientNew
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_leaseN

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.Assumptions]

/-- See the file header. -/
abbrev check.spec : Prop :=
  ∀
    (addr : GoString) (lg : Loc) (V : client.WEnv GF),
  plainEndpoint addr → threadBound GF ≤ 2 ^ 31 →
  errors.AsTarget go_etcd_io.etcd.api.v3.v3rpc.rpctypes.EtcdError.ty →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN ∗
      zapLoggerOk lg ∗ client.etcdLeaseReadAt addr }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.leaseN.check)) (Val #addr))
      (Val #lg))
  {{ (b : Bool), RET #b; True }}

end spec

end etcd_leaseN
end EtcdGrove
end Perennial
