/-
`(*leasingKV).Compact` (`client/v3/leasing/kv.go`).

Users: the gRPC proxy (`server/proxy/grpcproxy/kv.go:144`). Snippet: `leasing/writes.go`
(`ReqCompactThroughLeasing`).

Proof sketch: loads `lkv.kv` (`isLeasingKV`: a `kvAt` value of the cluster `γ` as `who`) and calls
its `Compact` (`kvAt_methods`: `KV.CompactTriple`) with the same arguments and update.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__Compact.lean`: W0's
contract (was the old client's compaction contract over a reached revision).

Margin: none beyond W0's.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Leasing

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- `lkv.Compact` meets **W0's** KV contract's `Compact` (`KV.CompactTriple`). -/
def leasingKV.Compact.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  KV.CompactTriple (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"Compact")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL)) γ who

end spec

end Leasing
end EtcdGrove
end Perennial
