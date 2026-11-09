/-
`(*leasingKV).GetStream` (`client/v3/leasing/kv.go`).

Users: none (the proxy's `RangeStream` is not served through it; Kubernetes uses the plain client).
Snippet: `leasing/reads.go` (`ReqGetStreamUnsupported`).

Proof sketch: `status.Error(codes.Unimplemented, msg)` (grpc's boundary, 2a: a non-nil error of
kind `.other`, `callErr`: `req/google_golang_org_grpc.md`, from 1e); returns `(nil, err)`: the
second disjunct, `indefCall err` with the thread token given back.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/leasing/leasingKV__GetStream.lean`: W0's
contract (was an unconditional error post).

Margin: the code always errs; the contract allows a stream.
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

/-- `lkv.GetStream` meets **W0's** KV contract's `GetStream` (`KV.GetStreamTriple`): it always fails with an error that settles nothing. -/
def leasingKV.GetStream.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  KV.GetStreamTriple (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"GetStream")
    (iprop(isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL)) γ who

end spec

end Leasing
end EtcdGrove
end Perennial
