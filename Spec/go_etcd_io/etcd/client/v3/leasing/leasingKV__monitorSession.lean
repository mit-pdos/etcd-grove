/-
`(*leasingKV).monitorSession` (`kv.go`): the goroutine `NewKV` starts; while `lkv.ctx` is live, it
makes a session (`concurrency.NewSession`, 1d) whenever the last one is done, resetting the cache.
Proof sketch: loop invariant `sessMonitor`; under the cache's write lock it resets `entries` (a new
map) and replaces `sessionc`; `NewSession(cl, opts...)` (1d's spec, with `sessOptsOk` and the grants
and keep-alives fired from `protoUpd`, which `ProtoStep` permits); then sets `session`, closes
`sessionc` (announcing `sessionReady`). Changes: from `specs-ref`'s `leasingKV__monitorSession.lean`: restated over `isLeasingKV`/`Internal.lean` (was the cache's log states and the history premise); weakened to what the leasing contract's proofs need.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.Internal

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

/-- `monitorSession()`: runs until the KV's context is done. -/
def leasingKV.monitorSession.spec : Prop :=
  ∀ (lkv : Loc) (γ : Cluster) (who : Principal) (pfx : Key) (γL : LeasingNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ who pfx γL ∗ sessMonitor lkv γL }}
    (App (Val (lkv @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.leasing.leasingKV.ty @!! go!"monitorSession")) (Val #()))
  {{ RET #(); True }}

end spec

end Leasing
end EtcdGrove
end Perennial
