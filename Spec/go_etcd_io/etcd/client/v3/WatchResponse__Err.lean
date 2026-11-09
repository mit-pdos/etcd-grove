/-
`(*clientv3.WatchResponse).Err()` (`client/v3/watch.go`).

**Users**: every watch user (`ending.go`); also on responses a caller builds (the cache's own
`WatchResponse`s: `closeErrOk_nil`). **Proof sketch**: the `switch`: `closeErr` (`closeErrOk`:
`rpctypes.Error` of it, 2a's spec, gives a non-nil error of its kind), `CompactRevision`
(`rpctypes.ErrCompacted`: `errVal .compacted`, 2a's variable law), `Canceled` with a reason
(`status.Error(FailedPrecondition, ...)` then `rpctypes.Error`: some error) or without
(`errVal .futureRev`). **Changes** from `specs-ref/.../WatchResponse__Err.lean`: over the struct
with `closeErrOk` (was `statusErrOk`). **Margin**: the canceled-with-reason error's kind is not
given (no consumer response has it: `watchStep`).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.ApiWatch

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ClientV3

open Iris Iris.BI EtcdModel EtcdWire
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `wr.Err()`: the response's error as its fields say. -/
def WatchResponse.Err.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (v : go_etcd_io.etcd.client.v3.WatchResponse) (k : Option CallErr),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ p ↦{dq} v ∗
      closeErrOk v.closeErr' k }}
    (App (Val (p @!! go.GoType.PointerType go_etcd_io.etcd.client.v3.WatchResponse.ty @!! go!"Err"))
      (Val #()))
  {{ (err : GoInterface), RET #err; p ↦{dq} v ∗
      (match k with
       | some ck => iprop(⌜err ≠ GoInterface.nil⌝ ∗ callErr err ck)
       | none =>
         if v.CompactRevision' ≠ W64 0 then iprop(⌜err = errVal .compacted⌝)
         else if v.Canceled' = true then
           (if v.CancelReason' = [] then iprop(⌜err = errVal .futureRev⌝)
            else iprop(⌜err ≠ GoInterface.nil⌝ ∗ ∃ ck, callErr err ck))
         else iprop(⌜err = GoInterface.nil⌝)) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
