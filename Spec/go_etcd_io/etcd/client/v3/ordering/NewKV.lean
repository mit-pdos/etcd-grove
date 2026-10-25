/-
`ordering.NewKV(kv, orderViolationFunc)` (`client/v3/ordering/kv.go`). Lean-first (no Rocq counterpart); see `InvOrdering.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.ordering.InvOrdering

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace ordering

open Iris Iris.BI go_etcd_io.etcd.client.v3.ordering

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.ordering.Assumptions]

/-- `ordering.NewKV(kv, orderViolationFunc)`: allocates a `*kvOrdering` wrapping `kv` and `vf`
with initial `prevRev = 0`, returning it as a `clientv3.KV` interface along with `isKvOrdering`
and the `RWMutex`'s tokens (`kvOrderingHandle`). -/
abbrev NewKV.spec : Prop :=
  ∀ (kv : go_etcd_io.etcd.client.v3.KV) (vf : OrderViolationFunc) (R : w64 → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.ordering ∗ □ R (W64 0) }}
    (App (App (Val (@! NewKV)) (Val #kv)) (Val #vf))
  {{ (kvp : Loc), RET #(interface.mkOk (go.GoType.PointerType kvOrdering.ty) #kvp);
      isKvOrdering kvp kv vf ∗
      [∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
        kvOrderingHandle kvp R }}

end spec

end ordering
end EtcdGrove
end Perennial
