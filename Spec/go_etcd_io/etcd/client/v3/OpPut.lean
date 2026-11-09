/-
`clientv3.OpPut` (`client/v3/op.go`).

Users: `kv.Put`, `client/v3/concurrency` (`stm.go`, `mutex.go`, `election.go` with `WithLease`), recipes, Kubernetes' store and compactor (`Then(OpPut(...))`).

Proof sketch: `Op{t, key, val}`, `Op.applyOpts.spec`, the `switch` (premise `¬ putPanics`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/OpPut.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `OpPut(key, val, opts...)`: a put. -/
def OpPut.spec : Prop :=
  ∀ (key v : GoString) (sl : GoSlice) (gs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs ∗ ⌜¬ (opPutM key v gs).putPanics⌝ }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.OpPut)) (Val #key)) (Val #v)) (Val #sl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; optsAt sl gs ∗ opAt op (opPutM key v gs) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
