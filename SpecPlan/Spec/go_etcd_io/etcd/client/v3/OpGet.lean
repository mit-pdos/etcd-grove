/-
`clientv3.OpGet` (`client/v3/op.go`).

Users: `kv.Get`, `client/v3/concurrency` (`stm.go:262`, `mutex.go:83`, `election.go:69` `Else(OpGet(...))`), leasing, the cache, Kubernetes' store (`Else(OpGet(key))`).

Proof sketch: `IsOptsWithPrefix.spec`, `IsOptsWithFromKey.spec` (the options run on a `NewOp()`, given back), `Op{t, key}` then `Op.applyOpts.spec`.

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/OpGet.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

Margin: none.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.client.v3.Api

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

/-- `OpGet(key, opts...)`: a range over `key` with the options applied. -/
def OpGet.spec : Prop :=
  ∀ (key : GoString) (sl : GoSlice) (gs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs ∗ ⌜¬ prefixAndFromKey gs⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.OpGet)) (Val #key)) (Val #sl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; optsAt sl gs ∗ opAt op (opGetM key gs) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
