/-
`clientv3.OpDelete` (`client/v3/op.go`).

Users: `kv.Delete`, `client/v3/concurrency` (`election.go:124`, `stm.go`), recipes (`client.go`), leasing.

Proof sketch: `IsOptsWithPrefix.spec`, `IsOptsWithFromKey.spec` (the options run on a `NewOp()`, given back), `Op{t, key}` then `Op.applyOpts.spec`, the `switch` (premise).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/OpDelete.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `OpDelete(key, opts...)`: a delete over `key` with the options applied. -/
def OpDelete.spec : Prop :=
  ∀ (key : GoString) (sl : GoSlice) (gs : List (OpM → OpM)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ optsAt sl gs ∗ ⌜¬ prefixAndFromKey gs ∧ ¬ (opDeleteM key gs).deletePanics⌝ }}
    (App (App (Val (@! go_etcd_io.etcd.client.v3.OpDelete)) (Val #key)) (Val #sl))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; optsAt sl gs ∗ opAt op (opDeleteM key gs) }}

end spec

end ClientV3
end EtcdGrove
end Perennial
