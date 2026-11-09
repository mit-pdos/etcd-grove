/-
`clientv3.OpTxn` (`client/v3/op.go`).

Users: leasing (`leasing/txn.go`: nested transactions), `examples/etcd/auth/authkv.go`.

Proof sketch: the comparisons cloned into a fresh slice (`Cmp.Clone.spec`), the branches' slices kept (read-only, `opsAt`).

Changes: from `specs-ref/Spec/go_etcd_io/etcd/client/v3/OpTxn.lean`: restated over this branch's vocabulary (the `OpM` model, `opAt`, `optsAt`); otherwise unchanged.

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

/-- `OpTxn(cmps, thenOps, elseOps)`: a transaction `Op`. -/
def OpTxn.spec : Prop :=
  ∀ (cs ts es : GoSlice) (ms : List (Option EtcdModel.Compare)) (os os' : List OpM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ cmpsAt cs ms ∗ opsAt ts os ∗ opsAt es os' }}
    (App (App (App (Val (@! go_etcd_io.etcd.client.v3.OpTxn)) (Val #cs)) (Val #ts)) (Val #es))
  {{ (op : go_etcd_io.etcd.client.v3.Op), RET #op; opAt op (opTxnM ms os os') }}

end spec

end ClientV3
end EtcdGrove
end Perennial
