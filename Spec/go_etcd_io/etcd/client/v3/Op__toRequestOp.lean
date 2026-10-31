/-
`clientv3.Op.toRequestOp()` (`client/v3/op.go`, translated for the vertical slice's unit V2). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvKVConn

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.Assumptions]

/-- `op.toRequestOp()` of an operation tree `t` whose plain operations are gets, puts and deletes
(else it panics, `"Unknown Op"`): a new `*pb.RequestOp` wrapping the request of its kind, a nested
transaction's `toTxnRequest` (its comparisons cloned, its operations' requests, recursively),
holding (read-only) the tree's wire model (`OpT.wire`); a put that ignores the value has none
(`reqOpAt`'s put case; Go copies the value into the request whatever `ignoreValue`, and the wire
model forgets it). -/
abbrev Op.toRequestOp.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (t : OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opTAtC false opv t ∗
      ⌜∀ o ∈ t.leaves, (o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3) ∧
        (o.t = W64 2 → o.ignoreValue = true → o.val = [])⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRequestOp")) (Val #()))
  {{ (p : Loc), RET #p; reqOpAt p (OpT.wire t) }}

end spec

end EtcdGrove
end Perennial
