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

/-- `op.toRequestOp()` of a get, a put or a delete: a new `*pb.RequestOp` wrapping the request of
its kind, holding (read-only) the operation's wire model (`leafWire`); a put that ignores the value
has none (2026-10-30: `reqOpAt`'s put case; Go copies the value into the request whatever
`ignoreValue`, and the wire model forgets it). -/
abbrev Op.toRequestOp.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗ opFullAt opv o ∗
      ⌜(o.t = W64 1 ∨ o.t = W64 2 ∨ o.t = W64 3) ∧ (o.t = W64 2 → o.ignoreValue = true → o.val = [])⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toRequestOp")) (Val #()))
  {{ (p : Loc), RET #p; reqOpAt p (leafWire o) }}

end spec

end EtcdGrove
end Perennial
