/-
`clientv3.Op.toTxnRequest()` (`client/v3/op.go`, nested transactions, `notes/txn-nested.md`). Lean-first (no Rocq counterpart).
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

/-- `op.toTxnRequest()` of a nested transaction tree `.txn o cs ts es` (its plain operations gets,
puts and deletes): a new `*pb.TxnRequest` whose comparisons are clones of the `Op`'s (`cs`), and
whose `Success` and `Failure` hold the requests of `ts` and `es` (`Op.toRequestOp`'s), read-only:
the fields of `reqOpAt`'s nested case. -/
abbrev Op.toTxnRequest.spec : Prop :=
  ∀ (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull) (cs : List CmpModel) (ts es : List OpT),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 ∗
      opTAtC false opv (.txn o cs ts es) ∗
      ⌜∀ x ∈ (OpT.txn o cs ts es).leaves, (x.t = W64 1 ∨ x.t = W64 2 ∨ x.t = W64 3) ∧
        (x.t = W64 2 → x.ignoreValue = true → x.val = [])⌝ }}
    (App (Val (opv @!! go_etcd_io.etcd.client.v3.Op.ty @!! go!"toTxnRequest")) (Val #()))
  {{ (r : Loc), RET #r; ⌜r ≠ null⌝ ∗ txnReqFieldsAt r cs (OpT.wireL ts) (OpT.wireL es) }}

end spec

end EtcdGrove
end Perennial
