/-
`lkv.Do(ctx, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingKV

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- What `Do` needs of a nested transaction `op` (`OpTxn(cmps, thenOps, elseOps)`): comparisons
with their operands set, plain operations a transaction can run (fewer than `2^63` in all, for
`Commit`'s `make`). -/
def doTxnPre (opv : go_etcd_io.etcd.client.v3.Op) : IProp GF :=
  iprop(∃ (ms : List CmpModel) (tos eos : List OpFull) (tops eops : List TxnOp),
    cmpsSetAt opv.cmps' ms ∗ opsAt opv.thenOps' tos ∗ opsAt opv.elseOps' eos ∗
    ⌜tos.map txnOpOf = tops.map some ∧ eos.map txnOpOf = eops.map some ∧
      (tos.length : Int) + eos.length < 2 ^ 63⌝)

/-- **`lkv.Do(ctx, op)`**, by the kind of `op` (`o.t`): a get answers as `get` (in the
`OpResponse`'s `get`), a put as `put`, a delete as `delete`, a transaction as `Txn(ctx).If(...)
.Then(...).Else(...).Commit()` (`commitOutcome`); anything else, an empty `OpResponse` and `nil`.
The monitor slot is kept unless a get started a lease monitor; the context must be cancelable. -/
abbrev leasingKV.Do.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (lo : w64) (q : Qp),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ lkvReader lkv γ pfx ∗ lkvReader lkv γ pfx ∗ context.isContext ctx cs ∗ context.isCancelCtxCtx ctx cs ∗
      opFullAt opv o ∗ etcdReached lo ∗ leasingOpen γ q ∗ threadTok ∗
      ⌜o.t = W64 2 → txnOpOf o ≠ none⌝ ∗ (⌜o.t = W64 4⌝ -∗ doTxnPre opv) }}
    (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"Do")) (Val #(GoInterface.ok ctx))) (Val #opv))
  {{ (r : go_etcd_io.etcd.client.v3.OpResponse) (err : GoInterface), RET (PairV #r #err);
      lkvReader lkv γ pfx ∗ leasingOpen γ q ∗ threadTok ∗
      (if o.t = W64 1 then getOutcome γ pfx lo o r.get' err (lkvReader lkv γ pfx)
       else lkvReader lkv γ pfx ∗
        (if o.t = W64 2 then
          (⌜err ≠ GoInterface.nil ∧ r.put' = null⌝ ∨
           (⌜err = GoInterface.nil⌝ ∗ ∃ top, ⌜txnOpOf o = some top⌝ ∗ putCommitted γ lo o top r.put'))
        else if o.t = W64 3 then
          (⌜err ≠ GoInterface.nil ∧ r.del' = null⌝ ∨
           (⌜err = GoInterface.nil⌝ ∗ deleteCommitted lo o r.del'))
        else if o.t = W64 4 then
          ∃ (ms : List CmpModel) (tos eos : List OpFull),
            cmpsSetAt opv.cmps' ms ∗ opsAt opv.thenOps' tos ∗ opsAt opv.elseOps' eos ∗
            commitOutcome γ lo (LTxnBuild.mk ms tos eos true true true) r.txn' err
        else ⌜r = zero_val go_etcd_io.etcd.client.v3.OpResponse ∧ err = GoInterface.nil⌝)) }}

end spec

end leasing
end EtcdGrove
end Perennial
