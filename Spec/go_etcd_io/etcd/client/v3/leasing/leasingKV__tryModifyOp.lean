/-
`lkv.tryModifyOp(ctx, op)` (`client/v3/leasing/kv.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

/-- The guarded transaction of `tryModifyOp` and `revoke`: `op` if the lease key `pfx ++ key` was
created at or before `rev` (or is absent), else `els`. -/
def guardedTxn (pfx key : GoString) (rev : w64) (top : TxnOp) (els : List TxnOp) : TxnModel :=
  { cmps := [compareM (cmpKeyM .create (pfx ++ key)) .lt (.num (rev + W64 1))],
    thenOps := [top], elseOps := els }

/-- **`lkv.tryModifyOp(ctx, op)`** for a write `op` (`top`) of the key `o.key`: `Lock`s the key's
entry (its revision `rev`, a waiter channel `wc` if cached) and commits `op` guarded by the lease
key's create revision being at most `rev`. Returns `(nil, nil, err)` on an error (the key evicted)
or if the guard failed (`err` nil), or the committed transaction (`opCommitted`) and the waiter
channel to close (nil if the key was not cached: then the caller also runs `revoke`, which
commits `op` **again**, a finding). -/
abbrev leasingKV.tryModifyOp.spec : Prop :=
  ∀ (lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (opv : go_etcd_io.etcd.client.v3.Op) (o : OpFull)
    (top : TxnOp) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ isLeasingKV lkv γ pfx ∗ context.isContext ctx cs ∗ opFullAt opv o ∗ etcdReached lo ∗
      ⌜txnOpOf o = some top ∧ (o.t = W64 2 ∨ o.t = W64 3)⌝ }}
    (App (App (Val (lkv @!! go.GoType.PointerType leasingKV.ty @!! go!"tryModifyOp")) (Val #(GoInterface.ok ctx))) (Val #opv))
  {{ (resp : Loc) (wc : GoChan) (err : GoInterface), RET (PairV (PairV #resp #wc) #err);
      ⌜resp = null ∧ wc = null⌝ ∨
      (⌜err = GoInterface.nil⌝ ∗ opCommitted lo top resp ∗
        (⌜wc = null⌝ ∨ waitcClose wc)) }}

end spec

end leasing
end EtcdGrove
end Perennial
