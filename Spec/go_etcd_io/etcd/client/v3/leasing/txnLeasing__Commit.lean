/-
`txn.Commit()` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeasingPrefix

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

/-- **`txn.Commit()`**: the cache's evaluation (`eval`) if it answers, else `serverTxn`:
`commitOutcome`. The context must be cancelable.

etcd#22118: if an operation of either branch is a delete intersecting the lease prefix `pfx`, the
commit fails before anything else; one that succeeds had no delete with a lease key in its range
(`LeaseDeleteGuard`). The spec before the PR is `txnLeasing.Commit.spec_old`, which this one
implies (`txnLeasing.Commit.spec_implies_old`). -/
abbrev txnLeasing.Commit.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ownTxnLeasing txn lkv γ pfx ctx cs b ∗ lkvReader lkv γ pfx ∗ context.isCancelCtxCtx ctx cs ∗ etcdReached lo ∗
      ⌜(b.thenOs.length : Int) + b.elseOs.length < 2 ^ 63⌝ }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"Commit")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); lkvReader lkv γ pfx ∗
      ⌜LeaseDeleteGuard pfx (b.thenOs ++ b.elseOs) err⌝ ∗
      commitOutcome γ lo b resp err }}


/-- **`txn.Commit()`, the spec before etcd#22118**: the cache's evaluation (`eval`) if it answers, else `serverTxn`:
`commitOutcome`. The context must be cancelable. -/
abbrev txnLeasing.Commit.spec_old : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild) (lo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ownTxnLeasing txn lkv γ pfx ctx cs b ∗ lkvReader lkv γ pfx ∗ context.isCancelCtxCtx ctx cs ∗ etcdReached lo ∗
      ⌜(b.thenOs.length : Int) + b.elseOs.length < 2 ^ 63⌝ }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"Commit")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); lkvReader lkv γ pfx ∗
      commitOutcome γ lo b resp err }}

end spec

end leasing
end EtcdGrove
end Perennial
