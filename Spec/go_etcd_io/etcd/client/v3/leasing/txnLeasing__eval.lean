/-
`txn.eval()` (`client/v3/leasing/txn.go`). Lean-first (no Rocq counterpart); see `InvLeasingKV.lean`.
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

/-- **`txn.eval()`**: waits for the cached gets' waiter channels (or the context: `(nil, err)`),
then under the read lock evaluates the comparisons (`leaseCache.evalCmp`) and the chosen branch
(`evalOps`) in the cache: `(nil, nil)` if it cannot (a comparison of a key not cached or of a
range, no header yet, an operation that is not a cached get), else the cache's answer
(`evalResult`). -/
abbrev txnLeasing.eval.spec : Prop :=
  ∀ (txn lkv : Loc) (γ : LeasingNames) (pfx : GoString) (ctx : GoInterfaceOk)
    (cs : context.ContextDesc (IProp GF)) (b : LTxnBuild),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.leasing ∗ ownTxnLeasing txn lkv γ pfx ctx cs b ∗ lkvReader lkv γ pfx ∗
      ⌜(b.thenOs.length : Int) + b.elseOs.length < 2 ^ 63⌝ }}
    (App (Val (txn @!! go.GoType.PointerType txnLeasing.ty @!! go!"eval")) (Val #()))
  {{ (resp : Loc) (err : GoInterface), RET (PairV #resp #err); ownTxnLeasing txn lkv γ pfx ctx cs b ∗ lkvReader lkv γ pfx ∗
      (⌜resp = null⌝ ∨ (⌜resp ≠ null ∧ err = GoInterface.nil⌝ ∗ evalResult γ b resp)) }}

end spec

end leasing
end EtcdGrove
end Perennial
