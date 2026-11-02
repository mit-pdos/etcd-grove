/-
The range deleter's code (mvcc's candidate API, `notes/mvcc-api-proof-plan.md`): what
`newWatchableStore` states of the deleter it sets on the lessor in the abstract mode, where the
deleter's contract (`mvccDeleter`) is over the store's pools, made after it returns.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvWatchSync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- **The range deleter `rd` is `ws.Write(traceutil.TODO())`** (persistent): not `nil`, and with
any spec of the watchable store's `Write` at a fresh trace, a call of it has that spec (its result,
a watchable write transaction, as the lessor's `TxnDelete`). -/
def mvcc.rdCode (rd : GoFunc) (ws : Loc) : IProp GF :=
  iprop(⌜rd ≠ func.nil⌝ ∗ □ (∀ (Pre : IProp GF) (Post : Loc → Loc → IProp GF),
    (∀ tr : Loc, {{ Pre ∗ ⌜tr ≠ null⌝ ∗ traceutil.ownTrace tr true }}
        (App (Val (ws @!! go.GoType.PointerType watchableStore.ty @!! go!"Write")) (Val #tr))
      {{ (tw : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw);
          Post tr tw }}) -∗
    {{ Pre }} (App (Val #rd) (Val #()))
      {{ (tw : Loc), RET #(interface.mkOk (go.GoType.PointerType watchableStoreTxnWrite.ty) #tw);
          ∃ tr : Loc, Post tr tw }}))

instance mvcc.rdCode_persistent (rd : GoFunc) (ws : Loc) : Persistent (mvcc.rdCode (GF := GF) rd ws) := by
  unfold mvcc.rdCode; infer_instance

end defs

end EtcdGrove
end Perennial
