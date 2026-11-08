/-
**The lessor's range deleter is the store's `Write`** (2026-11-06). Lean-first (no Rocq counterpart).

`NewStore` and `newWatchableStore` give the lessor the closure
`func() lease.TxnDelete { return s.Write(traceutil.TODO()) }` (`SetRangeDeleter`), `s` the store
(`*store`) or the watchable store (`*watchableStore`). `rdCalls rd ty v` says so generically: `rd`
is not `nil`, and whatever the handle's `Write` (`methods ty "Write" v`) does at a fresh trace,
`rd()` does (the conversion of its `TxnWrite` result to a `TxnDelete` is the identity on interface
values). The API's `mvccDeleter` follows from it and `KV.Write.contract` at the handle's type
(`Api/NewStoreApi.lean`, `Api/NewApi.lean`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvStore
public import Spec.go_etcd_io.etcd.pkg.v3.traceutil.TODO

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

/-- **`rd()` is `v.Write(traceutil.TODO())`** at the handle's type `ty` (persistent): not `nil`, and,
given `TODO`'s spec, every triple of `Write` at a fresh trace (not `nil`, owned and empty) is one of
`rd()`. -/
def mvcc.rdCalls (rd : GoFunc) (ty : go.GoType) (v : val) : IProp GF :=
  iprop(⌜rd ≠ func.nil⌝ ∗ □ ∀ (Pre : IProp GF) (Ψ : GoInterface → IProp GF),
    ⌜traceutil.TODO.spec (GF := GF) (hG := hG)⌝ -∗
    □ (∀ tr : Loc, {{ Pre ∗ ⌜tr ≠ null⌝ ∗ traceutil.ownTrace tr true }}
        (App (Val #(methods ty go!"Write" v)) (Val #tr)) {{ (t : GoInterface), RET #t; Ψ t }}) -∗
    {{ Pre }} (App (Val #rd) (Val #())) {{ (t : GoInterface), RET #t; Ψ t }})

instance mvcc.rdCalls_persistent (rd : GoFunc) (ty : go.GoType) (v : val) :
    Persistent (mvcc.rdCalls (GF := GF) rd ty v) := by
  unfold mvcc.rdCalls; infer_instance

end defs

end EtcdGrove
end Perennial
