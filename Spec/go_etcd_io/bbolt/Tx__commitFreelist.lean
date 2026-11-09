/-
`tx.commitFreelist()` (`tx.go`): allocate pages for the freelist (4d's
`EstimatedWritePageSize`), write it (4d's `freelist.Write`), record it in the meta; on an allocation
error, `rollback`. (internal, mirrors the code; not called under `NoFreelistSync`, etcd's)

**Proof sketch.** 4d's `freelist.Write` into the allocated page (its count and ids within the
extent, the old `fileHolds`' synced-freelist clause); `tx.meta.SetFreelist`.
-/
module

public import Spec.go_etcd_io.bbolt.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- (internal) `tx.commitFreelist()`: the freelist page written, or an error and the transaction
rolled back. -/
def Tx.commitFreelist.spec : Prop :=
  ∀ [HasExt osFsExt] (tx : Loc) (γ : BoltName) (T : TxView),
  {{ wtxAt (GF := GF) tx γ T CommitStage.spilled }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"commitFreelist")) (Val #()))
  {{ (err : GoInterface), RET #err;
      (⌜err = GoInterface.nil⌝ ∗ wtxAt tx γ T CommitStage.spilled) ∨
      (⌜err ≠ GoInterface.nil⌝ ∗ txDone tx) }}

end spec

end Bbolt
end EtcdGrove
end Perennial
