/-
`(*store).checkPrevCompactionCompleted()` (`kvstore.go:225`). Internal: `Compact` and
`compactLockfree` (under `s.mu`); its result only decides whether the job stores its hash.

**Proof sketch**: `s.b.ReadTx()`, `RLock` (a storage reader slot: the compactor's, in the open
token), the two `UnsafeRead*Compact`s (the image's compaction keys parse: the store's invariant),
`RUnlock`.

**Changes** from `specs-ref`'s file: over `storeWB` and the storage's reader slots.
-/
module

public import SpecPlan.Spec.go_etcd_io.etcd.server.v3.storage.mvcc.InternalStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Mvcc

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `s.checkPrevCompactionCompleted()` (`s.mu` held, a reader slot): some boolean. -/
def store.checkPrevCompactionCompleted.spec : Prop :=
  ∀ (s : Loc) (γ : MvccName) (B : MvccStorage) (Pk : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ isStore s γ ∗
      storeWB s γ B Pk ∗ kbRdToks B 1 ∗ schemaVars }}
    (App (Val (s @!! go.GoType.PointerType store.ty @!! go!"checkPrevCompactionCompleted")) (Val #()))
  {{ (b : Bool), RET #b; storeWB s γ B Pk ∗ kbRdToks B 1 }}

end spec
end Mvcc
end EtcdGrove
end Perennial
