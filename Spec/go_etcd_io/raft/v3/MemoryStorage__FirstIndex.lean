/-
## `MemoryStorage.FirstIndex()`

**Users.** raft (through `isStorage`); the examples (`kvdurable/kv.go:607`, `FirstIndex` before a
compaction). **Proof sketch.** Under the lock, `firstIndex`. **Changes.** Atomic.
-/
module

public import Spec.go_etcd_io.raft.v3.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Raft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]
variable [ctx_sem : context.Assumptions]

/-- `σ.first`, atomically. -/
def MemoryStorage.FirstIndex.spec : Prop :=

  ∀ (ms : Loc) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ (AU <{ ∃∃ (σ : StorState), memStor ms σ }> @ ⊤, ∅
        <{ memStor ms σ, COMM Q σ }>) }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"FirstIndex")) (Val #()))
  {{ (x : w64) (err : GoInterface), RET (PairV #x #err); ⌜err = interface.nil⌝ ∗
      ∃ σ, Q σ ∗ ⌜x = W64 σ.first⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
