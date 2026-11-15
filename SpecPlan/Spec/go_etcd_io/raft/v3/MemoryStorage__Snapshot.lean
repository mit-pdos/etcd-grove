/-
## `MemoryStorage.Snapshot()`

**Users.** raft (through `isStorage`: a leader's `maybeSendSnapshot`); etcd's `EtcdServer.getSnapshot`
(`server.go:755`, at a restart's snapshot purge) and the examples' `snapIndex`. **Proof sketch.**
Under the lock, a clone. **Changes.** Atomic.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.Api

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

/-- A copy of the stored snapshot, atomically. -/
def MemoryStorage.Snapshot.spec : Prop :=

  ∀ (ms : Loc) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ (AU <{ ∃∃ (σ : StorState), memStor ms σ }> @ ⊤, ∅
        <{ memStor ms σ, COMM Q σ }>) }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Snapshot")) (Val #()))
  {{ (sp : Loc) (err : GoInterface), RET (PairV #sp #err); ⌜err = interface.nil⌝ ∗
      ∃ σ, Q σ ∗ snapshotPts sp (DFrac.own 1) σ.snap }}

end spec
end Raft
end EtcdGrove
end Perennial
