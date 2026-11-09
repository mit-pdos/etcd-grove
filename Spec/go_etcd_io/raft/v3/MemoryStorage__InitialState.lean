/-
## `MemoryStorage.InitialState()`

**Users.** raft's `newRaft` (through `isStorage`, at a start). **Proof sketch.** Reads `hardState`
and the snapshot's `ConfState` **without the lock** (`issues/raft-memorystorage-initialstate-
unlocked.md`): so it needs the contents exclusively, not an update a concurrent writer could fire.
**Changes.** Restated over `memStor` (was the detached `memStorFresh`'s). **Margin.** The returned
pointers alias the storage's (read-only).
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

/-- The stored hard state (`nil` for the empty one) and the snapshot's configuration, on a storage
no one else touches. -/
def MemoryStorage.InitialState.spec : Prop :=

  ∀ (ms : Loc) (σ : StorState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ memStor ms σ }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"InitialState")) (Val #()))
  {{ (hp csp : Loc) (err : GoInterface), RET (PairV (PairV #hp #csp) #err);
      ⌜err = interface.nil⌝ ∗ memStor ms σ ∗ hsPtr hp σ.hs ∗
      confStatePts csp DFrac.discard σ.snap.conf }}

end spec
end Raft
end EtcdGrove
end Perennial
