/-
## `MemoryStorage.Entries(lo, hi, maxSize)`

**Users.** raft (through `isStorage`). **Proof sketch.** Under the lock; `limitSize` (at least one
entry); the full slice expression. Past the last index Go panics (excluded). **Changes.** Atomic.
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

/-- The stored entries `[lo, hi)`, a non-empty prefix of them, atomically; or `ErrCompacted` /
`ErrUnavailable`. -/
def MemoryStorage.Entries.spec : Prop :=

  ∀ (ms : Loc) (lo hi mx : w64) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ (AU <{ ∃∃ (σ : StorState), memStor ms σ ∗ ⌜uint.nat lo < uint.nat hi ∧ uint.nat hi ≤ σ.last + 1⌝ }> @ ⊤, ∅
        <{ memStor ms σ, COMM Q σ }>) }}
    (App (App (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Entries")) (Val #lo)) (Val #hi)) (Val #mx))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); ∃ σ, Q σ ∗
      ((⌜uint.nat lo ≤ σ.off⌝ ∗ errIs go_etcd_io.raft.v3.ErrCompacted err) ∨
       (⌜σ.ents = []⌝ ∗ errIs go_etcd_io.raft.v3.ErrUnavailable err) ∨
       (⌜err = interface.nil⌝ ∗ ∃ es, entriesRO sl (uint.nat lo) es ∗
          ⌜es ≠ [] ∧ es <+: (σ.ents.drop (uint.nat lo - σ.off - 1)).take
            (uint.nat hi - uint.nat lo)⌝)) }}

end spec
end Raft
end EtcdGrove
end Perennial
