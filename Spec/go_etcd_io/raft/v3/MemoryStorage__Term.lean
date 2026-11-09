/-
## `MemoryStorage.Term(i)`

**Users.** raft (through `isStorage`). **Proof sketch.** Under the lock. **Changes.** Atomic.
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

/-- The stored term at `i`, atomically; or `ErrCompacted` / `ErrUnavailable`. -/
def MemoryStorage.Term.spec : Prop :=

  ∀ (ms : Loc) (i : w64) (Q : StorState → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ (AU <{ ∃∃ (σ : StorState), memStor ms σ ∗ ⌜uint.nat i < σ.off + 2 ^ 63⌝ }> @ ⊤, ∅
        <{ memStor ms σ, COMM Q σ }>) }}
    (App (Val (ms @!! go.GoType.PointerType go_etcd_io.raft.v3.MemoryStorage.ty @!! go!"Term")) (Val #i))
  {{ (t : w64) (err : GoInterface), RET (PairV #t #err); ∃ σ, Q σ ∗
      ((⌜err = interface.nil ∧ σ.termAt (uint.nat i) = some t⌝) ∨
       (⌜uint.nat i < σ.off⌝ ∗ errIs go_etcd_io.raft.v3.ErrCompacted err) ∨
       (⌜σ.last < uint.nat i⌝ ∗ errIs go_etcd_io.raft.v3.ErrUnavailable err)) }}

end spec
end Raft
end EtcdGrove
end Perennial
