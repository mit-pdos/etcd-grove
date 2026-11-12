/-
## `(*raftLog).zeroTermOnOutOfBounds(t, err)` (internal)

**Users**: `findConflict`'s log line, `handleAppendEntries`' log line, `committedEntryInCurrentTerm`.
**Proof sketch**: comparisons with the error variables (`errs_init`: distinct, non-nil).
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__zeroTermOnOutOfBounds.lean`.
-/
module

public import SpecPlan.Spec.go_etcd_io.raft.v3.ApiLog

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

/-- (internal) `t` on success, 0 on `ErrCompacted`/`ErrUnavailable`. -/
def raftLog.zeroTermOnOutOfBounds.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (t : w64) (err : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗
      (⌜err = interface.nil⌝ ∨ errIs go_etcd_io.raft.v3.ErrCompacted err ∨ errIs go_etcd_io.raft.v3.ErrUnavailable err) }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"zeroTermOnOutOfBounds")) (Val #t)) (Val #err))
  {{ (r : w64), RET #r; raftLog l ls ∗
      ⌜(err = interface.nil ∧ r = t) ∨ (err ≠ interface.nil ∧ r = W64 0)⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
