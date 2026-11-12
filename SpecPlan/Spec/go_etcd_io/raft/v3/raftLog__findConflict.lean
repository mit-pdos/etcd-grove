/-
## `(*raftLog).findConflict(ents)` (internal)

**Users**: `maybeAppend`. **Proof sketch**: a loop over the entries with `matchTerm` (exact above
`compactFloor`), `Infof` with `zeroTermOnOutOfBounds(term(i))` on a conflict inside the log.
**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__findConflict.lean`: over `LogState.conflict`.
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

/-- (internal) The index of the first entry of `es` (at `k, k+1, ...`) the log does not have, or 0. -/
def raftLog.findConflict.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (sl : GoSlice) (k : Nat) (es : List LogEntry),
  ls.compactFloor < k → k + es.length < 2 ^ 64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗ entriesRO sl k es }}
    (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"findConflict")) (Val #sl))
  {{ (ci : w64), RET #ci; raftLog l ls ∗
      ⌜match ls.conflict k es with
        | none => ci = W64 0
        | some j => uint.nat ci = k + j⌝ }}

end spec
end Raft
end EtcdGrove
end Perennial
