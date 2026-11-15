/-
## `(*raftLog).entries(i, maxSize)` (internal)

**Users**: `maybeSendAppend` (`raft.go:640`: `ErrCompacted` means "send a snapshot"). Snippet
`raftlog/reads.go` (`ReqEntriesForSend`).

**Proof sketch**: past `lastIndex`: `nil`. Else `slice(i, lastIndex + 1, maxSize)` (`lastIndex + 1 <
2^64`: `Wf`).

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__entries.lean`: over `LogState`; `ErrCompacted` with
`logCompactedLb`. The premise bounding the range below `2^63` is new and is the memory limitation of
`extend` (`slice`).

**Margin**: the size limit is not stated.
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

/-- (internal) A non-empty prefix of the entries from `i` to the end (none past the end), or `ErrCompacted`. -/
def raftLog.entries.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i mx : w64),
  ls.lastIndex + 1 - uint.nat i < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"entries")) (Val #i)) (Val #mx))
  {{ (sl : GoSlice) (err : GoInterface), RET (PairV #sl #err); raftLog l ls ∗
      ((⌜err = interface.nil⌝ ∗ ∃ es, entriesRO sl (uint.nat i) es ∗
          ⌜(ls.lastIndex < uint.nat i ∧ es = []) ∨
           (uint.nat i ≤ ls.lastIndex ∧ es ≠ [] ∧ es <+: ls.range (uint.nat i) (ls.lastIndex + 1))⌝) ∨
       (errIs go_etcd_io.raft.v3.ErrCompacted err ∗ ⌜uint.nat i ≤ ls.compactFloor⌝ ∗ logCompactedLb l (uint.nat i))) }}

end spec
end Raft
end EtcdGrove
end Perennial
