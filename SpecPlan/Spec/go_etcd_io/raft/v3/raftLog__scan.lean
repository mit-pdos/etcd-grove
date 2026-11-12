/-
## `(*raftLog).scan(lo, hi, pageSize, v)` (internal)

**Users**: `hasUnappliedConfChanges` (`raft.go:1027`: `[applied+1, committed]`, a callback that
breaks at the first conf change). Snippet `raftlog/reads.go` (`ReqScanConfChanges`).

**Proof sketch**: a loop of `slice(lo, hi, pageSize)` (no `ErrCompacted`: above the floor; never
empty), the callback's triple on each page with `I` of the pages before; stop at its first error.

**Changes**: from `specs-ref/Spec/go_etcd_io/raft/v3/raftLog__scan.lean`: over `LogState`.

**Margin**: none.
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

/-- (internal) Visit the entries of `[lo, hi)` page by page; `nil` once all were visited, or the callback's first error. -/
def raftLog.scan.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lo hi ps : w64) (v : val) (I : List LogEntry → IProp GF)
    (B : GoInterface → IProp GF),
  ls.compactFloor < uint.nat lo → uint.nat lo ≤ uint.nat hi → uint.nat hi ≤ ls.lastIndex + 1 →
  uint.nat hi - uint.nat lo < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ raftLog l ls ∗ I [] ∗
      □ (∀ (sl : GoSlice) (done es : List LogEntry),
          {{ entriesRO sl (uint.nat lo + done.length) es ∗ I done ∗
              ⌜es ≠ [] ∧ done ++ es <+: ls.range (uint.nat lo) (uint.nat hi)⌝ }}
            (App (Val v) (Val #sl))
          {{ (err : GoInterface), RET #err;
              (⌜err = interface.nil⌝ ∗ I (done ++ es)) ∨ (⌜err ≠ interface.nil⌝ ∗ B err) }}) }}
    (App (App (App (App (Val (l @!! go.GoType.PointerType go_etcd_io.raft.v3.raftLog.ty @!! go!"scan")) (Val #lo)) (Val #hi)) (Val #ps)) (Val v))
  {{ (err : GoInterface), RET #err; raftLog l ls ∗
      ((⌜err = interface.nil⌝ ∗ I (ls.range (uint.nat lo) (uint.nat hi))) ∨
       (⌜err ≠ interface.nil⌝ ∗ B err)) }}

end spec
end Raft
end EtcdGrove
end Perennial
