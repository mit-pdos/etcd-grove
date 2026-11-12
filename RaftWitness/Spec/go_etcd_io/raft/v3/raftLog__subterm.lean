/-
`(*raftLog).subterm` (`log.go:314`, witness support): the term and subterm of the entry at
an index. Lean-first (2026-10-20).
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.subterm(i)`: `(term, subterm, true)` of the entry at index `i`, or `(0, 0, false)`.

**Total**, like `raftLog.term`: below `firstIndex` or past `lastIndex` the body returns
`false` before reading anything; in between it calls `slice(i, i+1, noLimit)`, whose range
premise the two tests establish (`firstIndex >= prev.index + 1`, and `i + 1` does not wrap by
`ownRaftLog`'s `Hnowrap`). `slice` may still answer `ErrCompacted` when the application
compacted the storage up to the floor (`LogState.fl`); then the result is `false` too.

Only `ok = true` is described: the entry at `i` of the log the protocol model sees,
`plogEntryAt prev (sents ++ uents) i` (`Protocol/Model.lean`; the same log as `raftLog.term`'s
`plogTermAt`), carries the returned term and subterm. When it answers `false` nothing is
claimed (the entry at `i` may be behind the boundary, past the end, or compacted by the
application). The log comes back unchanged. -/
abbrev raftLog.subterm.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"subterm")) (Val #i))
  {{ (t st : w64) (ok : Bool), RET (PairV (PairV #t #st) #ok);
      ownRaftLog l ls ∗
      ⌜ok = true → ∃ e, plogEntryAt ls.prev (ls.sents ++ ls.uents) i = some e ∧
        e.Term' = t ∧ e.Subterm' = st⌝ }}

end spec

end EtcdGrove
end Perennial
