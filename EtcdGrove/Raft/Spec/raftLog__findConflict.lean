/-
Port of election_proof/spec_raftLog__findConflict.v (feb5c73d4).

Lean notes:
* The reference `raftLog__findConflictⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:634` is to
  the Lean generated code `raftLog.findConflict.impl`.
-/
import EtcdGrove.Raft.InvRaftPhys
import EtcdGrove.Raft.Plog

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.findConflict(ents)`: the index of the first entry of the batch the log does not
have (a different term at that index, or nothing there); `0` if it has them all --
`plogFindConflict` (`Plog.lean`).

The body (`raftLog.findConflict.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`):

    for i := range ents {
        if id := pbEntryID(&ents[i]); !l.matchTerm(id) {
            if id.index <= l.lastIndex() {
                l.logger.Infof("found conflict ...", id.index,
                    l.zeroTermOnOutOfBounds(l.term(id.index)), id.term)
            }
            return id.index
        }
    }
    return 0

**Premise**: every entry of the batch is at or above the compaction boundary
`prev.index'`. It is not about the result (which is `plogFindConflict` regardless) but
about the log line: at a conflicting entry with `id.index <= lastIndex()` it makes
`term` return a `nil` error, which is what `zeroTermOnOutOfBounds`'s spec takes (see
there for why that spec stops at `nil`). `maybeAppend` supplies it: its batch starts
right after `a.prev`, which `matchTerm` has just placed at or above `prev.index'`. The
Go comment's "the index of the given entries MUST be continuously increasing" is not
needed for this function -- `plogFindConflict` is defined entry by entry, as the loop
is.

The batch is lent at any fraction and comes back; the log is unchanged. -/
abbrev raftLog.findConflict.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (es : GoSlice) (dq : DFrac) (ents : List raftpb.Entry),
  (∀ e ∈ ents, uint.Z ls.prev.index' ≤ uint.Z e.Index') →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "Hes" ∷ es ↦*{dq} ents }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"findConflict")) (Val #es))
  {{ RET #(plogFindConflict ls.prev (ls.sents ++ ls.uents) ents);
      ownRaftLog l ls ∗ es ↦*{dq} ents }}

end spec

end EtcdGrove
end Perennial
