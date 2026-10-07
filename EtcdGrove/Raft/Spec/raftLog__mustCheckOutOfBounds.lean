/-
Port of election_proof/spec_raftLog__mustCheckOutOfBounds.v (feb5c73d4).
-/
import EtcdGrove.Raft.InvRaftPhys

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

/-- `l.mustCheckOutOfBounds(lo, hi)`: `nil` when
`firstIndex <= lo <= hi <= lastIndex + 1`.

The range premise is about the log's state `ls`; the function calls `firstIndex` and
`lastIndex` on the log. The two `Panicf`s (`lo > hi`, and `hi` past the end) and the
`ErrCompacted` return (`lo < firstIndex`) are all excluded by the range premise, so the
result is exactly `nil` -- which is what lets `raftLog.slice` take its non-error
path. -/
abbrev raftLog.mustCheckOutOfBounds.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lo hi : w64),
  uint.Z ls.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo ≤ uint.Z hi ∧
    uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"mustCheckOutOfBounds"))
      (Val #lo)) (Val #hi))
  {{ RET #interface.nil; ownRaftLog l ls }}

end spec

end EtcdGrove
end Perennial
