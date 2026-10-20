/-
`raftLog.subterm` (`log.go`, 2026-10-19, witness support): the term and subterm of the entry at
an index, and whether the log has it.
-/
module

public import Proof.go_etcd_io.raft.v3.InvReadylog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- `l.subterm(i)`:

    if i < l.firstIndex() || i > l.lastIndex() { return 0, 0, false }
    ents, err := l.slice(i, i+1, noLimit)
    if err != nil || len(ents) == 0 { return 0, 0, false }
    return ents[0].GetTerm(), ents[0].GetSubterm(), true

`true`: the entry at `i` of the log (past its boundary) is of that term and subterm; `false`:
subterm `0` (the index is behind the boundary, past the log, or compacted out of the storage). The
log comes back unchanged. -/
abbrev raftLog.subterm.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"subterm")) (Val #i))
  {{ (t st : w64) (ok : Bool), RET (PairV (PairV #t #st) #ok);
      ownRaftLog l ls ∗
      ⌜ok = true → uint.Z ls.prev.index' < uint.Z i ∧
        ∃ e, (ls.sents ++ ls.uents)[(uint.Z i - uint.Z ls.prev.index' - 1).toNat]? = some e ∧
          e.Term' = t ∧ e.Subterm' = st⌝ ∗
      ⌜ok = false → st = W64 0⌝ }}

end spec

end EtcdGrove
end Perennial
