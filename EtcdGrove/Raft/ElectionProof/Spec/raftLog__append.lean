/-
Port of `election_proof/spec_raftLog__append.v`.
-/
import EtcdGrove.Raft.ElectionProof.InvRaftPhys

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

/-- `l.append(ents)`: add a batch to the end of the log, returning the new last index
(`raftLog.append.impl`, `Perennial/Code/go_etcd_io/raft/v3.lean`).

The body is short and has one panic:

    if len(ents) == 0 { return l.lastIndex() }
    if after := ents[0].Index - 1; after < l.committed {
        l.logger.Panicf("after(%d) is out of range [committed(%d)]", …)
    }
    l.unstable.truncateAndAppend(ents)
    return l.lastIndex()

The postcondition *names* the new state: `ls` with `uents ++ ents` as the unstable
suffix.

The premises are what makes the batch a legal continuation of the log, and they are
exactly what discharges the `Panicf`:

- `Hidx`: the whole log, batch included, still has contiguous indices from
  `prev.index+1`. In particular `ents[0].Index` is `prev.index+|sents|+|uents|+1`, so
  `after` is the current last index, which is `≥ l.committed` by `ownRaftLog`'s
  `Hcommitted` -- the panic is dead code, not assumed away. It also fixes the `after`
  subtraction: `ents[0].Index ≥ 1`, so it does not wrap.
- `Hnorm`: the batch holds no configuration change, which is what keeps `ownRaftLog`'s
  `HnoConfChange` true of the longer log. Under this development's scope no
  configuration change is ever proposed (`InvRaftlog.lean`), so a caller supplies it
  from the entry it built.
- `Hnowrap`: the *new* last index still leaves room, i.e.
  `prev.index + |sents| + |uents| + |ents| + 1 < 2^64`. `ownRaftLog` asserts this bound
  at the old length and a longer log needs it at the new one, so it cannot be derived
  and has to be asked for. See `Spec/raft__appendEntry.lean` for where the caller gets
  it.

The batch is *lent*: `truncateAndAppend` copies the entry values into
`unstable.entries`, so `es` comes back at the caller's fraction. -/
abbrev raftLog.append.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (ents : List raftpb.Entry) (es : GoSlice) (dq : DFrac),
  LogIndicesOk ls.prev (ls.sents ++ ls.uents ++ ents) →
  (∀ e ∈ ents, e.Type' = EntryNormal) →
  uint.Z ls.prev.index' + (ls.sents.length : Int) + (ls.uents.length : Int)
    + (ents.length : Int) + 1 < 2^64 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls ∗
      "Hes" ∷ es ↦*{dq} ents }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"append")) (Val #es))
  {{ (li : w64), RET #li;
      ownRaftLog l { ls with uents := ls.uents ++ ents } ∗ es ↦*{dq} ents ∗
      ⌜uint.Z li = uint.Z ls.prev.index' + (ls.sents.length : Int)
                   + (ls.uents.length : Int) + (ents.length : Int)⌝ }}

end spec

end EtcdGrove
end Perennial
