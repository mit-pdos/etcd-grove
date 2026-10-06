/-
Port of `election_proof/spec_raftLog__entries.v` (feb5c73d4).

Lean notes: ``es `prefix_of` l`` is `es <+: l`; `plog_from` is `plogFrom` (`Plog.lean`,
reached through `InvRaftPhys`, as in Rocq).
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

/-- `l.entries(i, maxSize)` -- the log from index `i` on, capped (`raftLog.entries.impl`,
`Perennial/Code/go_etcd_io/raft/v3.lean`; Rocq new/code/go_etcd_io/raft/v3.v:1102):

    if i > l.lastIndex() { return nil, nil }
    return l.slice(i, l.lastIndex()+1, maxSize)

So the error is always `nil` on this path, and the only premise is the lower one: `i`
must not be below the compaction boundary, or `raftLog.slice` would return
`ErrCompacted` (and the caller, `maybeSendAppend`, would go to `maybeSendSnapshot`).
The empty return is *not* an error -- a peer whose `Next` is past the end of the log
gets an empty `MsgApp`.

The result is read-only and the caller's for good, like `raftLog.slice`'s, and the log
comes back unchanged. Its contents are not described, because `maybeSendAppend` only
takes its length (for `Progress.SentEntries`) and its payload size, and puts it in a
message. (Until 2026-09-29 it was lent, and the log came back "on loan of the page",
`logstate.page`.) -/
abbrev raftLog.entries.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (i maxSize : w64),
  uint.Z ls.prev.index' + 1 ≤ uint.Z i →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"entries")) (Val #i))
      (Val #maxSize))
  {{ (s : GoSlice) (es : List raftpb.Entry), RET (PairV #s #interface.nil);
      ownRaftLog l ls ∗ s ↦*□ es ∗
      -- every entry returned is an entry of the log, and they are the log's from `i` on,
      -- cut short by `maxSize` (`raftLog.slice`)
      ⌜(∀ e, e ∈ es → e ∈ ls.sents ++ ls.uents) ∧
        es <+: plogFrom ls.prev (ls.sents ++ ls.uents) i⌝ }}

end spec

end EtcdGrove
end Perennial
