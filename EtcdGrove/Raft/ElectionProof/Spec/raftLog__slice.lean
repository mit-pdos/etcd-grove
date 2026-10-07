/-
Port of election_proof/spec_raftLog__slice.v (857d09190).

Lean notes:
* The return `(#s, #interface.nil)` is `PairV #s #interface.nil`;
  `Z.of_nat (length es)` is `(es.length : Int)`; `` `prefix_of` `` is `<+:`.
* `plog_from` is `plogFrom` (`Plog.lean`, imported through `InvRaftPhys`; the Rocq
  file does not `Require` `plog` either).
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

/-- `l.slice(lo, hi, maxSize)`: a non-empty prefix of the log entries at `[lo, hi)`,
cut to roughly `maxSize` bytes (`log.go:497`).

Stated at the log's state `ls`: it calls `mustCheckOutOfBounds` (hence
`firstIndex`/`lastIndex`) and reads the unstable suffix and the `Storage` directly. The
range premise makes every failure path dead: `mustCheckOutOfBounds` returns `nil`,
`Storage.Entries` cannot return `ErrCompacted`/`ErrUnavailable` (the contract in
`InvStorage.lean` says so on this range), so the `Panicf` and the `panic` are
unreachable, and `lo < hi` rules out the empty early return.

The result **aliases the log** in two of the three cases (a sub-slice of
`unstable.entries`, or one the `Storage` handed out); in the third (a range spanning
the stable/unstable boundary) it is a fresh slice from `extend`. In every case it is
returned **read-only and for good**, `s ↦*□ es`, and the log comes back unchanged: no
entry of the log is ever written again once it is in it -- `unstable` never writes in
place (`ownUnstable`, `InvRaftlog.lean`) and `Storage` promises the same (`isStorage`'s
`Entries`, `InvStorage.lean`) -- so there is nothing to give back. `maybeSendAppend`
relies on it: it puts the result in a `MsgApp`, which `r.msgs` keeps, and reads it again
(`payloadsSize`) after `r.send`. (Until 2026-09-29 the result was *lent*, and the log
came back "on loan of that page", `logstate.page`.)

What the result *is* is stated only as far as `scan` and its callers need: non-empty,
at most `hi - lo` entries, every one an entry of the log. That is enough for
`hasUnappliedConfChanges` (`HnoConfChange` is a fact about every entry) and for
`scan`'s progress. If a later caller needs the indices -- `maybeSendAppend` will --
strengthen this triple rather than adding a second one. -/
abbrev raftLog.slice.spec : Prop :=
  ∀ (l : Loc) (ls : LogState) (lo hi maxSize : w64),
  uint.Z ls.prev.index' + 1 ≤ uint.Z lo ∧ uint.Z lo < uint.Z hi ∧
    uint.Z hi ≤ uint.Z ls.prev.index' + (ls.sents.length : Int)
      + (ls.uents.length : Int) + 1 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "Hlog" ∷ ownRaftLog l ls }}
    (App (App (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"slice"))
      (Val #lo)) (Val #hi)) (Val #maxSize))
  {{ (s : GoSlice) (es : List raftpb.Entry),
      RET (PairV #s #interface.nil);
      ownRaftLog l ls ∗ s ↦*□ es ∗
      ⌜es ≠ [] ∧
        (es.length : Int) ≤ uint.Z hi - uint.Z lo ∧
        (∀ e, e ∈ es → e ∈ ls.sents ++ ls.uents) ∧
        -- the log's entries at `[lo, lo+1, ...]`, cut short by `maxSize`
        es <+: plogFrom ls.prev (ls.sents ++ ls.uents) lo⌝ ∗
      -- no spare capacity anyone else owns (2026-10-05): every exit re-caps
      -- (`ents[:len:len]`), returns `Storage.Entries`' capped slice, or `extend`s into a
      -- fresh one -- so the caller may hand the slice on where its capacity is demanded
      -- (`Step`'s `Hents_cap`, for `Advance`'s `MsgStorageApplyResp`)
      ownSliceCap raftpb.Entry s (DFrac.own 1) }}

end spec

end EtcdGrove
end Perennial
