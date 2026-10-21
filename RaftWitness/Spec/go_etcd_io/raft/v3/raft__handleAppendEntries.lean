/- Port of election_proof/spec_raft__handleAppendEntries.v (feb5c73d4).

## `raft.handleAppendEntries`

The follower's handling of a `MsgApp` (`raft.handleAppendEntries.impl`,
`Code/go_etcd_io/raft/v3.lean`; raft.go:1778). Three exits, in the order the
body takes them:

1. `a.prev.index < r.raftLog.committed` (stale): send `MsgAppResp{To: m.From, Index:
   committed}` and return;
2. `r.raftLog.maybeAppend(a, m.Commit)` answers `ok`: send `MsgAppResp{To: m.From,
   Index: mlastIndex}` and return;
3. otherwise (reject): a `Debugf` whose arguments call
   `zeroTermOnOutOfBounds(term(m.Index))` -- with `m.Index` possibly past the last
   index, so `term` may return `ErrUnavailable`; see
   `Spec/raftLog__zeroTermOnOutOfBounds.lean` -- then
   `hintIndex, hintTerm := findConflictByTerm(min(m.Index, lastIndex()), m.LogTerm)`
   and `MsgAppResp{To: m.From, Index: m.Index, Reject: true, RejectHint: hintIndex,
   LogTerm: hintTerm}`.

No exit writes a raft field: the struct changes only through the log (`maybeAppend`)
and the outbox (`send`).

**The messages, as `send` queues them** (`SendOk`'s `MsgAppResp` clause (d),
`Spec/raft__send.lean`): `From` stamped `id`, `Term` stamped `s.term`, `Entries` nil
(so `ents = []`), every field the literal does not name zero. So the abstraction of
the literal `m'` is `absMsgFrom .appResp m' id s.term []`, i.e. `appResp` below --
exactly the messages `Protocol/Model.lean`'s `Step.appStale` / `Step.appAccept` /
`Step.appReject` send (`Msg.mk .appResp id m.src term reject index logterm (W64 0)
rejecthint []`), with `logterm := hintTerm` and `rejecthint := hintIndex` on a rejection
and `0` for both otherwise.

Lean notes: Rocq's `app_resp` and `handle_app_result` are `appResp` and
`HandleAppResult` (a Prop-valued definition). The Rocq argument named `to` is `dst`.

raft v3.7 (2026-10-15, stage R4): `m` is a `*pb.Message` (`ml`), taken as `stepFollower`/
`stepCandidate` pass it, a received message (`msgIn ml □`: its entries read-only, the `Entries`
slice's capacity owned, which `maybeAppend` may adopt) and not given back; read through its
getters (`logSliceFromMsgApp`); every reply shares `m`'s `From` cell (`To: m.From`, read-only).
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys
public import Proof.go_etcd_io.raft.v3.Plog

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.raft.v3

section results
variable [FfiSyntax]

/-- The `MsgAppResp` `handleAppendEntries` queues, as the model sees it:
`Msg.mk ty src dst term reject index logterm commit rejecthint entries`. -/
def appResp (id : w64) (s : NState) (dst : w64) (reject : Bool)
    (index hintterm hint : w64) : Msg :=
  Msg.mk .appResp id dst s.term reject index hintterm (W64 0) hint []

/-- The three exits, as a relation between the state `s` the call starts in and the
state `s'` it ends in. The disjuncts are exclusive: the first on `m.Index < committed`,
the second and third on whether `(m.LogTerm, m.Index)` matches the log
(`plogMaybeAppend` is `none` exactly when it does not).

- stale: the reply carries `committed`;
- accept: the log is `maybeAppend`'s new log -- `prev` and `applied` unchanged, the
  entries `plogMaybeAppend`'s, `committed` raised to `min(m.Commit, lastnewi)`
  (`plogCommitTo`), `applying`, the pending snapshot and `unpersisted` unchanged
  (2026-10-09) -- and the reply carries `lastnewi`. `ls'` is existential because
  `maybeAppend`'s spec says no more about the `sents`/`uents` split;
- reject: state unchanged but for the reply; the hint is *some* `(hint, hintterm)`
  (`findConflictByTerm`'s spec pins only `hint ≤ min(m.Index, lastIndex())`, and the
  model allows any). -/
def HandleAppResult (id : w64) (s : NState) (m : MessageM)
    (ents : List EntryM) (s' : NState) : Prop :=
  let ls := s.logst
  let es := ls.sents ++ ls.uents
  let prev := entryID.mk m.LogTerm' m.Index'
  let dst := m.From'
  (uint.Z m.Index' < uint.Z ls.committed ∧
   s' = sendMsgs s [appResp id s dst false ls.committed (W64 0) (W64 0)])
  ∨
  (uint.Z ls.committed ≤ uint.Z m.Index' ∧
   ∃ (lastnewi : w64) (es' : List EntryM) (ls' : LogState),
     plogMaybeAppend ls.prev es prev ents = some (lastnewi, es') ∧
     ls'.prev = ls.prev ∧
     ls'.sents ++ ls'.uents = es' ∧
     ls'.applied = ls.applied ∧
     ls'.committed =
       plogCommitTo ls.committed
         (if uint.Z m.Commit' < uint.Z lastnewi then m.Commit' else lastnewi) ∧
     (ls'.applying = ls.applying ∧ ls'.snap = ls.snap ∧ ls'.unpersisted = ls.unpersisted ∧
      ls'.prev = ls.prev ∧ ls'.stored = ls.stored ∧ ls'.storage = ls.storage ∧
      -- (D19i part 1) the floor
      ls'.fl = ls.fl) ∧
     s' = sendMsgs { s with logst := ls' }
            [appResp id s dst false lastnewi (W64 0) (W64 0)])
  ∨
  (uint.Z ls.committed ≤ uint.Z m.Index' ∧
   ¬ PlogMatches ls.prev es prev ∧
   ∃ (hint hintterm : w64),
     -- (2026-10-19, D21 M3) `findConflictByTerm`'s hint (`RejHintOk`)
     RejHintOk ls.prev es m.Index' m.LogTerm' hint ∧
     s' = sendMsgs s [appResp id s dst true m.Index' hintterm hint])

end results

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- Premises -- `maybeAppend`'s (`Spec/raftLog__maybeAppend.lean`), restated at the
message, since `a = logSliceFromMsgApp(&m)` is `{term: m.Term, prev: (m.LogTerm,
m.Index), entries: m.Entries}`:

- the batch is a well-formed log slice after `(m.LogTerm, m.Index)` and does not wrap
  (until 2026-10-13 also: holds no configuration change);
- **the conflict fact**, as hypothetical as the code allows: only when the stale test
  has failed (`committed ≤ m.Index`) and the prefix matches is `maybeAppend`'s `Panicf`
  reachable, and there the conflict index must be `0` or above `committed`
  (`app_no_conflict_below_commit`, `Protocol/Facts.lean`);
- the `Entries` slice read-only with its capacity owned, because `maybeAppend` may
  adopt it as the unstable suffix. On the other two exits the capacity is simply
  dropped. (Stage R4: the message, `msgIn ml □`, holds both.)

`m.Type = MsgApp` (stage R5): the body never reads it, but a received message holds its
`Entries` capacity only when it is a `MsgApp` (`msgIn`'s `needsCap`), and `maybeAppend` needs it;
both callers are in their `MsgApp` arm.

Not needed, and so not premises: `m.From ≠
0` and `m.To = id` (no panic depends on them; `send`'s `MsgAppResp` clause allows any
`To`, the node itself included), `m.Term` (only `a.term`, which nothing reads). -/
abbrev raft.handleAppendEntries.spec : Prop :=
  ∀ (c : CfgM) (r : Loc) (id : w64) (s : NState)
    (ml : Loc) (m : MessageM) (ents : List EntryM) (sn : Option SnapshotM) (ctx : List w8)
    (rs : List Loc),
  PlogWf (entryID.mk m.LogTerm' m.Index') ents →
  uint.Z m.Index' + (ents.length : Int) + 1 < 2^64 →
  (let ls := s.logst
   let es := ls.sents ++ ls.uents
   uint.Z ls.committed ≤ uint.Z m.Index' →
   PlogMatches ls.prev es (entryID.mk m.LogTerm' m.Index') →
   plogFindConflict ls.prev es ents = W64 0 ∨
   uint.Z ls.committed < uint.Z (plogFindConflict ls.prev es ents)) →
  -- from another node (2026-10-10; `Step`'s premise): every reply goes to `m.From`, and
  -- a self-addressed rejection would not be steppable (`AAMsgOk`)
  m.From' ≠ id →
  -- a `MsgApp` (stage R5): only then does `msgIn` hold the `Entries` capacity
  m.Type' = MsgApp →
  -- (2026-10-16, stage R8a, D11) not at a leader: `maybeAppend` may truncate the log, and a
  -- leader's log only grows (`PrvalsOk`); a leader never handles a `MsgApp` of its term
  s.role ≠ .leader →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhysCV c c.voters r id s ∗
      "Hm" ∷ msgIn ml DFrac.discard ⟨m, ents, sn, ctx, rs⟩ }}
    (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"handleAppendEntries")) (Val #ml))
  {{ (s' : NState), RET #();
      ownRaftPhysCV c c.voters r id s' ∗ ⌜HandleAppResult id s m ents s'⌝ }}

end spec

end EtcdGrove
end Perennial
