/- Port of election_proof/spec_raft__maybeSendAppend.v (feb5c73d4).

Lean notes: Rocq's `send_msgs s ms <| nstate.prvals := pvs |>` is
`{ sendMsgs s ms with prvals := pvs }`, and the type of the untyped binder `pvs` is
written out.
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

/-- `r.maybeSendAppend(to, sendIfEmpty)` -- at most one `MsgApp` to one peer
(`raft.maybeSendAppend.impl`, `EtcdRaft/Code/go_etcd_io/raft/v3.lean`).

It can do four different things, and the postcondition is deliberately the weakest
statement true of all four:

  - `pr.IsPaused()` -> nothing sent, `false`;
  - `r.raftLog.term(pr.Next-1)` errors -> `maybeSendSnapshot`, which sends a `MsgSnap`
    or nothing;
  - no entries and `!sendIfEmpty` -> nothing sent, `false`;
  - otherwise one `MsgApp` to `to` at `r.Term`.

So: the outbox grows by *some* list of messages `ReplOk` allows (`Protocol/Model.lean`:
an `App` from `id` to `to` at the current term, carrying entries of the log and a
commit index no larger than the log's, or a `Snap`) -- in fact zero or one, but nothing
above needs that, and saying "one" would be false. This is the same weakening as
`raft.bcastAppend.spec`'s. (Until 2026-10-01: `AppSends`, `App`s with only the sender
and term pinned.)

The premises. `to ≠ id` is what `send_ok`'s `MsgApp` clause needs (`send` panics on a
self-addressed `MsgApp`); `bcastAppend`'s closure tests `id == r.id` and returns first.
`to ∈ cfg` is what makes `r.trk.Progress[to]` hit: a miss returns the zero `*Progress`,
i.e. `null`, and the `pr.IsPaused()` that follows would dereference it. `Visit` only
enumerates voters, so `bcastAppend` has it. -/
abbrev raft.maybeSendAppend.spec : Prop :=
  ∀ (cfg : GSet w64) (r : Loc) (id : w64) (s : NState) (to : w64) (sendIfEmpty : Bool),
  to ≠ id →
  to ∈ cfg →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "Hphys" ∷ ownRaftPhys cfg r id s }}
    (App (App (Val (r @!! go.GoType.PointerType raft.ty @!! go!"maybeSendAppend"))
      (Val #to)) (Val #sendIfEmpty))
  {{ (b : Bool) (ms : List Msg) (pvs : GMap w64 Progress), RET #b;
      ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜ReplSends id s ms⌝ ∗
      -- `SentEntries`, `SentCommit`, `BecomeSnapshot` leave `Match` alone
      ⌜prvalsMatch pvs = prvalsMatch s.prvals⌝ }}

end spec

end EtcdGrove
end Perennial
