/- Port of election_proof/spec_raft__maybeSendAppend.v. -/
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

/-- `r.maybeSendAppend(to, sendIfEmpty)` -- at most one `MsgApp` to one peer
(`raft.maybeSendAppend.impl`, `Perennial/Code/go_etcd_io/raft/v3.lean`).

It can do four different things, and the postcondition is deliberately the weakest
statement true of all four:

  - `pr.IsPaused()` -> nothing sent, `false`;
  - `r.raftLog.term(pr.Next-1)` errors -> `maybeSendSnapshot`, which sends a `MsgSnap`
    (model-invisible) or nothing;
  - no entries and `!sendIfEmpty` -> nothing sent, `false`;
  - otherwise one `MsgApp` to `to` at `r.Term`.

So: the outbox grows by *some* list of `App`s from `id` at the current term -- in fact
zero or one, but nothing above needs that, and saying "one" would be false. This is the
same weakening as `raft.bcastAppend.spec`'s.

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
  {{ (b : Bool) (ms : List Msg) (pvs : GMap w64 (tracker.Progress × tracker.Inflights)),
      RET #b;
      ownRaftPhys cfg r id { sendMsgs s ms with prvals := pvs } ∗
      ⌜AppSends id s.term ms⌝ }}

end spec

end EtcdGrove
end Perennial
