/-
Port of election_proof/spec_logSliceFromMsgApp.v (feb5c73d4).

Lean notes:
* `raft.logSlice.mk`/`raft.entryID.mk` are the generated constructors `logSlice.mk`
  and `entryID.mk`.
* The reference `logSliceFromMsgAppⁱᵐᵖˡ, new/code/go_etcd_io/raft/v3.v:4866` is to the
  Lean generated code `logSliceFromMsgApp.impl`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvRaftPhys

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

/-- `logSliceFromMsgApp(m)` repackages an append message as a `logSlice`
(`logSliceFromMsgApp.impl`, `Code/go_etcd_io/raft/v3.lean`; raft.go):

    func logSliceFromMsgApp(m *pb.Message) logSlice {
      return logSlice{
        term:    m.Term,
        prev:    entryID{term: m.LogTerm, index: m.Index},
        entries: m.Entries,
      }
    }

One exit, no panic, no call. It takes a *pointer* (`handleAppendEntries` passes `&m`)
and reads four fields; the `Entries` slice header is copied, not its contents, so
nothing about the entries is owned or returned here.

raft v3.7 (2026-10-15, stage R4): the fields are read through the getters (`m.GetTerm()`,
`m.GetLogTerm()`, `m.GetIndex()`, `m.GetEntries()`), and the `Entries` slice is lent as
`GetEntries` lends it (`Spec/.../raftpb/Message__GetEntries.lean`): its pointers at the message's
`dqe`, each entry read-only, the capacity when the message holds it (`cap`, `msgIn`), until the
caller gives the slice back (with or without the capacity).

(out_size C3, 2026-11-12) At the message's content (`msgPtsCC`, a received `MsgApp`'s form, its
entries' slice read-only): the entry objects are lent at their contents (`entRoC`), so that
`handleAppendEntries` appends them to the log with their sizes (`msgInC`). The `Entries` field is
read through `GetEntries`'s body (`wp_Message_GetEntries_field`): the getter's spec, over today's
form, does not say that the slice it returns is the field's. The message is given back without the
capacity (`maybeAppend` may adopt it). -/
abbrev logSliceFromMsgApp.spec : Prop :=
  ∀ (p : Loc) (cap : Bool) (c : MsgC),
  c.csUfNil →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      msgPtsCC p (DFrac.own 1) DFrac.discard cap c }}
    (App (Val #(functions logSliceFromMsgApp [])) (Val #p))
  {{ (es : GoSlice) (els : List Loc),
      RET #(logSlice.mk c.model.msg.Term' (entryID.mk c.model.msg.LogTerm' c.model.msg.Index') es);
      es ↦*□ els ∗ ([∗list] q;e ∈ els;c.f.entries, entRoC q e) ∗
      (if cap then ownSliceCap Loc es (DFrac.own 1) else emp) ∗
      (es ↦*□ els -∗ msgPtsCC p (DFrac.own 1) DFrac.discard false c) }}

end spec

end EtcdGrove
end Perennial
