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
caller gives the slice back (with or without the capacity). -/
abbrev logSliceFromMsgApp.spec : Prop :=
  ∀ (p : Loc) (dq dqe : DFrac) (cap : Bool) (ms : MsgSt),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ msgPtsC p dq dqe cap ms }}
    (App (Val #(functions logSliceFromMsgApp [])) (Val #p))
  {{ (es : GoSlice) (els : List Loc),
      RET #(logSlice.mk ms.msg.Term' (entryID.mk ms.msg.LogTerm' ms.msg.Index') es);
      es ↦*{dqe} els ∗ ([∗list] q;e ∈ els;ms.ents, entRO q e) ∗
      (if cap then ownSliceCap Loc es (DFrac.own 1) else emp) ∗
      (∀ (cap' : Bool) (els' : List Loc) (ents' : List EntryM),
        es ↦*{dqe} els' -∗ ([∗list] q;e ∈ els';ents', entRO q e) -∗
        (if cap' then ownSliceCap Loc es (DFrac.own 1) else emp) -∗
        msgPtsC p dq dqe cap' { ms with ents := ents' }) }}

end spec

end EtcdGrove
end Perennial
