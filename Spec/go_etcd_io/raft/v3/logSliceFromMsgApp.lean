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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
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
nothing about the entries is owned or returned here. -/
abbrev logSliceFromMsgApp.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (m : raftpb.Message),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ p ↦{dq} m }}
    (App (Val #(functions logSliceFromMsgApp [])) (Val #p))
  {{ RET #(logSlice.mk m.Term' (entryID.mk m.LogTerm' m.Index') m.Entries');
      p ↦{dq} m }}

end spec

end EtcdGrove
end Perennial
