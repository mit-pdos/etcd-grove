/-
Port of `election_proof/spec_raftLog__lastEntryID.v`.
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

/-- ## The interface other files use

These four statements are what `InvRaftPhys.lean`, `InvMisc.lean` and the `Proof/*.lean`
files call. The first three are unchanged from when they were axioms: they say nothing
about the value returned, only that the call returns and gives the log back. That is
all the election path needs -- `isUpToDate` returning a wrong answer can only make the
node decline to vote, which is always protocol-legal. -/
abbrev raftLog.lastEntryID.spec : Prop :=
  ∀ (l : Loc) (ls : LogState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ ownRaftLog l ls }}
    (App (Val (l @!! go.GoType.PointerType raftLog.ty @!! go!"lastEntryID")) (Val #()))
  {{ (e : entryID), RET #e; ownRaftLog l ls }}

end spec

end EtcdGrove
end Perennial
