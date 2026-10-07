/- Port of election_proof/spec_pbEntryID.v (feb5c73d4). -/
import EtcdGrove.Raft.InvRaftPhys
import EtcdGrove.Raft.Plog

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

/-- `pbEntryID(entry)`: the id (`term`, `index`) of the entry behind the pointer --
`entId` (`Plog.lean`). Two field loads and a struct literal (`pbEntryID.impl`,
`Perennial/Code/go_etcd_io/raft/v3.lean`). The entry is lent at any fraction:
`findConflict` calls it on `&ents[i]` of a batch it holds read-only. -/
abbrev pbEntryID.spec : Prop :=
  ∀ (p : Loc) (dq : DFrac) (e : raftpb.Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ "He" ∷ p ↦{dq} e }}
    (App (Val #(functions pbEntryID [])) (Val #p))
  {{ RET #(entId e); p ↦{dq} e }}

end spec

end EtcdGrove
end Perennial
