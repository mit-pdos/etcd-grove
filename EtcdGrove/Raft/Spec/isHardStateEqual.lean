/- Port of election_proof/spec_isHardStateEqual.v (feb5c73d4). -/
import EtcdGrove.Raft.InvRaftPhys

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

/-- Field-wise equality of two `HardState`s; `HardState` has exactly the three fields
compared. -/
abbrev isHardStateEqual.spec : Prop :=
  ∀ (a b : raftpb.HardState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (App (Val #(functions isHardStateEqual [])) (Val #a)) (Val #b))
  {{ RET #(decide (a.Term' = b.Term' ∧ a.Vote' = b.Vote' ∧ a.Commit' = b.Commit'));
      True }}

end spec

end EtcdGrove
end Perennial
