/- Port of election_proof/spec_isHardStateEqual.v (feb5c73d4). -/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvRaftPhys

@[expose] public section

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

/-- Field-wise equality of two `HardState`s; `HardState` has exactly the three fields
compared.

raft v3.7 (2026-10-15, stage R4): two `*pb.HardState`s compared through their getters
(`node.go:117`), each possibly `nil` (`hsOpt`, read as the zero record). -/
abbrev isHardStateEqual.spec : Prop :=
  ∀ (a b : Loc) (ha hb : HardStateM),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      "#Ha" ∷ hsOpt a ha ∗ "#Hb" ∷ hsOpt b hb }}
    (App (App (Val #(functions isHardStateEqual [])) (Val #a)) (Val #b))
  {{ RET #(decide (ha.Term' = hb.Term' ∧ ha.Vote' = hb.Vote' ∧ ha.Commit' = hb.Commit'));
      True }}

end spec

end EtcdGrove
end Perennial
