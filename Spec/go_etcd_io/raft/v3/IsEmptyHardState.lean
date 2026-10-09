/-
Port of `election_proof/spec_IsEmptyHardState.v` (feb5c73d4).
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

/-- `IsEmptyHardState st` is `st == emptyState`, and `emptyState` is the zero
`HardState` (`isInitialized`, `Proof.go_etcd_io.raft.v3.Base`; Rocq `v3_proof/base.v`). -/
abbrev IsEmptyHardState.spec : Prop :=
  ∀ (st : raftpb.HardState),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (Val #(functions IsEmptyHardState [])) (Val #st))
  {{ RET #(decide (st.Term' = W64 0 ∧ st.Vote' = W64 0 ∧ st.Commit' = W64 0));
      True }}

end spec

end EtcdGrove
end Perennial
