/- Port of election_proof/spec_assertConfStatesEquivalent.v. -/
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

/-- `assertConfStatesEquivalent l cs1 cs2` returns iff `cs1.Equivalent(cs2)` is `nil`,
and otherwise calls `l.Panic`. Stated for the voters-only case
`ConfState.Equivalent`'s triple covers (`Spec/ConfState__Equivalent.lean`); the `Panic`
path is then unreachable, which is why the logger needs no contract here. -/
abbrev assertConfStatesEquivalent.spec : Prop :=
  ∀ (l : Logger) (cs1 cs2 : raftpb.ConfState) (v1 v2 : List w64) (dq1 dq2 : DFrac),
  v1 ≡ₚ v2 →
  cs1.VotersOutgoing'.len = W64 0 →
  cs1.Learners'.len = W64 0 →
  cs1.LearnersNext'.len = W64 0 →
  cs2.VotersOutgoing'.len = W64 0 →
  cs2.Learners'.len = W64 0 →
  cs2.LearnersNext'.len = W64 0 →
  cs1.AutoLeave' = cs2.AutoLeave' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 }}
    (App (App (App (Val #(functions assertConfStatesEquivalent [])) (Val #l))
      (Val #cs1)) (Val #cs2))
  {{ RET #();
      cs1.Voters' ↦*{dq1} v1 ∗
      cs2.Voters' ↦*{dq2} v2 }}

end spec

end EtcdGrove
end Perennial
