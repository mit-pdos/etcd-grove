/-
Port of `election_proof/spec_MustSync.v` (857d09190).
-/
import EtcdGrove.Raft.ElectionProof.InvReadylog

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

/-- `MustSync(st, prevst, entsnum)` (`rawnode.go:193`): whether the `Ready` has to be
written durably before its messages are sent --
`entsnum != 0 || st.Vote != prevst.Vote || st.Term != prevst.Term`. -/
abbrev MustSync.spec : Prop :=
  ∀ (st prevst : raftpb.HardState) (n : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 }}
    (App (App (App (Val #(functions MustSync [])) (Val #st)) (Val #prevst)) (Val #n))
  {{ RET #(decide (n ≠ W64 0 ∨ st.Vote' ≠ prevst.Vote' ∨ st.Term' ≠ prevst.Term'));
      True }}

end spec

end EtcdGrove
end Perennial
