/-
`confchange.incoming(voters)` is `voters[0]`, the incoming majority config of a joint
config. Lean-first (no Rocq counterpart); see `InvConfchange.lean`.
-/
module

public import Proof.go_etcd_io.raft.v3.InvConfchange

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

/-- `incoming` returns the first component of the `[2]MajorityConfig`. -/
abbrev confchange.incoming.spec : Prop :=
  ∀ (jc : quorum.JointConfig) (v0 v1 : Loc),
  jc.arr = [v0, v1] →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange }}
    (App (Val #(functions confchange.incoming [])) (Val #jc))
  {{ RET #v0; True }}

end spec

end EtcdGrove
end Perennial
