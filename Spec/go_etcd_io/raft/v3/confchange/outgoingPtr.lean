/-
`confchange.outgoingPtr(&voters)` is `&voters[1]`. Lean-first (no Rocq counterpart);
see `InvConfchange.lean`.
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

/-- `outgoingPtr` returns the address of the second element of the `[2]MajorityConfig`. -/
abbrev confchange.outgoingPtr.spec : Prop :=
  ∀ (vp : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.confchange }}
    (App (Val #(functions confchange.outgoingPtr [])) (Val #vp))
  {{ RET #(arrayIndexRef quorum.MajorityConfig 1 vp); True }}

end spec

end EtcdGrove
end Perennial
