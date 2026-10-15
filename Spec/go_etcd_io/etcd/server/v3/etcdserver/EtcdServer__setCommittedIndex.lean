/-
`(*EtcdServer).setCommittedIndex(v)` (server.go). Lean-first (no Rocq counterpart); the request
path's unit 4c (2026-10-13).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvProposer

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.setCommittedIndex(v')` by the writer (the ready handler's `updateCommittedIndex`, on the
raft loop), with its half of the committed index at `v ≤ v'`: the atomic and the ghost committed
index move to `v'` (`committedAtLeast γr v'`). -/
abbrev EtcdServer.setCommittedIndex.spec : Prop :=
  ∀ (s : Loc) (γr : ReadNames) (v v' : w64), uint.Z v ≤ uint.Z v' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvCommittedInv s γr ∗ srvCommittedOwn γr v }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setCommittedIndex")) (Val #v'))
  {{ RET #(); srvCommittedOwn γr v' ∗ committedAtLeast γr v' }}

end spec

end EtcdGrove
end Perennial
