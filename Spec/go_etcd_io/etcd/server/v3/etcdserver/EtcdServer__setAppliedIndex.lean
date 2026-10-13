/-
`(*EtcdServer).setAppliedIndex(v)` (server.go). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.setAppliedIndex(v')`, by the apply thread (the only writer: `srvAppliedOwn γr v`, `v <
v'`), right after applying the entry at index `v'`, with mvcc's certificate of the KV log `L` it
left (the request path's unit 4b): it stores `v'` into the atomic `s.appliedIndex` and, at that
point, raises the ghost applied index to `v'` and deposits `L` as the log applied through `v'`. -/
abbrev EtcdServer.setAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (v v' : w64) (L : mvcc.Log),
  uint.Z v < uint.Z v' →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAppliedInv s E γr ∗ srvAppliedOwn γr v ∗ mvcc.idxCert E.γ.idx L }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"setAppliedIndex")) (Val #v'))
  {{ RET #(); srvAppliedOwn γr v' ∗ appliedAtLeast γr v' ∗ appliedLogAt γr v' L }}

end spec

end EtcdGrove
end Perennial
