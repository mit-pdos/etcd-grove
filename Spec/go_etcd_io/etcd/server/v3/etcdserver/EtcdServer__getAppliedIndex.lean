/-
`s.getAppliedIndex()` (`server.go`): the applied index's atomic. Lean-first (no Rocq
counterpart).
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

/-- `s.getAppliedIndex()`, any goroutine: some index (the atomic, in its invariant). -/
abbrev EtcdServer.getAppliedIndex.spec : Prop :=
  ∀ (s : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAtomicU64 (structFieldRef EtcdServer go!"appliedIndex" s) }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"getAppliedIndex")) (Val #()))
  {{ (v : w64), RET #v; True }}

end spec

end EtcdGrove
end Perennial
