/-
`cindex.NewConsistentIndex(be)`. Lean-first (no Rocq counterpart); see `InvCindex.lean`.
-/
import EtcdGrove.Server.InvCindex

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.storage

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `NewConsistentIndex(be)`: a consistent index with index 0 (not loaded yet), applying
index 0, and backend `be`, as a `ConsistentIndexer`. -/
abbrev NewConsistentIndex.spec : Prop :=
  ∀ (be : GoInterface),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex }}
    (App (Val (@! NewConsistentIndex)) (Val #be))
  {{ (ci : Loc) (γ : CINames), RET #(interface.mkOk (go.GoType.PointerType consistentIndex.ty) #ci);
      isCI ci γ ∗ ciIdx γ (W64 0) ∗ ciApplying ci (W64 0) (W64 0) ∗ ciOwner ci be }}

end spec

end EtcdGrove
end Perennial
