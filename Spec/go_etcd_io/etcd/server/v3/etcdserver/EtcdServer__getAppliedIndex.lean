/-
`s.getAppliedIndex()` (`server.go`): the applied index's atomic, a lower bound of the ghost applied index. Lean-first (no Rocq
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

/-- `s.getAppliedIndex()`, any goroutine: an index the applied index has reached
(`appliedAtLeast`; the applied index's invariant, the request path's unit 4b). -/
abbrev EtcdServer.getAppliedIndex.spec : Prop :=
  ∀ (s : Loc) (E : apply.AEnv GF) (γr : ReadNames),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvAppliedInv s E γr }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"getAppliedIndex")) (Val #()))
  {{ (v : w64), RET #v; appliedAtLeast γr v }}

end spec

end EtcdGrove
end Perennial
