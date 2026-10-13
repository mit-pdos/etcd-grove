/-
`monitorFileDescriptor(lg, done)` (`metrics.go`): names-only, one of the goroutines `Start` attaches. Lean-first (the request path's unit 4c).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `monitorFileDescriptor(lg, done)` returns (names-only: it logs the file descriptor usage until
`done` is closed). -/
abbrev monitorFileDescriptor.spec : Prop :=
  ∀ (lg : Loc) (done : GoChan),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.monitorFileDescriptor)) (Val #lg))
      (Val #done))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
