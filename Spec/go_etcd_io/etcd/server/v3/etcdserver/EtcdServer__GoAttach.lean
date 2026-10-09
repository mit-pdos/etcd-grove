/-
`EtcdServer.GoAttach`: the trust boundary (names-only; the closure it may run in a goroutine (the apply thread's raises the NOSPACE alarm through raft) is not verified). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvApplier

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.GoAttach(f)` returns (it starts `f` in a goroutine tracked by the server, unless stopping). -/
abbrev EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (f : val),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val f))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
