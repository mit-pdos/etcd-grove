/-
`EtcdServer.MemberID` (`server.go`: it reads `s.memberID`). Lean-first (no Rocq counterpart).
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

/-- `s.MemberID()` returns `s.memberID` (read-only). -/
abbrev EtcdServer.MemberID.spec : Prop :=
  ∀ (s : Loc) (id : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvMemberIDAddr s ↦□ id }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"MemberID")) (Val #()))
  {{ RET #id; True }}

end spec

end EtcdGrove
end Perennial
