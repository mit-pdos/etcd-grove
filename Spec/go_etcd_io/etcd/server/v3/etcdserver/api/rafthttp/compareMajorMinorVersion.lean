/-
`compareMajorMinorVersion(a, b)` (`util.go`; rafthttp stage 5e-3). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Stream

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.api

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`compareMajorMinorVersion(a, b)`** of two versions (not `nil`): some integer. -/
abbrev rafthttp.compareMajorMinorVersion.spec : Prop :=
  ∀ (a b : Loc),
  a ≠ null → b ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (App (Val (@! rafthttp.compareMajorMinorVersion)) (Val #a)) (Val #b))
  {{ (n : w64), RET #n; True }}

end spec

end EtcdGrove
end Perennial
