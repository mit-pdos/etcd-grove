/-
`checkStreamSupport(v, t)` (`stream.go`; rafthttp stage 5e-3). Lean-first. (Proved in stage 6e,
2026-10-24, over rafthttp's fact of the untranslated `supportedStream`: a read-only map of read-only
slices, `supportedStream_init`.)
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

/-- **`checkStreamSupport(v, t)`** of a version (not `nil`): some boolean. -/
abbrev rafthttp.checkStreamSupport.spec : Prop :=
  ∀ (v : Loc) (t : GoString),
  v ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp }}
    (App (App (Val (@! rafthttp.checkStreamSupport)) (Val #v)) (Val #t))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
