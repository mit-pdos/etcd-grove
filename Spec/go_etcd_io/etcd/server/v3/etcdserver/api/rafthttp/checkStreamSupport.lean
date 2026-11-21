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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Assumptions]

/-- **`checkStreamSupport(v, t)`** of a version (not `nil`; read-only, 2026-11-20, prove-smalllibs: `Major`/`Minor` read it): some boolean. -/
abbrev rafthttp.checkStreamSupport.spec : Prop :=
  ∀ (v : Loc) (x : github_com.Masterminds.semver.v3.Version) (t : GoString),
  v ≠ null →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ v ↦□ x }}
    (App (App (Val (@! rafthttp.checkStreamSupport)) (Val #v)) (Val #t))
  {{ (b : Bool), RET #b; True }}

end spec

end EtcdGrove
end Perennial
