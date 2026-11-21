/-
`serverVersion(h)` (`util.go`; rafthttp stage 5e-3): a peer's version from its headers. Lean-first.
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

/-- **`serverVersion(h)`** of a header map `hm` holding `hs`: a version (not `nil`), or (2026-10-24,
rafthttp stage 6e: any header, a request handler's) a panic when its `X-Server-Version` does not
parse (`semver.MustParse`), never when it does (`verHdrOk`: unset, or valid). The version is
read-only (2026-11-20, prove-smalllibs: `Version`'s methods read it). -/
abbrev rafthttp.serverVersion.spec : Prop :=
  ∀ (hm : Loc) (hs : List (GoString × GoString)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ http.hdrAt hm hs }}
    (App (Val (@! rafthttp.serverVersion)) (Val #hm))
  {{ (r : val), RET r; (∃ (v : Loc) (x : github_com.Masterminds.semver.v3.Version), ⌜r = #v ∧ v ≠ null⌝ ∗ v ↦□ x) ∨
      ⌜¬ verHdrOk hs ∧ ∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
