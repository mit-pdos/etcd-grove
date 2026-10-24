/-
`minClusterVersion(h)` (`util.go`; rafthttp stage 6e, 2026-10-24): a peer's minimum cluster version
from its headers. Lean-first.
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

/-- **`minClusterVersion(h)`** of a header map `hm` holding `hs`: a version (not `nil`), or a panic
when its `X-Min-Cluster-Version` does not parse (`semver.MustParse`; unset is `"2.0.0"`). -/
abbrev rafthttp.minClusterVersion.spec : Prop :=
  ∀ (hm : Loc) (hs : List (GoString × GoString)),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ http.hdrAt hm hs }}
    (App (Val (@! rafthttp.minClusterVersion)) (Val #hm))
  {{ (r : val), RET r; ⌜(∃ v : Loc, r = #v ∧ v ≠ null) ∨ ∃ p : val, r = PanicV p⌝ }}

end spec

end EtcdGrove
end Perennial
