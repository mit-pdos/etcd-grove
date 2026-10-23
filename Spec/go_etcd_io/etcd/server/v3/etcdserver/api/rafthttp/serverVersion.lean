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
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **`serverVersion(h)`** of a header map whose `X-Server-Version` is unset or parses
(`verHdrOk`, a raft member's response headers): the parsed version (`"2.0.0"` if unset), not
`nil`; no panic. -/
abbrev rafthttp.serverVersion.spec : Prop :=
  ∀ (hm : Loc) (hs : List (GoString × GoString)),
  verHdrOk hs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ http.hdrAt hm hs }}
    (App (Val (@! rafthttp.serverVersion)) (Val #hm))
  {{ (v : Loc), RET #v; ⌜v ≠ null⌝ }}

end spec

end EtcdGrove
end Perennial
