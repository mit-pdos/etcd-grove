/-
`(*EtcdServer).GoAttach(f)` (`server.go`), translated with its body (the request path's unit 4c,
2026-10-13; names-only, an axiom, until then). Lean-first (no Rocq counterpart); see
`InvGoAttach.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvGoAttach

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3 go_etcd_io.etcd.pkg.v3 go_uber_org

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- `s.GoAttach(f)`, by a goroutine with a reader slot of `wgMu` and its thread token
(`srvGoRes`) and the logger's reader slot (`Logger()` in the stopped case), of a closure `f` with
`P` (`{P} f() {True}`): if `stopping` is closed, nothing (`P` dropped: `f` never runs); else `f`
runs in a goroutine counted by `s.wg`. The caller gets its slots and thread token back. -/
abbrev EtcdServer.GoAttach.spec : Prop :=
  ∀ (s : Loc) (f : GoFunc) (P : IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
      srvGoRes s ∗ srvLgReader s ∗ P ∗
      {{ P }} (App (Val #f) (Val #())) {{ RET #(); True }} }}
    (App (Val (s @!! go.GoType.PointerType EtcdServer.ty @!! go!"GoAttach")) (Val #f))
  {{ RET #(); srvGoRes s ∗ srvLgReader s }}

end spec

end EtcdGrove
end Perennial
