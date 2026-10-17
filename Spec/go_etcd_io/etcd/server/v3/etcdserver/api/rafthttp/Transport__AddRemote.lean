/-
`(*rafthttp.Transport).AddRemote(id, urls)` (`transport.go`): names-only. Lean-first (no Rocq counterpart); the
server-construction unit, stage N0 (2026-10-16, D13: `notes/decisions.md`), for `NewServer`; an
axiom at the trust boundary since unit N4 (2026-10-17, D14e), why it is true of the Go code below.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvBoot

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **`t.AddRemote(id, us)`** on a live transport, the URLs parsing: it returns.

Why it is true of the Go code (`transport.go` at the etcd pin): `AddRemote` takes the transport's lock;
it returns early for a stopped transport or a known peer or remote; `types.NewURLs(us)` succeeds
(`peerURLsOk`: otherwise `Logger.Panic`); `startRemote` starts the remote's pipeline goroutines
(`transportEffectsOk`); it logs and returns. -/
abbrev rafthttp.Transport.AddRemote.spec : Prop :=
  ∀ (t : Loc) (id : w64) (us : GoSlice) (ss : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      ⌜transportEffectsOk⌝ ∗ transportLive t ∗ us ↦*□ ss ∗ ⌜membership.peerURLsOk ss⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"AddRemote")) (Val #id))
      (Val #us))
  {{ RET #(); transportLive t }}

end spec

end EtcdGrove
end Perennial
