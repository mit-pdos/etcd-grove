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
(their calls into the server: `Start`'s axiom); it logs and returns. It only reads `us` (the parsed `types.URLs` are
fresh), so the caller's share comes back. (D21 M2, 2026-10-19) The URLs are member `id`'s in the
network's directory (`γn.dir id`): what makes `Send`'s messages for `id` reach the transport holding
`id`'s slot (D21b's deployment fact; until then the opaque `transportEffectsOk`). (The partition
plan's S1, 2026-10-20) `id` joins the live transport's list of remotes (`transportLive γn t rs`),
whether or not `t.remotes` gets the key (not for a known peer or remote: the list over-approximates). -/
abbrev rafthttp.Transport.AddRemote.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc) (id : w64) (us : GoSlice) (dq : DFrac) (ss : List GoString)
    (rs : List w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      transportLive γn t rs ∗ us ↦*{dq} ss ∗ ⌜membership.peerURLsOk ss ∧ γn.dir id = ss⌝ }}
    (App (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"AddRemote")) (Val #id))
      (Val #us))
  {{ RET #(); transportLive γn t (rs ++ [id]) ∗ us ↦*{dq} ss }}

end spec

end EtcdGrove
end Perennial
