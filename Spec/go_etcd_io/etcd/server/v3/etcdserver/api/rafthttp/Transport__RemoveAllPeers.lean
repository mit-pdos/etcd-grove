/-
`(*rafthttp.Transport).RemoveAllPeers()` (`transport.go`): names-only. Lean-first (no Rocq
counterpart); D22 receiver epochs, S8c (2026-10-24), for `applySnapshot`'s transport reset; an
axiom at the trust boundary, why it is true of the Go code below.
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

/-- **`t.RemoveAllPeers()`** on a started transport: it returns.

Why it is true of the Go code (`transport.go:333-339` and `removePeer`, `:342-356`, at the etcd
pin): under the transport's lock it removes every peer (`peer.stop()`: the peer's goroutines and
streams stopped, its pending messages dropped; the probers' entries removed; the leader stats'
follower deleted, without the stats' lock: a data race with the v2 stats endpoint, outside the
model, `issues/etcd-rafthttp-leaderstats-followers-race.md`); on a stopped transport the map is nil and nothing happens, so no panic and no
token is needed. Its effect on the network contract (`netTransport`) is only that later `Send`s to
a removed id find no peer and drop the message (`Send`'s post promises nothing of delivery), until
`AddPeer` adds it back; the started transport's facts stay true. -/
abbrev rafthttp.Transport.RemoveAllPeers.spec : Prop :=
  ∀ (γn : NetNames GF) (t : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗
      transportStarted γn t }}
    (App (Val (t @!! go.GoType.PointerType
      go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"RemoveAllPeers"))
      (Val #()))
  {{ RET #(); True }}

end spec

end EtcdGrove
end Perennial
