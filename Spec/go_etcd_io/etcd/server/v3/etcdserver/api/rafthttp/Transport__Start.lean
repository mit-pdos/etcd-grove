/-
## `(*Transport).Start()`

**Users.** etcd's `NewServer` (`server/etcdserver/server.go:412-426`: the literal with the member's id, peer URLs, cluster id, the server as `Raft`, its snapshotter, stats and `errorc`; an error is returned to the caller). Snippet: `transport.go` (`ReqStartTransport`).

**Proof sketch.** `newStreamRoundTripper`, `NewRoundTripper` (their trust-boundary specs: an error, or `Http.roundTripperOk`); on an error the struct is left (its fields partly set) and the configuration dropped. Then the maps, `probing.NewProber` (twice: `proberAt`), the default `DialRetryFrequency`; allocate the transport's `RWMutex` invariant (the fields read-only from now on, the maps empty, the provers; the `Raft`'s `raftOk`, the stats, the error channel, the local URLs' peer addresses, kept persistent in `isTransport`) and the `trRunning` token whole.

**Changes.** Was an axiom until rafthttp stage 6d, then proved over `TransportState.lean`; restated: the network contract (`netTransport`, `netSlot`, `netHttpOk`, the snapshot directory invariant, the reader-token pool, `raftPool`, the remote ids `L`) is gone from the statement. The receiver's `Raft` contract is `raftOk` (each `Process` on its caller's thread token, not a pool of `R`s); the snapshot directory is the snapshotter's (`dbSaved`); the reader tokens of the lock are the callers' `threadTok`s.

**Margin.** The post says nothing about the error's cause; the struct after an error is not given back as a usable transport.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Api

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Rafthttp

open Iris Iris.BI Raft
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- **Starts the transport** `t` (a `Transport` literal the caller owns, with `trCfg`'s fields) for member `tv.ID` of network `ν`: an error (the round trippers' TLS configuration refused), or the transport started, with no peer yet. -/
def Transport.Start.spec : Prop :=
  ∀ (t : Loc) (tv : go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport) (ν : Net),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ t ↦ tv ∗ trCfg tv ν }}
    (App (Val (t @!! go.GoType.PointerType go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.Transport.ty @!! go!"Start")) (Val #()))
  {{ (err : GoInterface), RET #err; (⌜err ≠ interface.nil⌝ ∗ Http.errOk err) ∨ (⌜err = interface.nil⌝ ∗ isTransport t ν tv.ID' ∗ trRunning t 1) }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
