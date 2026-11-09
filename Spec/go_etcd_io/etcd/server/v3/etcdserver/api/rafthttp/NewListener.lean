/-
## `NewListener(u, tlsinfo)`

**Users.** embed's peer listeners (`embed/etcd.go:578`, through `transport.NewListenerWithOpts` directly; this one is rafthttp's exported helper).

**Proof sketch.** Assumed: `net.Listen` on the host binds it or fails; TLS wraps the listener (a TLS error is an error).

**Changes.** New (no old spec).

**Margin.** None.
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

/-- (trust boundary: untranslated; `transport.NewListenerWithOpts` over `net.Listen`) **A listener bound at `u`'s host**, or an error. -/
def NewListener.spec : Prop :=
  ∀ (u : _root_.Perennial.net.url.URL) (tls : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp ∗ True }}
    (App (App (Val (@! go_etcd_io.etcd.server.v3.etcdserver.api.rafthttp.NewListener)) (Val #u)) (Val #tls))
  {{ (l : GoInterface) (err : GoInterface), RET (PairV #l #err); (⌜err ≠ interface.nil⌝ ∗ Http.errOk err) ∨ (⌜err = interface.nil⌝ ∗ Http.listenerAt l u.Host') }}

end spec
end Rafthttp
end EtcdGrove
end Perennial
