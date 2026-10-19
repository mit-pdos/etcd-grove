/-
`http.Serve(l, handler)` (names only), serving a member's raft handler. Lean-first (no Rocq
counterpart); D21 stage M5 (2026-10-19, the user's (A)): an axiom at the trust boundary, why it is
true of the Go code below. The vocabulary: `Proof/net/InvNet.lean` (the listener),
`Proof/go_etcd_io/etcd/server/v3/etcdserver/InvRaftHandler.lean` (the handler).
-/
module

public import Proof.net.InvNet
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRaftHandler

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

/-- **`http.Serve(l, h)`** on a listener bound at `a` (`netListenerAt`, consumed: what
`net.Listen` gave) with a raft handler of member `id`'s transport in `γn` (`raftHandlerOf`,
`EtcdServer.RaftHandler`'s), where `http://a` is one of member `id`'s peer URLs (`γn.dir id`):
returns an error if it returns.

What the axiom asserts of the Go code (`net/http`'s `Serve`, `rafthttp`'s handlers, at the pins):
`Serve` accepts connections on `l` and serves each request with `h` on its own goroutine, until
`Accept` fails (then it returns the error); it panics on nothing a client sends (a handler's panic
is recovered per connection, rafthttp's pipeline handler panics only on a non-HTTP error of
`Process`, which the server's `Process` never returns). This is where D21b's deployment fact is
stated: the address `a`, the program's alone (`netAddrFree`, consumed by `net.Listen`), is served
by the transport holding `id`'s slot, so a message `Send` posts to `http://a` (a URL of
`γn.dir id`, where `AddPeer`/`AddRemote` put `id`'s peer) reaches `id`'s `Raft`, never another
member's -- the condition under which `rafthttp.Transport.Start`'s axiom holds
(`issues/etcd-rafthttp-misaddressed-403-member-removed.md`: a raft handler of another member at
`id`'s URL would answer `403`, read as `errMemberRemoved`). What the handler then does is
`Transport.Start`'s axiom's (`Process` with messages of the network for `id`, at most
`netProcSlots` calls at once). -/
abbrev net.http.Serve.spec : Prop :=
  ∀ (l h : GoInterface) (a : GoString) (γn : NetNames GF) (id : w64),
  {{ netListenerAt (GF := GF) l a ∗ raftHandlerOf γn id h ∗
      ⌜go!"http://" ++ a ∈ γn.dir id⌝ }}
    (App (App (Val (@! _root_.Perennial.net.http.Serve)) (Val #l)) (Val #h))
  {{ (err : GoInterface), RET #err; True }}

end spec

end EtcdGrove
end Perennial
