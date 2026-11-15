/-
# grpc's `peer` package: the peers grpc records (assumed; verify round, A6 completeness F3)

A `peer.Peer` is a struct of three interfaces (`Addr`, `LocalAddr`: `net.Addr`; `AuthInfo`:
`credentials.AuthInfo`). grpc makes one per transport (the remote address always set) and hands out
a pointer to it (`peer.FromContext` of a run's context: `peerOk`), or copies it into a caller's
variable after a unary attempt (`grpc.Peer(&p)`, `*o.PeerAddr = *x`, `rpc_util.go:327-331`:
`peerVar`). The users print it: `peerInfo.Addr.String()` (`v3rpc/interceptor.go:106`), `p.String()`
(`client/v3/retry_interceptor.go:71`, `peer/peer.go:46-70`: each field's `String()`/`AuthType()`
when non-nil).

Vocabulary: `addrOk a` (persistent): `a` is `nil` or a `net.Addr` whose `String()` returns;
`authOk ai` (persistent): `ai` is `nil` or a `credentials.AuthInfo` whose `AuthType()` returns;
`peerFieldsOk v` (transparent): the three fields of a peer value are. `peerOk p` and `peerVar p` are
`Grpc/Api.lean`'s; their meaning is the laws here (`peerOk_fields`, `peerVar_inv`).

Why true: grpc's addresses are `*net.TCPAddr`/`*net.UnixAddr` (or a custom dialer's, which etcd's
client does not install on its own; Kubernetes' egress dialer returns `net.Conn`s whose addresses
are the dialed connection's), whose `String()` formats fields; its `AuthInfo`s are `TLSInfo`
(`AuthType()` returns `"tls"`), `insecure`'s, or `nil`.
-/
module

public import SpecPlan.Spec.google_golang_org.grpc.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Grpc

open Iris Iris.BI

/-- **`a` is `nil` or a `net.Addr` whose `String()` returns** (persistent). -/
opaque addrOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (a : GoInterface) : IProp GF := iprop(True)

/-- **`ai` is `nil` or a `credentials.AuthInfo` whose `AuthType()` returns** (persistent). -/
opaque authOk [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] (ai : GoInterface) : IProp GF := iprop(True)

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [go_gctx : GoGlobalContext] [sem : go.Semantics]

/-- The fields of a peer value print. -/
def peerFieldsOk (v : google_golang_org.grpc.peer.Peer) : IProp GF :=
  iprop(addrOk v.Addr' ∗ addrOk v.LocalAddr' ∗ authOk v.AuthInfo')

def peer_persistent.spec : Prop :=
  (∀ a, Persistent (addrOk (GF := GF) a)) ∧ (∀ ai, Persistent (authOk (GF := GF) ai))

/-- `nil` is (the zero peer's fields: `var p peer.Peer`). -/
def peer_nil.spec : Prop := ⊢ addrOk (GF := GF) GoInterface.nil ∗ authOk (GF := GF) GoInterface.nil

/-- **`a.String()`** of a non-`nil` address returns. -/
def addrOk_string.spec : Prop := ∀ (a : GoInterface),
  {{ addrOk (GF := GF) a ∗ ⌜a ≠ GoInterface.nil⌝ }}
    (App (Val (a @!! _root_.Perennial.net.Addr.ty @!! go!"String")) (Val #()))
  {{ (s : GoString), RET #s; True }}

/-- **`ai.AuthType()`** of a non-`nil` auth info returns. -/
def authOk_authType.spec : Prop := ∀ (ai : GoInterface),
  {{ authOk (GF := GF) ai ∗ ⌜ai ≠ GoInterface.nil⌝ }}
    (App (Val (ai @!! google_golang_org.grpc.credentials.AuthInfo.ty @!! go!"AuthType")) (Val #()))
  {{ (s : GoString), RET #s; True }}

/-- **A peer grpc made** (`peer.FromContext`'s, `peerOk`): read-only, its fields print, its remote
address set (`peerInfo.Addr.String()` of `logUnaryRequestStats`). -/
def peerOk_fields.spec : Prop := ∀ p : Loc,
  peerOk (GF := GF) p ⊢ ∃ v : google_golang_org.grpc.peer.Peer, p ↦□ v ∗ peerFieldsOk v ∗
    ⌜v.Addr' ≠ GoInterface.nil⌝

/-- **A peer variable lent to grpc** (`grpc.Peer(&p)`'s, `peerVar`): an invariant holds its fields,
each one that prints. Field by field, since grpc's copy `*o.PeerAddr = *x` stores them one at a time
and the caller's `p.String()` loads them one at a time (each load sees a field that prints, whatever
the interleaving). -/
def peerVar_inv.spec : Prop := ∀ p : Loc,
  peerVar (GF := GF) p ⊢ inv (nroot .@ "grpcPeer") iprop(∃ (a l ai : GoInterface),
    p.[google_golang_org.grpc.peer.Peer, go!"Addr"] ↦ a ∗ addrOk a ∗
    p.[google_golang_org.grpc.peer.Peer, go!"LocalAddr"] ↦ l ∗ addrOk l ∗
    p.[google_golang_org.grpc.peer.Peer, go!"AuthInfo"] ↦ ai ∗ authOk ai)

end laws

end Grpc
end EtcdGrove
end Perennial
