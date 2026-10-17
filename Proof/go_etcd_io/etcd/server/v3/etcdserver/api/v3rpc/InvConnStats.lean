/-
**The connection stats handler** (`connstats.go`, pr-verify etcd#21621): what the specs of
`connStatsHandler.HandleConn` and `RecordClientCertExpiration` share. Lean-first (no Rocq
counterpart).

**The histogram** (`certExpHist P Q`, persistent): the package variable
`clientCertExpirationSecs` holds a fixed histogram whose `Observe(x)` takes `P` to `Q x`. `P` and `Q`
are the caller's: with a token `P` that only `Observe` consumes, a spec that returns `P` shows that
nothing was observed, and one that returns `Q x` that exactly one value was. (The histogram's
`Observe` is prometheus', names only: the variable's contract is an assumption about package
initialization, as `v3rpcInit`'s and `watchVars`' metrics.)

**What the handler reads of the connection** (`connTLSOk o oti`, persistent): if the context's peer
`o` has a `credentials.TLSInfo` as its `AuthInfo`, it is `oti = some ti`, and the TLS state's `PeerCertificates` slice (read-only),
and, if there is one, the leaf certificate's `NotAfter` (read-only: grpc's TLS handshake builds the
state once, and `x509.Certificate` is names only: the field is a points-to at its address). An
interface value whose dynamic type is `TLSInfo` holds a `TLSInfo` (`ii.v = #ti`). (`oti` is the
spec's argument, not read off the value: `intoVal` is not known injective at struct types.)

**The event** (`connEventOk s`): a `*stats.ConnBegin` in the interface is a pointer.

**When it records** (`connRecords s hs o oti`): the event is a `*stats.ConnBegin`, the context carries
a peer whose `AuthInfo` is a `TLSInfo`, the handler's `clientAuth` is not `tls.NoClientCert`, and
the peer sent at least one certificate.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Base
public import Proof.google_golang_org.grpc.peer.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI google_golang_org.grpc

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The histogram `clientCertExpirationSecs`, whose `Observe(x)` takes `P` to `Q x`. -/
def certExpHist (P : IProp GF) (Q : w64 → IProp GF) : IProp GF :=
  iprop(∃ h : GoInterfaceOk,
    globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.clientCertExpirationSecs ↦□
      GoInterface.ok h ∗
    □ (∀ x : w64, {{ P }} (App (Val #(methods h.ty go!"Observe" h.v)) (Val #x))
      {{ RET #(); Q x }}))

instance certExpHist_persistent (P : IProp GF) (Q : w64 → IProp GF) :
    Persistent (certExpHist P Q) := by
  unfold certExpHist; infer_instance

/-- The leaf certificate's `NotAfter`, read-only, if there is a certificate. -/
def leafOk : List Loc → IProp GF
  | [] => iprop(True)
  | c :: _ => iprop(∃ na : time.Time, structFieldRef crypto.x509.Certificate go!"NotAfter" c ↦□ na)

instance leafOk_persistent (certs : List Loc) : Persistent (leafOk (GF := GF) certs) := by
  cases certs <;> (unfold leafOk; infer_instance)

/-- The TLS state's certificates, read-only, and the leaf's `NotAfter`. -/
def tlsCertsOk (ti : credentials.TLSInfo) : IProp GF :=
  iprop(∃ certs : List Loc, ti.State'.PeerCertificates' ↦*□ certs ∗ leafOk certs)

instance tlsCertsOk_persistent (ti : credentials.TLSInfo) :
    Persistent (tlsCertsOk (GF := GF) ti) := by
  unfold tlsCertsOk; infer_instance

/-- The context's peer, and the TLS state `oti` if its `AuthInfo` is a `TLSInfo` (an interface
value of dynamic type `TLSInfo` holds the `TLSInfo` `ti`, `oti = some ti`). -/
def connTLSOk : Option (Loc × peer.Peer) → Option credentials.TLSInfo → IProp GF
  | none, _ => iprop(True)
  | some (_, pr), oti => iprop(∀ ii : GoInterfaceOk, ⌜pr.AuthInfo' = GoInterface.ok ii⌝ -∗
      ⌜ii.ty = credentials.TLSInfo.ty⌝ -∗
      ∃ ti : credentials.TLSInfo, ⌜oti = some ti ∧ ii.v = #ti⌝ ∗ tlsCertsOk ti)

instance connTLSOk_persistent (o : Option (Loc × peer.Peer)) (oti : Option credentials.TLSInfo) :
    Persistent (connTLSOk (GF := GF) o oti) := by
  cases o with
  | none => unfold connTLSOk; infer_instance
  | some x => obtain ⟨p, pr⟩ := x; unfold connTLSOk; infer_instance

end defs

section pure
variable [ext : FfiSyntax] [go_gctx : GoGlobalContext]

/-- The event `s` is well formed: a `*stats.ConnBegin` in it is a pointer (an interface value holds
a value of its dynamic type). -/
def connEventOk (s : GoInterface) : Prop :=
  ∀ ii : GoInterfaceOk, s = GoInterface.ok ii →
    ii.ty = go.GoType.PointerType stats.ConnBegin.ty → ∃ l : Loc, ii.v = #l

/-- **When `HandleConn` records** an observation (see the file header). -/
def connRecords (s : GoInterface) (hs : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.connStatsHandler)
    (o : Option (Loc × peer.Peer)) (oti : Option credentials.TLSInfo) : Prop :=
  (∃ l : Loc, s = GoInterface.ok ⟨go.GoType.PointerType stats.ConnBegin.ty, #l⟩) ∧
  ∃ (p : Loc) (pr : peer.Peer), o = some (p, pr) ∧
    (∃ v : val, pr.AuthInfo' = GoInterface.ok ⟨credentials.TLSInfo.ty, v⟩) ∧
    hs.clientAuth' ≠ W64 0 ∧
    ∃ ti : credentials.TLSInfo, oti = some ti ∧ 0 < sint.Z ti.State'.PeerCertificates'.len

end pure

end v3rpc
end EtcdGrove
end Perennial
