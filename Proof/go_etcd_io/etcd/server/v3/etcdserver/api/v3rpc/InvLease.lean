/-
**The lease keep-alive stream's server end** (`lease.go`'s `LeaseKeepAlive`/`leaseKeepAlive`;
etcd-io/etcd#21960, 2026-10-17): the message models of the stream, the lessor's contract, the
lease server's predicate and the handler's stream specification. Lean-first (no Rocq
counterpart); the stream is grpc's generic server end (`srvStreamIs`,
`google_golang_org/grpc/InvGrpcStream.lean`), as the watch service's.

**The messages** (`pbLeaseKeepAliveRequest`, `pbLeaseKeepAliveResponse`, trusted wire models as
the watch service's): a request's model is its lease id (the only field the server reads); a
response's (`LKRespM`) its lease id, its TTL and its header's cluster and member ids (the header's
other fields, the raft term, the leader and the revision, are the server's advisory view: some
values).

**The lessor** (`lessorOk le Ren`, persistent; a premise of the handler's spec, not an axiom):
the server's `Lessor` interface value `le`, whose `LeaseRenew(ctx, id)` returns a TTL with no
error, in the relation `Ren id ttl` (what the lessor promises of a renewal; the handler's
specification is over any `Ren`), or an error `togRPCError` and `errors.Is` can take
(`srvErrIs`: `lease.ErrLeaseNotFound` is one).

**The lease server** (`isLeaseServer p S`, persistent): `NewLeaseServer`'s `*LeaseServer`, its
logger, its lessor (`lessorOk`), its header (`hdrIs`, the KV server's: `newHeader(s)`), and the
package facts `lease.go` reads (`leaseVars`: `io.EOF`, the counter vector `streamFailures`,
`lease.ErrLeaseNotFound` a pointer leaf), assumptions about package initialization as the watch
service's `watchVars`.

**The stream specification** (`lkDn`, `lkStreamSpec`): the `j`th response the handler sends
answers the `j`th request the client sent (`upAt`): its lease id is the request's, its header's
ids are the server's, its TTL is `0` (the lease was not found) or a renewal's (`Ren`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.InvWatch

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.api.v3 go_etcd_io.etcd.server.v3.etcdserver
open go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc (LeaseServer)

/-- **A `*pb.LeaseKeepAliveResponse`** as the wire carries it: the lease id, the TTL, the
header's cluster and member ids. -/
structure LKRespM where
  id : w64
  ttl : w64
  cid : w64
  mid : w64

instance LKRespM.countable : Pos.Countable LKRespM :=
  .ofInjective (fun m => Pos.Countable.encode (m.id, m.ttl, m.cid, m.mid))
    (fun a b h => by
      have := Pos.encode_inj h
      cases a; cases b; simp_all)

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **A decoded `*pb.LeaseKeepAliveRequest`** at `l` with the lease id `id`, owned by the
server (its `ID` field; the rest is not read). -/
def lkReqRecv (l : Loc) (id : w64) : IProp GF :=
  iprop(structFieldRef etcdserverpb.LeaseKeepAliveRequest go!"ID" l ↦ id)

/-- **A `*pb.LeaseKeepAliveRequest` the client sends** at `l` with the lease id `id`
(read-only). -/
def lkReqSend (l : Loc) (id : w64) : IProp GF :=
  iprop(structFieldRef etcdserverpb.LeaseKeepAliveRequest go!"ID" l ↦□ id)

/-- **A `*pb.LeaseKeepAliveResponse`** at `l` holding `m`, owned (the server's message, and the
client's decoded copy): its id, TTL and header (the header's ids `m.cid`, `m.mid`, some term,
leader and revision). -/
def lkResp (l : Loc) (m : LKRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (r : w64),
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"ID" l ↦ m.id ∗
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"TTL" l ↦ m.ttl ∗
    structFieldRef etcdserverpb.LeaseKeepAliveResponse go!"Header" l ↦ h ∗
    hdrFilled h m.cid m.mid ∗ structFieldRef etcdserverpb.ResponseHeader go!"Revision" h ↦ r)

/-- **The keep-alive requests on the wire** (a trusted wire model, as the watch requests'). -/
abbrev pbLeaseKeepAliveRequest : StreamMsg GF where
  ty := etcdserverpb.LeaseKeepAliveRequest.ty
  M := w64
  cnt := inferInstance
  send := lkReqSend
  recv := lkReqRecv
  own l := iprop(∃ v : etcdserverpb.LeaseKeepAliveRequest, l ↦ v)

/-- **The keep-alive responses on the wire** (a trusted wire model). -/
abbrev pbLeaseKeepAliveResponse : StreamMsg GF where
  ty := etcdserverpb.LeaseKeepAliveResponse.ty
  M := LKRespM
  cnt := inferInstance
  send := lkResp
  recv := lkResp
  own l := iprop(∃ v : etcdserverpb.LeaseKeepAliveResponse, l ↦ v)

/-- **The lessor `le`** (persistent): `LeaseRenew(ctx, id)` returns a TTL in the relation
`Ren id`, or an error the handler can pass to `errors.Is` and `togRPCError`. -/
def lessorOk (le : GoInterface) (Ren : w64 → w64 → Prop) : IProp GF :=
  iprop(∃ li : GoInterfaceOk, ⌜le = GoInterface.ok li⌝ ∗
    □ ∀ (ctx : GoInterface) (id : w64),
      {{ True }}
        (App (App (Val #(methods li.ty go!"LeaseRenew" li.v)) (Val #ctx)) (Val #id))
      {{ (ttl : w64) (err : GoInterface), RET (PairV #ttl #err);
          (⌜err = GoInterface.nil ∧ Ren id ttl⌝) ∨ srvErrIs err }})

instance lessorOk_persistent (le : GoInterface) (Ren : w64 → w64 → Prop) :
    Persistent (lessorOk (GF := GF) le Ren) := by
  unfold lessorOk; infer_instance

/-- **The package facts `lease.go` reads** (persistent): `io.EOF`, the counter vector
`streamFailures`, `lease.ErrLeaseNotFound` (an `errors.New` error). -/
def leaseVars : IProp GF :=
  iprop(eofVar ∗
    (∃ cv : Loc, globalAddr go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.streamFailures ↦□ cv) ∗
    errVarLeaf (hlc := HasLC.hasLC) go_etcd_io.etcd.server.v3.lease.ErrLeaseNotFound)

instance leaseVars_persistent : Persistent (leaseVars (GF := GF)) := by
  unfold leaseVars; infer_instance

/-- **The lease server's values**: the server and its KV answers (the header's `rev()`), the
cluster and member ids, the logger, the lessor and its renewal relation. -/
structure LSrv (GF : BundledGFunctors) where
  s : Loc
  A : KVAns GF
  cid : w64
  mid : w64
  lg : Loc
  le : GoInterface
  Ren : w64 → w64 → Prop

/-- **The `*LeaseServer` `p`** (persistent): its fields, the lessor's contract, the package
facts. -/
def isLeaseServer (p : Loc) (S : LSrv GF) : IProp GF :=
  iprop(⌜p ≠ null ∧ S.lg ≠ null⌝ ∗
    structFieldRef LeaseServer go!"lg" p ↦□ S.lg ∗
    structFieldRef LeaseServer go!"le" p ↦□ S.le ∗
    hdrIs (structFieldRef LeaseServer go!"hdr" p) S.s S.A S.cid S.mid ∗
    lessorOk S.le S.Ren ∗ leaseVars)

instance isLeaseServer_persistent (p : Loc) (S : LSrv GF) : Persistent (isLeaseServer p S) := by
  unfold isLeaseServer; infer_instance

/-- **What the handler says of the `j`th response `m`** (persistent): it answers the `j`th
request (`upAt`, the lease id `id`): its id is `id`, its header's ids the server's, its TTL `0`
(not found) or a renewal's. -/
def lkDn (γ : StreamNames) (S : LSrv GF) (j : Nat) (m : LKRespM) : IProp GF :=
  iprop(∃ id : w64, upAt (Req := pbLeaseKeepAliveRequest) γ j id ∗
    ⌜m.id = id ∧ m.cid = S.cid ∧ m.mid = S.mid ∧ (m.ttl = W64 0 ∨ S.Ren id m.ttl)⌝)

instance lkDn_persistent (γ : StreamNames) (S : LSrv GF) (j : Nat) (m : LKRespM) :
    Persistent (lkDn γ S j m) := by
  unfold lkDn upAt; infer_instance

/-- **The stream's specification** (persistent): what the handler says of a response is the
stream's content `Dn` of it. -/
def lkStreamSpec (γ : StreamNames) (S : LSrv GF) (Dn : Nat → LKRespM → IProp GF) : IProp GF :=
  iprop(□ ∀ (j : Nat) (m : LKRespM), lkDn γ S j m -∗ Dn j m)

instance lkStreamSpec_persistent (γ : StreamNames) (S : LSrv GF) (Dn : Nat → LKRespM → IProp GF) :
    Persistent (lkStreamSpec γ S Dn) := by
  unfold lkStreamSpec; infer_instance

/-- **The handler's end state** of the stream: the receiver's and the sender's tokens, back with
the handler (it no longer uses the stream: no receive or send of it runs after the return), the
header's resources. (Nothing is said of the result: whether a `nil` return answered every
request received would need `errors.Is(nil, io.EOF)` to be `false`, which Perennial's
`errors.Is.spec` does not say: its result is some boolean.) -/
def lkDone (γ : StreamNames) (S : LSrv GF) : IProp GF :=
  iprop(∃ (Lq : List w64) (Lr : List LKRespM),
    srvRecvTok (Req := pbLeaseKeepAliveRequest) γ Lq ∗
    srvSendTok (Rep := pbLeaseKeepAliveResponse) γ Lr ∗ S.A.revR)

/-- The receiver's token knows the request at each position it received. -/
theorem srvRecvTok_upAtLK (γ : StreamNames) (L : List w64) (m : w64) :
    srvRecvTok (GF := GF) (Req := pbLeaseKeepAliveRequest) γ (L ++ [m]) ⊢
      srvRecvTok (Req := pbLeaseKeepAliveRequest) γ (L ++ [m]) ∗
        upAt (Req := pbLeaseKeepAliveRequest) γ L.length m := by
  unfold srvRecvTok upAt monoListIdxOwn
  iintro ⟨H1, #H2⟩
  iframe H1 H2
  ipureintro
  simp

end defs

end v3rpc
end EtcdGrove
end Perennial
