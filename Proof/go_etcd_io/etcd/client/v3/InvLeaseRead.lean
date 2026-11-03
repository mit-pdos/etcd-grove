/-
**The client's lease reads over gRPC** (the closed lease example, 2026-11-02;
`notes/lease-ex-plan.md`): the vocabulary of the `Lease` service's `LeaseTimeToLive` and
`LeaseLeases` as the client's `lessor.TimeToLive`/`Leases` (`client/v3/lease.go`) call them through
the retry lease client and the generated stub, as `InvLease.lean`'s for `LeaseGrant`/`LeaseRevoke`.
Lean-first (no Rocq counterpart).

**Messages** (`ProtoMsg` instances, trusted wire models as `InvLease.lean`'s):
- a `LeaseTimeToLiveRequest`'s model is its `(ID, Keys)`, held by the sender as the owned struct and
  by the server's decoded copy read-only as a whole (`LeaseServer.LeaseTimeToLive` takes
  `r ↦{dq} v`); a `LeaseLeasesRequest`'s is nothing (the server reads none of it);
- a `LeaseTimeToLiveResponse`'s model (`LeaseTTLRespM`) is its header, `ID`, `TTL` and
  `GrantedTTL`: the `Keys` slice the client copies is a field it reads (some slice), but its
  contents are not modelled (no spec states them: `issues/etcd-lease-timetolive-keys-toctou.md`);
- a `LeaseLeasesResponse`'s model (`LeaseLeasesRespM`) is its header and the IDs of its `Leases`,
  in order (each a `*LeaseStatus` the client reads the `ID` of).
Responses are held read-only by the server's response and the client's decoded reply alike.

**etcd's specs** (`etcdLeaseTTLSpec`, `etcdLeaseLeasesSpecAny`): a `LeaseTimeToLive` reply is about the
lease asked (`ID`: on the leader `v3_server.go`'s `ID: r.ID`, or the handler's own not-found reply;
on a follower the leader's reply, which `leasehttp.TimeToLiveHTTP` checks has the asked ID); a
`LeaseLeases` reply lists no lease twice (the lessor's map's keys, `leaseIdsAt`). What `Main` of
`examples/leasekv` checks.
-/
module

public import Proof.go_etcd_io.etcd.client.v3.InvLease

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.api.v3
open go_etcd_io.etcd.cache.v3 (statusErrOk)

/-! ## Messages -/

section model
variable [GooseExts]

/-- A `*pb.LeaseTimeToLiveResponse` as the wire carries it: its header, `ID`, `TTL`,
`GrantedTTL` (not its keys' contents). -/
structure LeaseTTLRespM where
  hdr : HdrM
  id : w64
  ttl : w64
  grantedTtl : w64

/-- A `*pb.LeaseLeasesResponse` as the wire carries it: its header and its leases' IDs. -/
structure LeaseLeasesRespM where
  hdr : HdrM
  ids : List w64

end model

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The `*pb.LeaseTimeToLiveResponse` `l` holds the message `m`** (read-only; its `Keys` some
slice). -/
def leaseTTLRespMsg (l : Loc) (m : LeaseTTLRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (ks : GoSlice),
    structFieldRef etcdserverpb.LeaseTimeToLiveResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.LeaseTimeToLiveResponse go!"ID" l ↦□ m.id ∗
    structFieldRef etcdserverpb.LeaseTimeToLiveResponse go!"TTL" l ↦□ m.ttl ∗
    structFieldRef etcdserverpb.LeaseTimeToLiveResponse go!"GrantedTTL" l ↦□ m.grantedTtl ∗
    structFieldRef etcdserverpb.LeaseTimeToLiveResponse go!"Keys" l ↦□ ks)

instance leaseTTLRespMsg_persistent (l : Loc) (m : LeaseTTLRespM) :
    Persistent (leaseTTLRespMsg (GF := GF) l m) := by
  unfold leaseTTLRespMsg; infer_instance

/-- **The `*pb.LeaseLeasesResponse` `l` holds the message `m`** (read-only): its `Leases` the
pointers `ps`, the `k`th a `*LeaseStatus` whose `ID` is `m.ids[k]`. -/
def leaseLeasesRespMsg (l : Loc) (m : LeaseLeasesRespM) : IProp GF :=
  iprop(⌜l ≠ null⌝ ∗ ∃ (h : Loc) (sl : GoSlice) (ps : List Loc),
    structFieldRef etcdserverpb.LeaseLeasesResponse go!"Header" l ↦□ h ∗ hdrFull h m.hdr ∗
    structFieldRef etcdserverpb.LeaseLeasesResponse go!"Leases" l ↦□ sl ∗ sl ↦*□ ps ∗
    ⌜ps.length = m.ids.length⌝ ∗
    [∗list] k ↦ p ∈ ps, ∃ id : w64, ⌜m.ids[k]? = some id⌝ ∗
      structFieldRef etcdserverpb.LeaseStatus go!"ID" p ↦□ id)

instance leaseLeasesRespMsg_persistent (l : Loc) (m : LeaseLeasesRespM) :
    Persistent (leaseLeasesRespMsg (GF := GF) l m) := by
  unfold leaseLeasesRespMsg; infer_instance

/-- **A `*pb.LeaseTimeToLiveRequest`** on the wire: its `(ID, Keys)`. The server's decoded copy is
read-only as a whole (`LeaseServer.LeaseTimeToLive` takes `r ↦{dq} v`; grant's `recv` is two
fields), which claims that protobuf's internal fields are not written after decoding either: true of
the server, where no `proto.Size` or `Marshal` reaches a lease request (the log interceptor sizes
only the KV requests, `v3rpc/interceptor.go:111-175`; a follower forwards a new request,
`leasehttp/http.go:229`). -/
def pbLeaseTimeToLiveRequest : ProtoMsg GF where
  ty := etcdserverpb.LeaseTimeToLiveRequest.ty
  M := w64 × Bool
  send inp m := iprop(∃ req : etcdserverpb.LeaseTimeToLiveRequest, inp ↦ req ∗
    ⌜m = (req.ID', req.Keys') ∧ req.unknownFields' = slice.nil⌝)
  wireLen _ := wireSlack
  recv r m := iprop(∃ v : etcdserverpb.LeaseTimeToLiveRequest, r ↦□ v ∗
    ⌜(v.ID', v.Keys') = m⌝)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseTimeToLiveRequest))
  own l := iprop(∃ v : etcdserverpb.LeaseTimeToLiveRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.LeaseTimeToLiveResponse`** on the wire (`leaseTTLRespMsg`). -/
def pbLeaseTimeToLiveResponse : ProtoMsg GF where
  ty := etcdserverpb.LeaseTimeToLiveResponse.ty
  M := LeaseTTLRespM
  send := leaseTTLRespMsg
  recv := leaseTTLRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseTimeToLiveResponse))
  own l := iprop(∃ v : etcdserverpb.LeaseTimeToLiveResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.LeaseLeasesRequest`** on the wire: nothing the server reads. -/
def pbLeaseLeasesRequest : ProtoMsg GF where
  ty := etcdserverpb.LeaseLeasesRequest.ty
  M := Unit
  send inp _ := iprop(∃ req : etcdserverpb.LeaseLeasesRequest, inp ↦ req ∗
    ⌜req.unknownFields' = slice.nil⌝)
  wireLen _ := wireSlack
  recv _ _ := iprop(True)
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseLeasesRequest))
  own l := iprop(∃ v : etcdserverpb.LeaseLeasesRequest, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **A `*pb.LeaseLeasesResponse`** on the wire (`leaseLeasesRespMsg`). -/
def pbLeaseLeasesResponse : ProtoMsg GF where
  ty := etcdserverpb.LeaseLeasesResponse.ty
  M := LeaseLeasesRespM
  send := leaseLeasesRespMsg
  recv := leaseLeasesRespMsg
  recv_persistent _ _ := inferInstance
  blank l := iprop(l ↦ (zero_val etcdserverpb.LeaseLeasesResponse))
  own l := iprop(∃ v : etcdserverpb.LeaseLeasesResponse, l ↦ v)
  blank_own l := by iintro H; iexists _; iexact H

/-- **What a unary `LeaseTimeToLive` call returns** to the client (as `leaseGrantCallOut`). -/
def leaseTTLCallOut (Q : LeaseTTLRespM → IProp GF) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseTTLRespM, leaseTTLRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err))

/-- **What a unary `LeaseLeases` call returns** to the client (as `leaseGrantCallOut`). -/
def leaseLeasesCallOut (Q : LeaseLeasesRespM → IProp GF) (resp : Loc) (err : GoInterface) :
    IProp GF :=
  iprop((⌜err = GoInterface.nil⌝ ∗ ∃ m : LeaseLeasesRespM, leaseLeasesRespMsg resp m ∗ Q m) ∨
    (⌜err ≠ GoInterface.nil ∧ clientErr err ∧ resp = null⌝ ∗ statusErrOk err))

/-! ## The lease options (`op.go`'s `LeaseOption`) -/

/-- **The `LeaseOption` `f` sets `attachedKeys` by `g`** (`WithAttachedKeys`: `fun _ => true`), as
`optSpec` for the KV's `OpOption`s: on a `*LeaseOp` it changes nothing else. -/
def leaseOptSpec (f : GoFunc) (g : Bool → Bool) : IProp GF :=
  iprop(□ ∀ (p : Loc) (op : go_etcd_io.etcd.client.v3.LeaseOp),
    {{ p ↦ op }} (App (Val #f) (Val #p))
    {{ RET #(); p ↦ { op with attachedKeys' := g op.attachedKeys' } }})

instance leaseOptSpec_persistent (f : GoFunc) (g : Bool → Bool) :
    Persistent (leaseOptSpec (GF := GF) f g) := by
  unfold leaseOptSpec; infer_instance

/-- **The options' slice `sl`** (read-only), the `i`th meeting `leaseOptSpec` at `gs[i]` (as
`optsAt`). -/
def leaseOptsAt (sl : GoSlice) (gs : List (Bool → Bool)) : IProp GF :=
  iprop(∃ fs : List GoFunc, sl ↦*□ fs ∗ ⌜fs.length = gs.length⌝ ∗
    □ ∀ (i : Nat) (f : GoFunc) (g : Bool → Bool), ⌜fs[i]? = some f⌝ -∗ ⌜gs[i]? = some g⌝ -∗
      leaseOptSpec f g)

instance leaseOptsAt_persistent (sl : GoSlice) (gs : List (Bool → Bool)) :
    Persistent (leaseOptsAt (GF := GF) sl gs) := by
  unfold leaseOptsAt; infer_instance

end defs

/-- The `attachedKeys` the options `gs` leave, from `b`: in order (`applyOpts`). -/
def leaseKeysFold (gs : List (Bool → Bool)) (b : Bool) : Bool := gs.foldl (fun b g => g b) b

/-! ## etcd's specs of the `Lease` service's reads -/

section specs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **etcd's spec of `LeaseTimeToLive`** (see the file header): the reply is about the lease the
request asks about. The weakest spec `leasekv` needs: nothing of the header, `TTL` or `GrantedTTL`
(the server's answer, `v3rpc.leaseTTLOut`, gives more; a stronger spec of the method can be
registered beside it). -/
def etcdLeaseTTLSpec : GrpcSpec (GF := GF) pbLeaseTimeToLiveRequest pbLeaseTimeToLiveResponse :=
  fun (req : w64 × Bool) (Φ : LeaseTTLRespM → IProp GF) =>
    iprop(∀ m : LeaseTTLRespM, ⌜m.id = req.1⌝ -∗ Φ m)

/-- **etcd's old spec of `LeaseLeases`**: the reply lists no lease twice. Since the lease-grant
review's S6 (2026-11-02) a corollary of the contract `etcdLeaseLeasesSpec`
(`client/v3/InvLeaseGrant.lean`, which also lists the caller's grants: `isGrpcRpc_leaseLeases_any`);
kept for its callers. The weakest spec `leasekv`
needs: nothing of which leases (the server's answer, `v3rpc.leaseLeasesOut`, gives the lessor's at an
index of its history). -/
def etcdLeaseLeasesSpecAny : GrpcSpec (GF := GF) pbLeaseLeasesRequest pbLeaseLeasesResponse :=
  fun (_ : Unit) (Φ : LeaseLeasesRespM → IProp GF) =>
    iprop(∀ m : LeaseLeasesRespM, ⌜m.ids.Nodup⌝ -∗ Φ m)

end specs

end EtcdGrove
end Perennial
