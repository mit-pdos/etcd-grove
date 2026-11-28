/- Lean-first (no Rocq counterpart).

# Interim cross-machine vocabulary for etcd's distributed theorems (until #24's S2 switch)

`notes/putget-dist-plan.md` §12, `notes/etcd-dist-plan.md` §18. The cluster's view (`DistView`, O1 option
B: a Lean value the start fixes; no publication) and the address fact over it, since phase 7 S2's interface
switch (2026-11-24) #24's own `grpcAddrAt a (etcdSvc Γ mid)`. The table `etcdSvc` is defined (stage B′,
2026-11-28): with auth off, etcd's KV methods at the view's specs, flagged as never refusing; every other
entry is `etcdSvcRest`'s (see their docstrings).

One axiom (`etcdSvcRest`; the start law `etcdAddr_set` is a theorem); the server side's axiom is
`ServeDist.lean`. Every other declaration is a definition or a proved law.
-/
module

public import GooseLang.Ext.Net.Proto
public import Proof.google_golang_org.grpc.InvGrpcWire
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest
public import Proof.go_etcd_io.etcd.client.v3.KVServiceV

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI Iris.ProofMode Net

/-! ## The view (O1, option B: `notes/etcd-dist-plan.md` §18.3) -/

/-- **What a client's statements read of the cluster** (O1, option B, `notes/etcd-dist-plan.md` §18.3): a
Lean value the deployment's start chooses before any machine runs, never stored in ghost state, so no
member publishes anything and nothing about it changes across a restart.

* `kv`: the cluster's KV names (`ClusterNames.γk`, `clusterAllocN`'s). Every incarnation of every member
  has KV names `kvCongr` to them (a first start's by `memberBoot_of_slice`, a restart's by
  `restartNames`), and `Serve_dist` serves the table at `Γ` only for such a member.
* `ls mid`: member `mid`'s lessor history name. `Serve_dist` serves the table at `Γ` only for a member whose
  lessor is at `Γ.ls mid` (`memberUpL`/`memberUpOnL`, F7 step 3, 2026-11-26: `NewServer_dist` takes the name from
  the start, P-L1); the lease contracts read it. The starts that allocate no lessor slot set it to a constant
  (`ClusterNames.lsNone`).
* `auth`: the cluster's auth mode. `etcdSvc` has etcd's KV entries (never refusing: a write is sent at
  most once) for `auth = false` only (interim, until nomode N4); `Serve_dist` serves a member whose auth mode
  is the view's (`memberUpL` with auth off, `memberUpOnL` with auth on).
* `au mid`: member `mid`'s auth names (F7, 2026-11-26, the approved design's P-A1, `notes/etcd-dist-f7.md`).
  No axiom reads it yet: the auth-on drafts (`AuthViewDist.lean`) read it, sound because `Serve_dist` requires
  the member's auth store at `Γ.au mid` with auth on (`memberUpOnL`, F7 step 3, 2026-11-26; the review
  `notes/axiom-review/f7-a.md`); the starts without auth names set it to a constant (`ofKV`, `auNone`). -/
structure DistView [GooseExts] where
  kv : KVNames
  ls : w64 → GName
  auth : Bool
  au : w64 → EtcdGrove.auth.AuthNames

/-- **The auth-off view at the KV names `γk`**, its lessor names a constant until P-L1 and its auth names a
constant until P-A1's start (no contract reads either yet): a start's view (`ClusterNames.view`). -/
def DistView.ofKV [GooseExts] (γk : KVNames) : DistView :=
  ⟨γk, fun _ => 0, false, fun _ => ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩⟩

/-! ## The address fact (over phase 7 S2's interface; the table: `etcdSvc`) -/

/-- **The entries of etcd's table that no law describes** (interim, axiomatized; heap-free, the same on
every machine). `etcdSvc` takes every entry from it but auth-off KV methods: etcd's other unary methods
(Lease, Auth, Cluster, Maintenance, ...), its streams (Watch, LeaseKeepAlive), and with auth on its KV
methods. It has no law: no proof learns an entry of it, so nothing calls such a method through grpc's
`Invoke` (`isGrpcRpcMd` needs the entry) or opens such a stream, and a server serves it through
`Server.Serve` only by registering no method under its names (`grpcServes`: every call there gets
`Unimplemented`). The cross-machine axioms of those methods (`Lease_*_dist`, `Watch_dist`, `Auth_*_dist`,
the `*On_dist` KV ones) are their contracts; `Serve_dist` is the only server of these entries. A table is
data, so the axiom is consistent (`GrpcSvc` is inhabited). Retired entry by entry as each method's view
spec is written (`notes/etcdsvc-b.md`). -/
axiom etcdSvcRest [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    {GF : BundledGFunctors} [GooseGlobalGS .hasLC GF]
    (Γ : DistView) (mid : w64) : GrpcSvc GF

section table
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF]

/-- **etcd's KV methods at the KV names `γk`** (heap-free): `Put`, `Range`, `DeleteRange`, `Txn` and
`Compact` at their messages' wire parts and the view specs `client.etcdPutSpecV γk`, ... (the specs
naming no member, which the client's `isKv` registers), each flagged as never refusing (`nr`); no other
method. -/
def etcdKvSvc (γk : KVNames) : GrpcSvc GF := fun name =>
  if name = go!"/etcdserverpb.KV/Put" then
    some (.unary ⟨client.putReqWire, client.putRespWire, client.etcdPutSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/Range" then
    some (.unary ⟨client.rangeReqWire, client.rangeRespWire, client.etcdRangeSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/DeleteRange" then
    some (.unary ⟨client.delReqWire, client.delRespWire, client.etcdDeleteSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/Txn" then
    some (.unary ⟨client.txnReqWire, client.txnRespWire, client.etcdTxnSpecV γk, true⟩)
  else if name = go!"/etcdserverpb.KV/Compact" then
    some (.unary ⟨client.compactReqWire, client.compactRespWire, client.etcdCompactSpecV γk, true⟩)
  else none

/-- **etcd's service table for the member `mid` of the cluster view `Γ`** (heap-free: every machine
holds the same table). With auth off (`Γ.auth = false`), etcd's KV methods are `etcdKvSvc Γ.kv`'s: the
view specs at the cluster's KV names, flagged as never refusing. Every other entry is
`etcdSvcRest Γ mid`'s (no law).

What serving it claims (`Serve_dist`, `grpcServesEnt`): an auth-off member's KV handlers, through its
interceptors, meet the view specs (its in-process specs at names `kvCongr` to `Γ.kv`, `etcdPutSpecV_M`,
...) and never return a refusal (`grpcRunNRMd`): with auth off no auth refusal occurs, and the member is
a voter for its whole life (`ServeDist.lean`; `notes/etcdsvc-b.md`).

The guard `Γ.auth = false` is interim: there are no auth modes (one KV model, `nomode` N1-N4); once the
KV view specs are single (N4) the guard goes and auth-on members serve the same entries. -/
def etcdSvc (Γ : DistView) (mid : w64) : GrpcSvc GF := fun name =>
  if Γ.auth = false then (etcdKvSvc (GF := GF) Γ.kv name <|> etcdSvcRest Γ mid name)
  else etcdSvcRest Γ mid name

theorem etcdSvc_kv (Γ : DistView) (mid : w64) (name : GoString) (e : GrpcSvcEntry GF)
    (hauth : Γ.auth = false) (h : etcdKvSvc (GF := GF) Γ.kv name = some e) :
    etcdSvc (GF := GF) Γ mid name = some e := by
  unfold etcdSvc
  rw [if_pos hauth, h]
  rfl

theorem etcdKvSvc_put (γk : KVNames) :
    etcdKvSvc (GF := GF) γk go!"/etcdserverpb.KV/Put" =
      some (.unary ⟨client.putReqWire, client.putRespWire, client.etcdPutSpecV γk, true⟩) := by
  unfold etcdKvSvc
  rw [if_pos rfl]

theorem etcdKvSvc_range (γk : KVNames) :
    etcdKvSvc (GF := GF) γk go!"/etcdserverpb.KV/Range" =
      some (.unary ⟨client.rangeReqWire, client.rangeRespWire, client.etcdRangeSpecV γk, true⟩) := by
  unfold etcdKvSvc
  rw [if_neg (by decide), if_pos rfl]

theorem etcdKvSvc_delete (γk : KVNames) :
    etcdKvSvc (GF := GF) γk go!"/etcdserverpb.KV/DeleteRange" =
      some (.unary ⟨client.delReqWire, client.delRespWire, client.etcdDeleteSpecV γk, true⟩) := by
  unfold etcdKvSvc
  rw [if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem etcdKvSvc_txn (γk : KVNames) :
    etcdKvSvc (GF := GF) γk go!"/etcdserverpb.KV/Txn" =
      some (.unary ⟨client.txnReqWire, client.txnRespWire, client.etcdTxnSpecV γk, true⟩) := by
  unfold etcdKvSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

theorem etcdKvSvc_compact (γk : KVNames) :
    etcdKvSvc (GF := GF) γk go!"/etcdserverpb.KV/Compact" =
      some (.unary ⟨client.compactReqWire, client.compactRespWire, client.etcdCompactSpecV γk,
        true⟩) := by
  unfold etcdKvSvc
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]

end table

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The address `a` serves etcd's calls for the member `mid` of the view `Γ`** (persistent): `a`
serves etcd's table (`grpcAddrAt`: its net-library protocols are grpc's opaque `grpcCliPI`/`grpcSrvPI`
for the table, over a slot map). #24's `∃ σ, depSlotsCtx ∗ grpcAddrAt a (etcdSvc …)` (`grpcAddrAt`
holds `depSlotsCtx`). -/
def etcdAddrAt (a : GoString) (Γ : DistView) (mid : w64) : IProp GF :=
  iprop(∃ σ : NetSlotGS, grpcAddrAt (Gg := Gg) (π := π) (σ := σ) a (etcdSvc (GF := GF) Γ mid))

instance etcdAddrAt_persistent (a : GoString) (Γ : DistView) (mid : w64) :
    Persistent (etcdAddrAt (GF := GF) a Γ mid) := by
  unfold etcdAddrAt; infer_instance

/-- **Every endpoint serves a member of the view `Γ`** (persistent): what a client of several
endpoints (`etcdstart.NewClients eps`) takes. -/
def membersAt (eps : List GoString) (Γ : DistView) : IProp GF :=
  iprop([∗list] a ∈ eps, ∃ mid : w64, etcdAddrAt (GF := GF) a Γ mid)

instance membersAt_persistent (eps : List GoString) (Γ : DistView) :
    Persistent (membersAt (GF := GF) eps Γ) := by
  unfold membersAt; infer_instance

/-- One endpoint's address fact is the endpoints' fact of the one-element list. -/
theorem membersAt_one (a : GoString) (Γ : DistView) (mid : w64) :
    etcdAddrAt (GF := GF) a Γ mid ⊢ membersAt [a] Γ := by
  iintro #H
  iunfold membersAt
  iapply BigSepL.bigSepL_singleton.2
  iexists mid
  iexact H

/-- **The start law** (`notes/putget-dist-plan.md` §12; proved since the S2 interface switch, 2026-11-24,
where it was an axiom): the deployment's start sets the unset address `a` to serve etcd's table for
`(Γ, mid)`, over a fresh slot map (`depSlots_alloc`, then `grpc_addr_set`). It spends `addrUnset a`:
`a`'s pending set, its token and its listening token, so `a` is set at most once (`netLisTok_excl`). It is
not the only source of `etcdAddrAt`: `net.Listen`'s `netAddrLeft` sets a table too (`addr_set_proto_tok`), and
`etcdAddrAt`'s `addrProto` lets its holder listen at `a` (`listen_au`). With the old `bridge.New` that refuted
the client contracts (review 4); since 2026-11-24 `bridge.New` also consumes `netAddrLeft a`, which neither
route leaves (`notes/axiom-review/bridge-addrleft.md`). -/
theorem etcdAddr_set (E : CoPset) (a : GoString) (Γ : DistView) (mid : w64) :
    ⊢ regCtx (Gg := Gg) -∗ addrUnset (Gg := Gg) a ={E}=∗ etcdAddrAt (GF := GF) a Γ mid := by
  iintro #Hreg Hu
  imod depSlots_alloc (Gg := Gg) E with ⟨%σ, #Hs⟩
  imod grpc_addr_set (Gg := Gg) (σ := σ) E a (etcdSvc (GF := GF) Γ mid) $$ Hreg Hs Hu with #Ha
  imodintro
  unfold etcdAddrAt
  iexists σ
  iexact Ha

end addr

end etcd_dist
end EtcdGrove
end Perennial

end
