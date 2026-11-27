/- Lean-first (no Rocq counterpart).

# Interim cross-machine vocabulary for etcd's distributed theorems (until #24's S2 switch)

`notes/putget-dist-plan.md` §12, `notes/etcd-dist-plan.md` §18. The cluster's view (`DistView`, O1 option
B: a Lean value the start fixes; no publication) and the address fact over it, since phase 7 S2's interface
switch (2026-11-24) #24's own `grpcAddrAt a (etcdSvc Γ mid)` with only the table `etcdSvc` axiomatized (see
its docstring).

One axiom (A1 `etcdSvc`; the start law `etcdAddr_set` is a theorem); the function axioms are in their own
files beside this one: `ServeDist.lean` (the server side) and the clientv3 contracts `KVPutDist.lean`,
`KVGetDist.lean`, `KVDeleteDist.lean`, `KVCompactDist.lean`, `TxnCommitDist.lean` (putget's
`Client_Put_dist`/`Client_Get_dist` are theorems over the first two). Every other declaration is a
definition or a proved law.
-/
module

public import GooseLang.Ext.Net.Proto
public import Proof.google_golang_org.grpc.InvGrpcWire
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest

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
* `auth`: the cluster's auth mode. The KV write contracts are for `auth = false` only (refusal-free
  members: a write is sent at most once); `Serve_dist` serves a member whose auth mode is the view's
  (`memberUpL` with auth off, `memberUpOnL` with auth on).
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

/-! ## The address fact (over phase 7 S2's interface; the table axiomatized: see `etcdSvc`) -/

/-- **etcd's service table for the member `mid` of the cluster view `Γ`** (interim, axiomatized;
heap-free: it takes no `HeapGS`, so every machine holds the same table). Its intended interpretation is
#24's `etcdSvc` (`notes/phase7-plan.md` §1.3) at the view (`notes/etcd-dist-plan.md` §18.3): etcd's unary
methods by full name, each at its messages' wire parts (`pbPutRequest.wire`, ...) with the member's
handler spec at names agreeing with `Γ` (`kvCongr` of its KV names with `Γ.kv`), `grpcNoCall` for the
methods no client of the theorems calls. It cannot be defined yet: the entries' specs need S2's etcd side
(the handlers' contracts as wire specs, #24). It has no law: no proof can learn an entry of it, so nothing
can call it through grpc's own `Invoke` (`isGrpcRpcMd` needs an entry of the table at the address), and
only a server registering no method (unary or stream; its interceptors may be anything) serves it through
`Server.Serve` (`grpcServes … [] [] []` holds vacuously: every call gets `Unimplemented`). The client-side
contracts at the table (`KV_Put_dist`, `KV_Get_dist`, ...) are axioms of their own. A table is data, so
the axiom is consistent (`GrpcSvc` is inhabited). Retired by S2's `etcdSvc` (the cluster id `cid` joins
the view then, #24 05:09Z). -/
axiom etcdSvc [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
    [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
    {GF : BundledGFunctors} [GooseGlobalGS .hasLC GF]
    (Γ : DistView) (mid : w64) : GrpcSvc GF

section addr
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable [GoLocalContext] [go.Semantics] [go_etcd_io.etcd.client.v3.Assumptions]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The address `a` serves etcd's calls for the member `mid` of the view `Γ`** (persistent): `a`
serves etcd's table (`grpcAddrAt`: its net-library protocols are grpc's opaque `grpcCliPI`/`grpcSrvPI`
for the table, over a slot map). #24's `∃ σ, depSlotsCtx ∗ grpcAddrAt a (etcdSvc …)` (`grpcAddrAt`
holds `depSlotsCtx`); only the table is axiomatized. -/
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
