/-
**etcd's KV calls registered at a served member's address** (2026-10-22, D33). Lean-first (no Rocq
counterpart).

The ghost step putget's, linkv's, linkvtxn's, putget3's and linkv3's `Main`s took between `Listen`
and `go gs.Serve(l)`, once, for `Serve`'s caller's ghost step (`Serve.spec`'s `G`):
* `kv_served`: from `v3rpc.Server`'s and `Listen`'s results (`grpcUp`) and the request slots a
  started member leaves (`memberUp`'s; one gRPC slot, `client.etcdGrpcSlots_of_started`), the right
  to serve and etcd's `Put`, `Range`, `DeleteRange` and `Txn` at the address
  (`client.etcd_kv_started`);
* `grpcUp_noRefusal`: the member never refuses (authentication off, a voter: the members' axiom
  `etcd_noRefusal`, D29), which the examples whose clients retry take before `kv_served`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Defs
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NoRefusal

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace common

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- **etcd's KV calls at `addr`** (persistent): `Put`, `Range`, `DeleteRange`, `Txn`, at the
server's views (`E`, the request names' read names `ρ.rd` and the read names `γr`) and the KV
server's cluster and member ids. -/
def etcdKVAt (addr : GoString) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid : w64) : IProp GF :=
  iprop(isGrpcRpc addr go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E ρ.rd cid mid) ∗
    isGrpcRpc addr go!"/etcdserverpb.KV/Range" (client.etcdRangeSpec E γr cid mid) ∗
    isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (client.etcdTxnSpec E ρ.rd γr cid mid))

instance etcdKVAt_persistent (addr : GoString) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) : Persistent (etcdKVAt (GF := GF) addr E ρ γr cid mid) := by
  unfold etcdKVAt; infer_instance

/-- **etcd's KV registrations at the address are the member's** (`client.kvRegsAt`, what the
client's calls take, D44) when the request path's and the read loop's read names are one (a
started server's, `ρ.rd = γr`). -/
theorem etcdKVAt_regs (addr : GoString) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid : w64) (hρ : ρ.rd = γr) :
    etcdKVAt (GF := GF) addr E ρ γr cid mid ⊢
      client.kvRegsAt (⟨addr, E, γr, cid, mid⟩ : client.SrvAt GF) := by
  subst hρ
  iintro #H
  iunfold etcdKVAt at H
  unfold client.kvRegsAt
  iexact H

/-- **The member never refuses** (see the file header): `etcd_noRefusal` at `grpcUp`'s gRPC
server and listener. -/
theorem grpcUp_noRefusal (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (gs : Loc)
    (lis : GoInterface) (addr : GoString) (cid mid : w64) (R : v3rpc.WSrv GF)
    (HEo : E.authOn = false) :
    isServerReq s E ρ ∗ grpcUp s E ρ γr gs lis addr cid mid R ⊢
      grpcUp s E ρ γr gs lis addr cid mid R ∗ ⌜noRefusalAt addr⌝ := by
  iintro ⟨#Hreq, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %d', %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, Hlg, Hbemu, Hgo, Hwpi, HWRs,
    Hlis⟩
  ihave ⟨Hgsn, Hlis, %Hnr⟩ := (EtcdGrove.etcd_noRefusal addr gs q p s lis E ρ [il, im, iu]
      [ims, is] svcs regs sregs HC.2.2.1 HEo) $$ [Hgsn Hlis]
  · iframe Hgsn Hlis; iframe #
  isplitl
  · iunfold grpcUp
    iexists C, q, p, pw, il, im, iu, ims, is, svcs, regs, sregs, d'
    iframe; iframe #
    ipureintro; exact HC
  ipureintro; exact Hnr

/-- **etcd's KV calls registered at the address** (see the file header). -/
theorem kv_served [v3rpc.ServerMethodSets] (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗
        ([∗list] _x ∈ List.replicate 64 (), srvLeadTimeReader s) ∗
        ([∗list] _x ∈ List.replicate (64 - 2) (), srvLgReader s) ∗
        ([∗list] _x ∈ List.replicate 64 (), E.RD) ∗
        ([∗list] _x ∈ List.replicate 64 (), mvcc.storeReader E.s E.γ) ∗
        ([∗list] _x ∈ List.replicate (Int.toNat sync.rwmutex.actualMaxReaders) (),
          srvReadReader s γr) ∗
        ([∗list] _x ∈ List.replicate 64 (), srvBemuReader s) ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> grpcServeTok gs lis ∗ etcdKVAt addr E ρ γr cid mid := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %d', %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, -, -, Hlis⟩
  obtain ⟨HCA, -, Hregs, -⟩ := HC
  icases replicate_take2 _ _ (by omega) $$ Hlts with ⟨-, -, Hlts⟩
  icases replicate_take2 _ _ (by omega) $$ Hrds with ⟨-, -, Hrds⟩
  ihave Hslots := client.etcdGrpcSlots_of_started s E γr 1 (64 - 2) 64
      (Int.toNat sync.rwmutex.actualMaxReaders) 64 (by omega) (by omega)
      (by have := sync.actualMaxReaders_ge_2; omega) (by omega)
      $$ [Hlts Hlgs Hrds Hsts Hrslots Hbms]
  · iframe
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  rw [HCA]
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
      sregs 1 Hregs) $$ [Hgsn Hlis Hslots] with ⟨Hserv, -, #HPut, #HRange, #HDel, #HTxn⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb
  imodintro
  iframe Hserv
  iunfold etcdKVAt
  iframe #

end served

end common
end EtcdGrove
end Perennial
