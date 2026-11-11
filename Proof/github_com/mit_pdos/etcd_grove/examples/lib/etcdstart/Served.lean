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

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Defs
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.NoRefusal

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcdstart

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section served
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
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
    isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (client.etcdRangeSpecE E γr cid mid) ∗
    isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (client.etcdDeleteSpec E ρ.rd cid mid) ∗
    isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (client.etcdTxnSpec E ρ.rd γr cid mid) ∗
    isGrpcRpc addr go!"/etcdserverpb.KV/Compact" (client.etcdCompactSpec E ρ.rd cid mid))

instance etcdKVAt_persistent (addr : GoString) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (cid mid : w64) : Persistent (etcdKVAt (GF := GF) addr E ρ γr cid mid) := by
  unfold etcdKVAt; infer_instance

omit [HasExt idIssueExt] cache_sem in
/-- **`etcdKVAt` is its five registrations** (`rfl`; lease-mono3's review r2, N1: the law a client
rewrites with, in place of unfolding the definition). -/
theorem etcdKVAt_eq (addr : GoString) (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames)
    (cid mid : w64) :
    etcdKVAt (GF := GF) addr E ρ γr cid mid =
      iprop(isGrpcRpc addr go!"/etcdserverpb.KV/Put" (client.etcdPutSpec E ρ.rd cid mid) ∗
        isGrpcRpcMd addr go!"/etcdserverpb.KV/Range" (client.etcdRangeSpecE E γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/DeleteRange" (client.etcdDeleteSpec E ρ.rd cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Txn" (client.etcdTxnSpec E ρ.rd γr cid mid) ∗
        isGrpcRpc addr go!"/etcdserverpb.KV/Compact" (client.etcdCompactSpec E ρ.rd cid mid)) :=
  rfl

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
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, Hlg, Hbemu, Hgo,
    Hlis, #Hlu⟩
  ihave ⟨Hgsn, Hlis, %Hnr⟩ := (EtcdGrove.etcd_noRefusal addr gs q p s lis E ρ [il, im, iu]
      [ims, is] svcs regs sregs HC.2.2.1 HEo) $$ [Hgsn Hlis]
  · iframe Hgsn Hlis; iframe #
  isplitl
  · iunfold grpcUp
    iexists C, q, p, pw, il, im, iu, ims, is, svcs, regs, sregs
    iframe; iframe #
    ipureintro; exact HC
  ipureintro; exact Hnr

/-- **The server's watch facts, as the watch path names them** (R9, the `lean` merge: v3rpc's
`SrvW` of the server at its apply environment `E`, read names `γr` and auth mode `on`): the store's
handle and names, the store invariant's namespace, the certified bounds of the notified log
(`srvApi.histLb`, what `client.srvKVFacts` ties `W.histLb` to) and the compaction permits
(`srvApi.crevOk`). -/
def srvWOf (E : apply.AEnv GF) (γr : ReadNames) (on : Bool) : v3rpc.SrvW GF :=
  ⟨E.kv, E.γ, srvApi.kvsN, srvApi.histLb γr on E.γs, srvApi.crevOk γr⟩

/-- **The raw stocks a started member leaves for its gRPC runs** (per-type stage B3, 2026-11-11;
`memberUp`'s, written once for `kv_served`, `kv_lease_served` and the watch servers): the server's
serving stock (`srvServeStock`: the revocation's built part, the run pool's raw readers of the store
and `bemu`) and the read loop's readers for the run pool (`srvRunReadStock`), from which the serve
step builds the gRPC run pool (`srvRunPool_init`). Until B3: 64 reader slots of each kind, from which
the served theorems' caller-chosen slots were made. -/
def kvServeStocks (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) : IProp GF :=
  iprop(srvServeStock s E ∗ srvRunReadStock s γr)

/-- **The run pools, built at the serve step** (per-type stage B3): `srvRunPool_init` on the stocks,
at any mask. -/
theorem kvServeStocks_pools (s : Loc) (E : apply.AEnv GF) (γr : ReadNames) (Em : CoPset) :
    kvServeStocks (GF := GF) s E γr ⊢ |={Em}=> srvRunPool s E γr ∗ srvRevokeBuilt s E := by
  iintro H
  unfold kvServeStocks
  imod (srvRunPool_init s E γr Em) $$ H with ⟨#Hrp, #Hb⟩
  imodintro
  iframe #

/-- **etcd's KV calls registered at the address** (see the file header); under `grpcRepliesFit`
(`grpc.start`'s). -/
theorem kv_served (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ γ, grpcServeTok gs lis γ) ∗ etcdKVAt addr E ρ γr cid mid := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, Hstk, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, Hlis, -⟩
  obtain ⟨HCA, -, Hregs, -, -, -, -, -, Hnd⟩ := HC
  imod (kvServeStocks_pools s E γr ⊤) $$ Hstk with ⟨#Hrp, #Hb⟩
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  rw [HCA]
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
      sregs Hregs Hrf Hnd hρ HL) $$ [Hgsn Hlis] with ⟨%γ, Hserv, -, #HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb
  imodintro
  isplitl [Hserv]
  · iexists γ; iexact Hserv
  iunfold etcdKVAt
  iframe #

end served

section memberUp
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **A started member, for serving** (N6, 2026-11-06; what `Serve`, `v3rpc.Server` and the
examples' ghost steps take of `memberUp`): at its apply environment `E` (agreeing with `E₀`, auth
off), configuration `cfg` (with the logger `lg`, no tracer options, no progress-notify interval) and
wait-registry name `γw`, the request and read views, the serving facts, the `GoAttach` resources, an
`lgMu` and a `bemu` reader slot, the watchable store's built part (`srvWatchBuilt`), the raw stocks
the gRPC run pools are built from (`kvServeStocks`, per-type stage B3), the partitioner's part (`srvPeerCtl`) and the lease
subsystem's reader side (`srvLeaseRd`). The rest of `memberUp` (the right to stop it, the read
loop's other slots) is dropped. The examples reach `memberUp` through this law and `memberUp_stop`, never its body, so that
a new conjunct of `memberUp` changes only these laws' proofs. -/
theorem memberUp_served (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc)
    (γn : NetNames GF) (id : w64) (m : lease.Mode) :
    memberUp (GF := GF) s ρ E₀ lg γn id m ⊢
      ∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
        ⌜envAgree E E₀ ∧ E.authOn = false ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
          cfg.WatchProgressNotifyInterval' = 0⌝ ∗
        isServerReq s E { ρ with wait := γw } ∗ isServerRead s E ρ.rd ∗ srvServeFacts s E cfg ∗
        srvGoRes s ∗ srvLgReader s ∗ srvBemuReader s ∗ srvWatchBuilt s E ∗
        kvServeStocks s E ρ.rd ∗
        srvPeerCtl γn s id ∗ srvLeaseRd s E m := by
  iintro Hup
  iunfold memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, Hstk, Hrun, #Hreq, #Hrd, Hgo, Hlg3, -, #Hwb, #Hsf, Hbemu,
    Hctl, #HLR, -⟩
  iexists E, cfg, γw
  isplitr; · ipureintro; exact HEc
  iframe Hreq Hrd Hsf Hgo Hlg3 Hbemu Hwb Hctl HLR
  unfold kvServeStocks
  iframe Hstk Hrun

/-- **A member started with auth on, from its parts** (N6, 2026-11-06; `memberUpOn`'s introduction,
for a starter outside the package, authkv's `startServer`): its conjuncts (per-type stage B2: with
the gRPC run pool's raw stocks), the views in its mode (`E.authOn`, `true`). (Until per-type stage
B3, 2026-11-11, also the reader stocks the gRPC runs took, 64 of each kind, and the watch service's
reader tokens, `srvWatchReaders`.) -/
theorem memberUpOn_intro (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc)
    (γn : NetNames GF) (id : w64) (γa : auth.AuthNames) (E : apply.AEnv GF)
    (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName) :
    ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
        cfg.WatchProgressNotifyInterval' = 0⌝ ∗
      srvServeStock s E ∗ srvRunReadStock s ρ.rd ∗
      isServerReqM E.authOn s E { ρ with wait := γw } ∗ isServerReadM E.authOn s E ρ.rd ∗
      srvAuthLb s E ∗ srvWatchBuilt s E ∗ srvServeFacts s E cfg ∗
      srvGoRes s ∗ srvLgReader s ∗ srvBemuReader s ∗
      ([∗list] _x ∈ List.replicate memberReadN (), srvReadReader s ρ.rd) ∗
      srvPeerCtl γn s id ∗ □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD ⊢
    memberUpOn (GF := GF) s ρ E₀ lg γn id γa := by
  iintro ⟨%HEc, H⟩
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [HEc.2.1]; rfl
  irevert H
  rw [hon]
  iintro ⟨Hstk, Hrun, #Hreq, #Hrd, #Hlb, #Hwb, #Hsf, Hgo, Hlg3, Hbemu, Hrslots, Hctl, #Htls, #HBF⟩
  iunfold memberUpOn
  iexists E, cfg, γw
  isplitr; · ipureintro; exact HEc
  isplitl [Hstk]; · iexact Hstk
  isplitl [Hrun]; · iexact Hrun
  iframe Hreq Hrd Hlb Hwb Hsf Htls HBF
  iframe

/-- **A member started with auth on, for serving** (N6, 2026-11-06; `memberUp_served`'s): what
`Serve` and authkv's ghost steps take of `memberUpOn`, the views in its mode (`E.authOn`, which is `true`: what `Serve` takes), the store's range
check (`srvAuthLb`), the TLS fallback off and the auth store's `Authenticate` side besides. The rest
(`srvWatchBuilt`) is dropped. -/
theorem memberUpOn_served (s : Loc) (ρ : ReqNames) (E₀ : apply.AEnv GF) (lg : Loc)
    (γn : NetNames GF) (id : w64) (γa : auth.AuthNames) :
    memberUpOn (GF := GF) s ρ E₀ lg γn id γa ⊢
      ∃ (E : apply.AEnv GF) (cfg : go_etcd_io.etcd.server.v3.config.ServerConfig) (γw : GName),
        ⌜envAgree E E₀ ∧ E.authMode = .on γa ∧ cfg.Logger' = lg ∧ cfg.TracerOptions' = slice.nil ∧
          cfg.WatchProgressNotifyInterval' = 0⌝ ∗
        isServerReqM E.authOn s E { ρ with wait := γw } ∗ isServerReadM E.authOn s E ρ.rd ∗
        srvAuthLb s E ∗ srvServeFacts s E cfg ∗
        srvGoRes s ∗ srvLgReader s ∗ srvBemuReader s ∗ srvWatchBuilt s E ∗
        kvServeStocks s E ρ.rd ∗
        srvPeerCtl γn s id ∗ □ (srvTLSId s -∗ False) ∗ srvAuthStoreOn s E.RD := by
  iintro Hup
  iunfold memberUpOn at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, Hstk, Hrun, #Hreq, #Hrd, #Hlb, Hgo, Hlg3, -, #Hwb, #Hsf,
    Hbemu, Hctl, #Htls, #HBF⟩
  have hon : E.authOn = true := by unfold apply.AEnv.authOn; rw [HEc.2.1]; rfl
  iexists E, cfg, γw
  isplitr; · ipureintro; exact HEc
  rw [hon]
  iframe Hreq Hrd Hlb Hsf Hgo Hlg3 Hbemu Hwb Hctl Htls HBF
  unfold kvServeStocks
  iframe Hstk Hrun

end memberUp

end etcdstart
end EtcdGrove
end Perennial
