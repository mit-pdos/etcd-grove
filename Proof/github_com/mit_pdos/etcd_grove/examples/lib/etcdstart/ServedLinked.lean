/-
`kv_served` (etcd's KV calls registered at the address, from `client.etcd_kv_started`, a linked result),
moved out of `Served.lean` (2026-11-18) so that the definitions there (`etcdKVAt`, `srvWOf`), which
specs name, import no linked result (CLAUDE.md, "Import tiers"). See `Served.lean`'s header.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart

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

/-- **etcd's KV calls registered at the address, and the server there etcd's** (see the file
header; `kv_served` with `etcdKVSrv`, what `etcd_noRefusal_at` takes, 2026-11-24); under
`grpcRepliesFit` (`grpc.start`'s). -/
theorem kv_served_at (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ etcdKVAt addr E ρ γr cid mid ∗
        etcdKVSrv addr s := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, Hstk, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, Hlis, Hleft, -, #Hics⟩
  obtain ⟨HCA, -, Hregs, -, -, -, -, -, Hnd⟩ := HC
  imod (kvServeStocks_pools s E γr ⊤) $$ Hstk with ⟨#Hrp, #Hb⟩
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  rw [HCA]
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
      sregs Hregs Hrf Hnd hρ HL) $$ [Hgsn Hlis Hleft] with ⟨%γ, Hserv, -, #Hksa, #HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb
  imodintro
  isplitl [Hserv]
  · iexists _; iexact Hserv
  isplitr
  · iunfold etcdKVAt
    iframe #
  iapply etcdKVSrv_intro addr s [il, im, iu]
  iframe #

/-- **`kv_served_at`, with the `GoAttach` resources given back** (decision 1b, 2026-11-24): its post and
the member's `srvGoRes` (the thread token it holds), which the serving thread splits again for its
own client calls (as `kv_lease_served_go`). -/
theorem kv_served_at_go (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ etcdKVAt addr E ρ γr cid mid ∗
        etcdKVSrv addr s ∗ srvGoRes s := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, Hstk, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, Hgo, Hlis, Hleft, -, #Hics⟩
  obtain ⟨HCA, -, Hregs, -, -, -, -, -, Hnd⟩ := HC
  imod (kvServeStocks_pools s E γr ⊤) $$ Hstk with ⟨#Hrp, #Hb⟩
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  rw [HCA]
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
      sregs Hregs Hrf Hnd hρ HL) $$ [Hgsn Hlis Hleft] with ⟨%γ, Hserv, -, #Hksa, #HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  · iframe; iframe #
    iintro !>
    imodintro
    iunfold idCred
    ipureintro; exact Hrb
  imodintro
  iframe Hgo
  isplitl [Hserv]
  · iexists _; iexact Hserv
  isplitr
  · iunfold etcdKVAt
    iframe #
  iapply etcdKVSrv_intro addr s [il, im, iu]
  iframe #

/-- **etcd's KV calls registered at the address** (see the file header; `kv_served_at` without the
server's identity); under `grpcRepliesFit` (`grpc.start`'s). -/
theorem kv_served (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ etcdKVAt addr E ρ γr cid mid := by
  iintro H
  imod (kv_served_at s E ρ γr gs lis addr cid mid R Hrb Hrf hρ HL) $$ H with ⟨Hserv, #Hkv, -⟩
  imodintro
  iframe Hserv Hkv

/-- **`kv_served`, with the `GoAttach` resources given back** (decision 1b, 2026-11-24): `kv_served`'s
post and the member's `srvGoRes` (`kv_served_at_go`). -/
theorem kv_served_go (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗ etcdKVAt addr E ρ γr cid mid ∗ srvGoRes s := by
  iintro H
  imod (kv_served_at_go s E ρ γr gs lis addr cid mid R Hrb Hrf hρ HL) $$ H with ⟨Hserv, #Hkv, -, Hgo⟩
  imodintro
  iframe Hserv Hkv Hgo

end served

end etcdstart
end EtcdGrove
end Perennial
