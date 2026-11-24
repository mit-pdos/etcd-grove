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

/-- **etcd's KV calls registered at every address serving the member's table** (see the file
header; phase 7's switch, SW1, 2026-11-24: relative to the table, `tableAt`, so that a bridge set to
it serves them too, `StartBridge`); under `grpcRepliesFit` (`grpc.start'`'s). -/
theorem kv_served_tbl (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (γr : ReadNames) (gs : Loc) (lis : GoInterface) (addr : GoString) (cid mid : w64)
    (R : v3rpc.WSrv GF) (Hrb : receiptBound GF ≤ 2 ^ 48) (Hrf : grpcRepliesFit) (hρ : ρ.rd = γr)
    (HL : srvLevels (GF := GF)) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc ∗
        isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver ∗
        isServerReq s E ρ ∗ isServerRead s E γr ∗ kvServeStocks s E γr ∗
        grpcUp s E ρ γr gs lis addr cid mid R ⊢
      |={⊤}=> (∃ Svc, grpcServeTok gs lis addr Svc) ∗
        tableAt addr (fun a => etcdKVAt a E ρ γr cid mid) := by
  iintro ⟨#Pv3, #Psrv, #Hreq, #Hrd, Hstk, Hup⟩
  iunfold grpcUp at Hup
  icases Hup with ⟨%C, %q, %p, %pw, %il, %im, %iu, %ims, %is, %svcs, %regs, %sregs, %HC,
    #Hgc, Hgsn, #Hq, #Hkvs, #Hws, #Hil, #Him, #Hiu, #Hims, #His, -, -, -, Hleft, -⟩
  obtain ⟨HCA, -, Hregs, -, -, -, -, -, Hnd⟩ := HC
  imod (kvServeStocks_pools s E γr ⊤) $$ Hstk with ⟨#Hrp, #Hb⟩
  ihave #Hkva := client.kvServerAt_of_is p s C.A cid mid C.n $$ Hkvs
  rw [HCA]
  ihave Hgsn := grpcSrvUp_lis gs lis addr _ _ svcs regs sregs $$ Hgsn
  imod (client.etcd_kv_started addr gs q p s lis E ρ γr cid mid C.n il im iu ims is svcs regs
      sregs [] Hregs (by intro m hm; simp at hm) (by simp) Hrf Hnd hρ HL) $$ [Hgsn Hleft]
      with ⟨Hserv, -, -, -, -, -, -, #Hsat, #Htab⟩
  · iframe; iframe #
    isplitl []
    · iintro !>
      imodintro
      iunfold idCred
      ipureintro; exact Hrb
    iintro !>
    iapply BigSepL.bigSepL_nil.2
    itrivial
  imodintro
  isplitl [Hserv]
  · iexists _; iexact Hserv
  iunfold tableAt
  iexists _, _, _, _
  iframe Hsat
  iintro !> %a #Ha
  imod Htab $$ %a Ha with ⟨-, #HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  imodintro
  iunfold etcdKVAt
  iframe #

/-- **etcd's KV calls registered at the address** (see the file header); under `grpcRepliesFit`
(`grpc.start'`'s). -/
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
  imod (kv_served_tbl s E ρ γr gs lis addr cid mid R Hrb Hrf hρ HL) $$ H with ⟨Htok, #Ht⟩
  imod (tableAt_self addr _) $$ Ht with #Hkv
  imodintro
  iframe Htok Hkv

end served

end etcdstart
end EtcdGrove
end Perennial
