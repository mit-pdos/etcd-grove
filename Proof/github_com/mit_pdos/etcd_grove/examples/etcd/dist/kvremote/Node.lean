/- Lean-first (no Rocq counterpart).

The proof of `Node.spec`: `zap.NewNop()`; `etcdstart.NewClients(eps, lg)` (at a watch environment
`kvNodePre` says exists: `Call` reads none of it); on its error `Node` returns; otherwise the client
is a client of the view (`kvClientV_intro`: `NewClients`' `isNewClient` and `clientNoProxy`, the
start's `membersAtV`); then `remote.ServeClient` at the store `kvR Γ.kv`'s service with `Codec()`
(`codecOk_wireOk`), the system `tok sys := ⌜sys = cli⌝ ∗ levelTok 0` (`newClient` returns the
client), and the operation `opMaybe` (`opMaybe_svcOp`): `op(sys, in)` is `txnlin.Call(cli, in)`
across machines (`Call_dist.spec`), whose update is the slot's (`slotUpd_callUpd`, at a fresh token
`γt` for a read's result) and whose result is back `Φ` of a store output (`nodeQ_out` for a write;
`nodeRQ_out` for a read, whose later is paid by one credit taken in the closure's steps before the
call) or the unknown output (`Call`'s error, `errOut`).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Node
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.CallDist
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Codec
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClients
public import Net.Spec.github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.NodeUpd
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.ClientV

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open EtcdGrove EtcdGrove.etcd_txnlin EtcdGrove.etcd_dist.view
open github_com.mit_pdos.etcd_grove.examples.etcd.txnlin
open github_com.mit_pdos.etcd_grove.examples.lib.remote

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote.Assumptions]
variable [v3rpc_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable [srv_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]
variable [cache_sem : go_etcd_io.etcd.cache.v3.Assumptions]
variable [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [ρ : RemoteGS]

theorem Node.wp_proof (svc : DistView → w64 → GrpcSvc GF)
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_NewClients : etcdstart.NewClients.spec (GF := GF) (hG := hG))
    (wp_Codec : Codec.spec (GF := GF) (hG := hG))
    (wp_Call_dist : Call_dist.spec (GF := GF) (hG := hG) svc)
    (wp_ServeClient : github_com.mit_pdos.etcd_grove.examples.lib.remote.ServeClient.spec
      (GF := GF) (hG := hG) (I := VIn) (O := VOut)) :
    Node.spec (GF := GF) (hG := hG) svc := by
  intro c addr eps epsL
  wp_start as ⟨Heps, Hpre⟩
  iunfold kvNodePre at Hpre
  icases Hpre with ⟨%Γ, %Hp, Hlt, #Hm, #Hra⟩
  obtain ⟨hauth, htb, hpl, hAs, hV⟩ := Hp
  ihave #Hrp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.remote $$ []
  · iPkgInit
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Ptl : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  iapply fupd_wp
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  imodintro
  wp_auto
  wp_apply wp_NewNop as %lg #Hlg
  wp_apply (wp_NewClients eps epsL lg (Classical.choice hV) htb hpl) $$ [$Hlt]
    as %cl %cerr ⟨Hlt, Hcl⟩
  · iframe #
  icases Hcl with (⟨%Hcerr, #Hnc, -, #Hnp⟩ | %Hcfail)
  rotate_left
  · -- no client: `Node` returns
    obtain ⟨Hcerr, -⟩ := Hcfail
    cases cerr with
    | nil => exact absurd rfl Hcerr
    | ok ei => ?_
    wp_auto
    iapply HΦ; itrivial
  subst Hcerr
  ihave Hkv := kvClientV_intro svc cl epsL (Classical.choice hV) Γ $$ [Hnc Hnp Hm]
  · iframe #
  icases Hkv with ⟨%api, Hkv⟩
  iunfold kvClientV at Hkv
  icases Hkv with ⟨#Hk1, #Hk2, #Hk3, #Hk4⟩
  wp_auto
  ipersist cli
  wp_apply (wp_Codec Γ.kv) as %cd #Hcd
  wp_apply wp_ServeClient (RBase.svc (Gg := hG.goose_globalGS) (kvR Γ.kv)) c addr _ _ cd _
    (fun sys => iprop(⌜sys = interface.mkOk
      (go.GoType.PointerType go_etcd_io.etcd.client.v3.Client.ty) #cl⌝ ∗ levelTok 0)) $$ [Hlt]
    as ⟨⟩
  iframe #
  isplitr [Hlt]
  · iapply codecOk_wireOk $$ Hcd
  isplitr [Hlt]
  · -- the operation: `txnlin.Call` across machines
    iapply opMaybe_svcOp
    unfold opMaybe
    iintro %sys %x %Ψ
    iintro !> %Φr ⟨⟨%Hsys, Hlt⟩, Hupd, -⟩ HΦr
    subst Hsys
    rw [show ((kvR (GF := GF) Γ.kv).iv x : GoInterface) = boxIn x.1 from rfl]
    wp_auto_lc 1
    imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
    ihave HU := slotUpd_callUpd Γ.kv γt x Ψ $$ Hupd
    wp_apply_core (wp_Call_dist cl api epsL (Classical.choice hV) Γ hauth hAs x.1 (kvMi x)
      (if (kvMi x).isWrite then nodeQ x Ψ else nodeRQ γt x Ψ) (kvMi_dec x) x.2) $$ [Hlt HU]
    · iframe #
      iframe
      iunfold kvClientV
      iframe #
    iintro %v ⟨Hlt, Hv⟩
    icases Hv with (%Hv | ⟨%y, %σ, HQ, %Hy⟩)
    · -- `Call` failed: the unknown output
      subst Hv
      wp_auto
      iapply HΦr
      dsimp only
      iframe Hlt
      isplitr
      · ipureintro; rfl
      iright
      ipureintro; rfl
    obtain ⟨Hvy, -, -, hy⟩ := Hy
    subst Hvy
    cases hw : (kvMi x).isWrite
    · -- a read: its result from the invariant, the later paid by the credit
      isimp only [callRes, hw, Bool.false_eq_true, ↓reduceIte] at HQ
      icases HQ with #HQ
      imod nodeRQ_out γt x Ψ σ y hy ⊤ CoPset.subseteq_top $$ HQ Htok with HR
      imod lc_fupd_elim_later (E := ⊤) $$ Hlc1 HR with ⟨%o, %Hyo, HR⟩
      subst Hyo
      wp_auto
      iapply HΦr
      dsimp only
      iframe Hlt
      isplitr
      · ipureintro; rfl
      ileft
      iexists o
      iframe HR
      ipureintro; rfl
    · -- a write: its result
      isimp only [callRes, hw, ↓reduceIte] at HQ
      ihave HR := nodeQ_out x Ψ σ y hy $$ HQ
      icases HR with ⟨%o, %Hyo, HR⟩
      subst Hyo
      wp_auto
      iapply HΦr
      dsimp only
      iframe Hlt
      isplitr
      · ipureintro; rfl
      ileft
      iexists o
      iframe HR
      ipureintro; rfl
  · -- the client's system: the client
    iintro %Φr HΦr
    wp_auto
    iapply HΦr
    iframe Hlt
    ipureintro; rfl

end proof

end github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote
end Perennial
