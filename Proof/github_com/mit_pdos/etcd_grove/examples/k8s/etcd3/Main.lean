/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/Main.lean` (stage 6g of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

As `linkvtxn/Main.lean` to the client (the shared start, `etcdstart.StartServer` and `etcdstart.Serve`,
at `k8setcd3`'s configuration), then: `kubernetes.New` (a write sent at most once: the member is refusal-free, D29), the seeding (`seedInv` over etcd's
start state, `seed`, cancelled at the seeded state), the store's history at the seeded state
(`histAuth_seed`), `etcd3.New` (the driver's contract), the instance's invariant at the seeded
state (`kInv_seed`) and `Check(s, st0, clients, ops, 0)`, which returns `Ok` (`timeout = 0`), so the
panic on `Illegal` is not taken. Every step's error ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.seed
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewDefaultLeaseManagerConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Contract
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Serve
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.Served
public import Spec.go_etcd_io.etcd.client.v3.New
public import Perennial.Spec.context.Background
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.BuildGap
public import Proof.go_etcd_io.etcd.client.v3.ServeFromStart
public import Proof.go_etcd_io.etcd.client.v3.ClientPutGet
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

set_option maxHeartbeats 3200000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : etcdstart.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : etcdstart.Serve.spec (GF := GF) (hG := hG))
    (wp_kNew : kubernetes.New.spec (GF := GF) (hG := hG))
    (wp_seed : seed.spec (GF := GF) (hG := hG))
    (wp_sNew : k8s.New.spec (GF := GF) (hG := hG))
    (wp_lmc : k8s.NewDefaultLeaseManagerConfig.spec (GF := GF) (hG := hG))
    (wp_newObj : newObj.spec (GF := GF) (hG := hG))
    (wp_Encode : runtime.Encode.spec (GF := GF) (hG := hG))
    (wp_cEncode : codec.Encode.spec (GF := GF) (hG := hG))
    (wp_Upd : versioner.UpdateObject.spec (GF := GF) (hG := hG))
    (wp_Prep : versioner.PrepareObjectForStorage.spec (GF := GF) (hG := hG))
    (wp_ORV : versioner.ObjectResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Parse : versioner.ParseResourceVersion.spec (GF := GF) (hG := hG))
    (wp_From : identity.TransformFromStorage.spec (GF := GF) (hG := hG))
    (wp_To : identity.TransformToStorage.spec (GF := GF) (hG := hG))
    (wp_Dec : decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_SetZero : runtime.SetZeroValue.spec (GF := GF) (hG := hG))
    (wp_UID : Obj.GetUID.spec (GF := GF) (hG := hG))
    (wp_RV : Obj.GetResourceVersion.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG))
    (hne : mvcc.api.names_nonempty.law) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS EK RT SC ST VA N id ctxs boot clients ops Hbf Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms hAs
    hse Hty H0 H31 Hops Hmul
  have hcon := driver_contractOk wp_Encode wp_cEncode wp_Upd wp_Prep wp_ORV wp_Parse wp_From wp_To
    wp_Dec wp_SetZero wp_UID wp_RV (driverSpec_tyOk Hty)
  wp_start as ⟨Hstart, Htok, #Hprem⟩
  -- (hub step 7) the client address's listen right, out of the member's start bundle (to `Serve`)
  icases etcdstart.memberStartRes_client _ _ _ rfl $$ Hstart with ⟨Haddr, Hstart⟩
  iunfold premises at Hprem
  iunfold etcdstart.premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := etcdstart.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (k8setcd3Dir id) go!"k8setcd3" go!"k8setcd3"
      (etcdstart.urls1 go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896") id cfgOk urlsOk
      (fun _ h => h)
      (fun _ h => h) $$ Hboot
  ihave #Hcom : etcdstart.commonPremises (GF := GF) $$ []
  · iunfold etcdstart.commonPremises; iframe #
  -- `context`'s `closedchan`, from its package's fact
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  -- the imports' package facts
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Psrv : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver $$ []
  · iPkgInit
  ihave #Pv3 : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg %Hlg
  (try wp_auto)
  -- the ghost state `NewServer` takes (`alloc1`)
  have hblen0 : boot.length = 1 := by rw [Hbf.boot.1]; rfl
  imod (etcdstart.alloc1_false hne id ctxs boot Hbf.idLow Hbf.boot Hbf.cc Hbf.urls (k8setcd3Dir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hrule, hboot, hγn1, hγn2, hlog, -⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("k8setcd3", "127.0.0.1:23906", clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (k8setcd3Dir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  -- (hub step 7) no peer address: the start bundle is the fresh bundle at the network `γn`
  ihave Hfresh := etcdstart.memberStartRes_fresh _ _ γn rfl $$ Hstart
  wp_apply (wp_StartServer N go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896" lg (LogEntry.toEntries boot 0) ctxs
      (k8setcd3Dir id) id γ ρ E₀ Φs γn .none Htb Hrb48 HrbN HwbN hvs
      hrule hboot hblen hγn1 hγn2 Hdirok
      (by simp [k8setcd3Dir, etcdstart.dir1, dirOne]) (rafthttp.bootCfg_dirOne id _) (by decide) Hlg Hck Haf Hbuq Hdbo) $$ [Htok Hmb Hfresh]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup, -⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  icases etcdstart.memberUp_served _ _ _ _ _ _ _ $$ Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd,
    #Hsf, Hgo, Hlg3, Hbemu, HWR, ⟨Hlts, Hlgs, Hrds, Hsts, Hrslots, Hbms⟩, -, -⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`: (D29) the member never refuses (authentication off, a voter, the
  -- members' axiom), and etcd's KV calls registered at the address
  haveI := Hms
  ihave ⟨%HsvOff, #HreqM, #HrdM, #Hlb⟩ := etcdstart.serveViews_off srv E { ρ with wait := γw } ρ.rd
    $$ []
  · iframe #
  wp_apply (wp_Serve srv go!"127.0.0.1:23896" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid _ => iprop(etcdstart.etcdKVAt go!"127.0.0.1:23896" E { ρ with wait := γw } ρ.rd cid mid ∗
        ⌜noRefusalAt go!"127.0.0.1:23896"⌝)))
    $$ [Haddr Hlg3 Hbemu Hgo HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [HElg]; exact Hlg, HEtr, HEw, Hms, Hbuq, HsvOff.2⟩
    iintro %gs %lis %cid %mid %R Hg
    rw [HsvOff.1]
    ihave Hg := etcdstart.grpcUpM_false _ _ _ _ _ _ _ _ _ _ $$ Hg
    ihave ⟨Hg, %Hnr⟩ := etcdstart.grpcUp_noRefusal srv E { ρ with wait := γw } ρ.rd gs lis
      go!"127.0.0.1:23896" cid mid R HEo $$ [Hg]
    · iframe; iframe #
    imod (etcdstart.kv_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23896" cid mid R Hrb48 Hrf rfl)
      $$ [Hg Hlts Hlgs Hrds Hsts Hrslots Hbms] with ⟨Hserv, #Hkv⟩
    · unfold etcdstart.kvServeStocks
      iframe; iframe #
    imodintro
    iframe Hserv Hkv
    ipureintro; exact Hnr
  icases Hs with (%Hserr | ⟨%Hserr, %cid, %mid, %R, #Hkv, %Hnr⟩)
  · cases serr with
    | nil => exact absurd rfl Hserr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hserr
  wp_auto
  iunfold etcdstart.etcdKVAt at Hkv
  icases Hkv with ⟨#HPut, #HRange, #HDel, #HTxn, #HCmp⟩
  -- `kubernetes.New(Config{Endpoints: {clientAddr}, Logger: lg, MaxUnaryRetries: 1})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  ihave #Pkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  let V : client.WEnv GF := EtcdGrove.client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"127.0.0.1:23896" [] null null [] null default
  haveI : ThreadBoundLe GF (2 ^ 28) := ⟨Htb⟩
  wp_apply (wp_kNew _ [go!"127.0.0.1:23896"] V (fun _ => iprop(True))) $$ [] as %kc %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact plainEndpoints_singleton _ (by unfold plainEndpoint; decide)
      · simp [Hlg]
    iapply clientAuthPre_anon; rfl
  icases Hcl with (⟨%Hcerr, %cl, #Hkc, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · cases cerr with
    | nil => exact absurd rfl Hcfail
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  -- (D29) a write sent at most once: the member is refusal-free
  ihave #Hone' : client.clientWriteOnce (GF := GF) cl [go!"127.0.0.1:23896"] $$ []
  · iunfold client.clientWriteOnce; ipureintro
    intro a ha; simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    subst ha; exact Hnr
  -- the one member, and its KV specs
  let x : client.SrvAt GF := ⟨go!"127.0.0.1:23896", E, ρ.rd, cid, mid⟩
  ihave #Hreg1 : client.kvRegsAt x $$ []
  · iunfold client.kvRegsAt
    iframe #
  -- the seeding, from the server's start state (`σb`: no key, revision `1`)
  have hboot0 : kvModelSt ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)) = σb := by
    have h : kvModel ρ.rd.kv (bootEntries (LogEntry.toEntries boot 0)) = [[], []] := by
      unfold kvModel
      rw [linkv.kvRaftOf_boot _ _ _ (fun _ _ => True) [id] (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog]
    rw [kvModelSt_boot _ (fun _ _ => True) _ (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), h]; rfl
  imod (seedInv_alloc ρ.rd.kv σb ⊤) $$ [Hetcd] with ⟨%γs, #Hsi, Hs⟩
  · rw [← hboot0]; iexact Hetcd
  ihave #Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply (wp_seed cl x _ γs hAs) $$ [Hs] as %st0 %ok Hsd
  · iframe #
    iframe Hs
  icases Hsd with (%Hok | ⟨%Hok, Hs, #Hst0⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  wp_auto
  imod (seedInv_cancel γs ρ.rd.kv σs2) $$ [Hs] with Hetcd
  · iframe #
    iframe Hs
  imod (histAuth_seed (GF := GF)) with ⟨%γh, Hhist, #Hsr⟩
  -- `etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix, ...)`; the
  -- conversion to `runtime.Codec` (`type Codec Serializer`) unfolds two named types
  haveI : go.UnderlyingEq k8s_io.apimachinery.pkg.runtime.Codec.ty
      k8s_io.apimachinery.pkg.runtime.Serializer.underlying :=
    ⟨(go.UnderlyingDirectedEq.underlying_unfold (t := k8s_io.apimachinery.pkg.runtime.Codec.ty)).trans
      go.UnderlyingDirectedEq.underlying_unfold⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_lmc as %lmc -
  (try wp_auto)
  ihave #Hctx := client_ctx_field cl [go!"127.0.0.1:23896"] V $$ [Hnc]
  · iexact Hnc
  ihave #Hpr : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apimachinery.pkg.runtime $$ []
  · iPkgInit
  ihave #Hpd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 $$ []
  · iPkgInit
  ihave #Hcon := hcon $$ [Hpr Hpd]
  · isplitl; iexact Hpr; iexact Hpd
  have e1 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.codec) = codecI := rfl
  have e2 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.identity.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.identity) =
      GoInterface.ok identityI := rfl
  have e3 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.decoder) =
      GoInterface.ok decoderI := rfl
  have e4 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.versioner) =
      GoInterface.ok versionerI := rfl
  rw [e1, e2, e3, e4]
  have hpc : path.PathCleanAbs go!"/registry" := by unfold path.PathCleanAbs; decide
  wp_apply (wp_sNew DObj driverSpec kc cl [x] V γh _ codecI _ func.nil func.nil go!"/registry"
      go!"/objs" ⟨[], go!"objs"⟩ versionerI identityI decoderI lmc hpc (by decide) (by decide))
    as %sp %err Hnew
  · simp only [List.map]
    iframe #
    isplitr
    · iapply BigSepL.bigSepL_nil.2; itrivial
    imodintro
    iintro %Φ' HΦ'
    wp_apply wp_newObj as %o %ho
    iapply HΦ'
    ipureintro; exact ho
  icases Hnew with ⟨%Herr, %mt, %lt, #Hstore⟩
  subst Herr
  wp_auto
  -- the driver's invariant at the seeded state, and `Check`
  let c : k8s.StoreCfg GF DObj :=
    { S := driverSpec, codec := codecI, vi := versionerI, ti := identityI, di := decoderI,
      pathPrefix := go!"/registry", resourcePrefix := go!"/objs", gr := ⟨[], go!"objs"⟩, kc := kc,
      cl := cl, ms := [x], V := V, mt := mt, lt := lt, γh := γh }
  imod (kInv_seed ρ.rd.kv c rfl rfl ⊤) $$ [Hetcd Hhist] with ⟨%γ, #Hinv, Hks⟩
  · iframe
    iexact Hsr
  wp_apply (wp_Check γ sp c g0s st0 clients ops (W64 0) rfl rfl rfl hAs hse (by simp [c])
      (by omega) H0 H31 Hops Hmul (by rw [g0s_items]; simp)) $$ [Hks] as %r %hr
  · iframe #
    iframe Hks
    iapply BigSepL.bigSepL_nil.2; itrivial
  have hok : r = go!"Ok" := hr.2 (by decide)
  subst hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
