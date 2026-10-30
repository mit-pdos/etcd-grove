/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8setcd3/Main.lean` (stage 6g of
`notes/k8s-etcd3-plan.md`). Lean-first (no Rocq counterpart).

As `linkvtxn/Main.lean` to the client (the shared start, `common.StartServer` and `common.Serve`,
at `k8setcd3`'s configuration), then: `kubernetes.New` (a write sent at most once: the member is refusal-free, D29), the seeding (`seedInv` over etcd's
start state, `seed`, cancelled at the seeded state), the store's history at the seeded state
(`histAuth_seed`), `etcd3.New` (the driver's contract), the instance's invariant at the seeded
state (`kInv_seed`) and `Check(s, st0, clients, ops, 0)`, which returns `Ok` (`timeout = 0`), so the
panic on `Illegal` is not taken. Every step's error ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.seed
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8setcd3.newObj
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewDefaultLeaseManagerConfig
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Boot
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Contract
public import Spec.go_uber_org.zap.NewNop
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.StartServer
public import Spec.github_com.mit_pdos.etcd_grove.examples.common.Serve
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Alloc
public import Proof.github_com.mit_pdos.etcd_grove.examples.common.Served
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
namespace k8setcd3

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]

set_option maxHeartbeats 3200000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_StartServer : common.StartServer.spec (GF := GF) (hG := hG))
    (wp_Serve : common.Serve.spec (GF := GF) (hG := hG))
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
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS EK RT SC ST VA N id ctxs boot clients ops Hbf Htb Hrb48 HrbN Hck Haf Hbuq Hdbo Hms hAs
    hse Hty H0 H31 Hops Hmul
  have hcon := driver_contractOk wp_Encode wp_cEncode wp_Upd wp_Prep wp_ORV wp_Parse wp_From wp_To
    wp_Dec wp_SetZero (driverSpec_tyOk Hty)
  wp_start as ⟨Haddr, Htok, #Hprem⟩
  iunfold premises at Hprem
  icases Hprem with ⟨#Hboot, #Hmarsh, #Hzap, #Hsetlg, #Htd, #Hns, #Htk, #Hstop, #Hnrl⟩
  -- `Main`'s premises in the shared start's form
  ihave #Hb := common.bootPremise_of N [id] (LogEntry.toEntries boot 0) ctxs (k8setcd3Dir id) go!"k8setcd3" go!"k8setcd3"
      (common.urls1 go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896") id cfgOk urlsOk
      (fun _ h => by obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h; exact ⟨h1, by rw [h2]; rfl, h3, h4, h5, h6⟩)
      (fun _ h => by obtain ⟨h1, h2, h3, h4⟩ := h; exact ⟨h1, h2, h3, h4⟩) $$ Hboot
  ihave #Hcom : common.commonPremises (GF := GF) $$ []
  · iunfold common.commonPremises; iframe #
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
  imod (common.alloc1 id ctxs boot Hbf.idLow Hbf.boot Hbf.cc (k8setcd3Dir id) (dirOne_member id _)
      (by omega) (by omega)) $$ Hmarsh
    with ⟨%γ, %ρ, %E₀, %Φs, %γn, %Hal, Hmb, #Hnet, Hetcd⟩
  obtain ⟨hvs, hdyn, hboot, hγn1, hγn2, hlog⟩ := Hal
  have hblen : (LogEntry.toEntries boot 0).length ≤ 2 ^ 60 := by
    simp [LogEntry.toEntries, hblen0]
  -- `StartServer("k8setcd3", "127.0.0.1:23906", clientAddr, lg)`
  -- (2026-10-24, rafthttp stage 6d) the one-member directory is well formed
  have Hdirok : netDirOk (k8setcd3Dir id) :=
    dirOne_ok id _ (by intro h; apply Hbf.idLow; rw [h]; decide) (by decide)
  wp_apply (wp_StartServer N go!"k8setcd3" go!"127.0.0.1:23906" go!"127.0.0.1:23896" lg (LogEntry.toEntries boot 0) ctxs
      (k8setcd3Dir id) id γ ρ E₀ Φs γn Htb Hrb48 HrbN hvs
      hdyn hboot hblen hγn1 hγn2 Hdirok
      (by simp [k8setcd3Dir, dirOne]) Hlg Hck Haf Hbuq Hdbo) $$ [Htok Hmb]
    as %srv %err Hr
  · iframe; iframe #
  icases Hr with (⟨%Herr, -⟩ | ⟨%Herr, Hup⟩)
  · cases err with
    | nil => exact absurd rfl Herr
    | ok ei => ?_
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Herr
  wp_auto
  iunfold common.memberUp at Hup
  icases Hup with ⟨%E, %cfg, %γw, %HEc, #Hreq, #Hrd, Hgo, Hlg3, Hrslots, #Hwb, #Hsf, Hwpi,
    Hbemu, Hlts, Hlgs, Hrds, Hsts, Hbms, -, HWR⟩
  obtain ⟨HEa, HEo, HElg, HEtr, HEw⟩ := HEc
  -- `Serve(s, clientAddr)`: (D29) the member never refuses (authentication off, a voter, the
  -- members' axiom), and etcd's KV calls registered at the address
  haveI := Hms
  wp_apply (wp_Serve srv go!"127.0.0.1:23896" E { ρ with wait := γw } ρ.rd cfg
      (fun cid mid _ => iprop(common.etcdKVAt go!"127.0.0.1:23896" E { ρ with wait := γw } ρ.rd cid mid ∗
        ⌜noRefusalAt go!"127.0.0.1:23896"⌝))
      (by rw [HElg]; exact Hlg) HEtr HEw Hms Hbuq)
    $$ [Haddr Hlg3 Hbemu Hgo Hwpi HWR Hlts Hlgs Hrds Hsts Hrslots Hbms] as %serr Hs
  · iframe; iframe #
    iintro %gs %lis %cid %mid %R Hg
    ihave ⟨Hg, %Hnr⟩ := common.grpcUp_noRefusal srv E { ρ with wait := γw } ρ.rd gs lis
      go!"127.0.0.1:23896" cid mid R HEo $$ [Hg]
    · iframe; iframe #
    imod (common.kv_served srv E { ρ with wait := γw } ρ.rd gs lis go!"127.0.0.1:23896" cid mid R Hrb48)
      $$ [Hg Hlts Hlgs Hrds Hsts Hrslots Hbms] with ⟨Hserv, #Hkv⟩
    · iframe; iframe #
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
  iunfold common.etcdKVAt at Hkv
  icases Hkv with ⟨#HPut, #HRange, #HDel, #HTxn⟩
  -- `kubernetes.New(Config{Endpoints: {clientAddr}, Logger: lg, MaxUnaryRetries: 1})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  ihave #Pkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  let V : client.WEnv GF := EtcdGrove.client.srvWEnv R go!"127.0.0.1:23896" [] null null [] null default
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
    isplitr
    · iapply clientAuthPre_anon; rfl
    ipureintro; exact Htb
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
    simp only [github_com.anishathalye.porcupine.Unknown]
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  wp_auto
  imod (seedInv_cancel γs ρ.rd.kv σs2) $$ [Hs] with Hetcd
  · iframe #
    iframe Hs
  imod (histAuth_seed (GF := GF)) with ⟨%γh, Hhist⟩
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
  ihave #Hpd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8setcd3 $$ []
  · iPkgInit
  ihave #Hcon := hcon $$ [Hpr Hpd]
  · isplitl; iexact Hpr; iexact Hpd
  have e1 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.codec) = codecI := rfl
  have e2 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.identity) =
      GoInterface.ok identityI := rfl
  have e3 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.decoder) =
      GoInterface.ok decoderI := rfl
  have e4 : interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner.ty #(zero_val github_com.mit_pdos.etcd_grove.examples.k8setcd3.versioner) =
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

end k8setcd3
end EtcdGrove
end Perennial
