/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainPartition.lean` (step 2 of
"k8s etcd3 over cluster3" in `notes/k8s-etcd3-plan.md`, 2026-11-07). Lean-first (no Rocq
counterpart).

`MainCluster`'s proof (`MainCluster.lean`), keeping what it drops of the cluster's start: each
member's place in the network (`etcdstart.srvPeerCtl`) and each bridge owned
(`bridge.ownBridge … false`), from `cluster3.clusterAt`. Once the store is made, they go to the
forked `cluster3.Partitioner` (its `PeerPausable` premise by `inferInstance`), as the k8s
compactor's `MainPartition`; the rest, the seeding, the store and `Check`, is `MainCluster`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.clusterConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.seed
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.noStreaming
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj
public import Spec.go_etcd_io.etcd.client.v3.kubernetes.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewDefaultLeaseManagerConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Partitioner
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Main

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
set_option maxRecDepth 8192 in
theorem MainPartition.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_clusterConfig : clusterConfig.spec (GF := GF) (hG := hG))
    (wp_StartCluster : cluster3.StartCluster.spec (GF := GF) (hG := hG))
    (wp_Partitioner : cluster3.Partitioner.spec (GF := GF) (hG := hG))
    (wp_kNew : kubernetes.New.spec (GF := GF) (hG := hG))
    (wp_seed : seed.spec (GF := GF) (hG := hG))
    (wp_noStreaming : noStreaming.spec (GF := GF) (hG := hG))
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
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    MainPartition.spec (GF := GF) (hG := hG) := by
  intro CS EK RT SC ST VA N id₁ id₂ id₃ ps ctxs boot clients ops sched steps ThB RcB RcN Hbf HwbN Hck
    Haf Hbuq Hrf Hdbo Hms hAs hse Hty H0 H31 Hops Hmul
  have Htb := ThreadBoundLe.le (GF := GF) (2 ^ 28)
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  have HrbN := ReceiptBoundLe.le (GF := GF) (N + 1)
  have hcon := driver_contractOk wp_Encode wp_cEncode wp_Upd wp_Prep wp_ORV wp_Parse wp_From wp_To
    wp_Dec wp_SetZero wp_UID wp_RV (driverSpec_tyOk Hty)
  wp_start as ⟨Hstart, #Hsched, Htok, #Hprem⟩
  -- the imports' package facts
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Ppb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
  · iPkgInit
  ihave #Pc3 : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.cluster3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  ihave %Hlg := zapLoggerOk_ne_null lg $$ Hlgz
  (try wp_auto)
  -- `cfg := clusterConfig()`
  wp_apply wp_clusterConfig
  (try wp_auto)
  -- `cluster3.StartCluster(cfg, lg)`, compaction off
  wp_apply (wp_StartCluster clusterCfg N id₁ id₂ id₃ ps ctxs boot lg false .none clusterCfg_ok Hbf
      Htb Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms lease.runCfg_none (by decide)
      (fun h => absurd rfl h))
    $$ [Hstart Htok] as %srvs %brs %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    (try wp_auto)
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  (try wp_auto)
  iunfold cluster3.clusterUp at Hup
  icases Hup with ⟨%γ, %γn, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %cid₁, %cid₂, %cid₃, %mid₁, %mid₂,
    %mid₃, %R₁, %R₂, %R₃, %s₁, %s₂, %s₃, %br₁, %br₂, %br₃, Hcl⟩
  iunfold cluster3.clusterAt at Hcl
  icases Hcl with ⟨#Hsrvs, #Hbrs, #Hm₁, #Hm₂, #Hm₃, Hctl₁, Hctl₂, Hctl₃, Hob₁, Hob₂, Hob₃, Hetcd,
    %Hal⟩
  obtain ⟨hst₂, hst₃, -, -⟩ := Hal
  isimp only [cluster3.memberAt_none] at Hm₁ Hm₂ Hm₃
  icases Hm₁ with ⟨#Hfw₁, -, #HPut₁, #HRange₁, #HDel₁, #HTxn₁, #HCmp₁, %Hnr₁, -, -, -, -, %Hp₁⟩
  icases Hm₂ with ⟨#Hfw₂, -, #HPut₂, #HRange₂, #HDel₂, #HTxn₂, #HCmp₂, %Hnr₂, -, -, -, -, -⟩
  icases Hm₃ with ⟨#Hfw₃, -, #HPut₃, #HRange₃, #HDel₃, #HTxn₃, #HCmp₃, %Hnr₃, -, -, -, -, -⟩
  obtain ⟨-, -, -, hlog₁, -⟩ := Hp₁
  -- the members at their bridges: their registrations there, refusal-free (D29)
  let ms : List (client.SrvAt GF) :=
    [⟨clusterCfg.Bridge1', E₁, ρ₁.rd, cid₁, mid₁⟩, ⟨clusterCfg.Bridge2', E₂, ρ₂.rd, cid₂, mid₂⟩,
      ⟨clusterCfg.Bridge3', E₃, ρ₃.rd, cid₃, mid₃⟩]
  have hsame : ∀ x ∈ ms, kvSame x.γr.kv ρ₁.rd.kv := by
    intro x hx
    simp only [ms, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact kvSame_refl _
    · exact hst₂
    · exact hst₃
  ihave #Hregs : ([∗list] x ∈ ms, client.kvRegsAt x) $$ []
  · iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold client.kvRegsAt
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HPut₁]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpcMd_forwards $$ [Hfw₁ HRange₁]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HDel₁]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HTxn₁]; iframe #
      iapply cluster3.isGrpcRpc_forwards $$ [Hfw₁ HCmp₁]; iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold client.kvRegsAt
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HPut₂]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpcMd_forwards $$ [Hfw₂ HRange₂]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HDel₂]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HTxn₂]; iframe #
      iapply cluster3.isGrpcRpc_forwards $$ [Hfw₂ HCmp₂]; iframe #
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iunfold client.kvRegsAt
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HPut₃]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpcMd_forwards $$ [Hfw₃ HRange₃]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HDel₃]; iframe #
      isplitr
      · iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HTxn₃]; iframe #
      iapply cluster3.isGrpcRpc_forwards $$ [Hfw₃ HCmp₃]; iframe #
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ihave %Hb₁' : ⌜noRefusalAt clusterCfg.Bridge1'⌝ $$ []
  · iunfold cluster3.forwards at Hfw₁; icases Hfw₁ with ⟨-, %Hf⟩; ipureintro; exact Hf Hnr₁
  ihave %Hb₂' : ⌜noRefusalAt clusterCfg.Bridge2'⌝ $$ []
  · iunfold cluster3.forwards at Hfw₂; icases Hfw₂ with ⟨-, %Hf⟩; ipureintro; exact Hf Hnr₂
  ihave %Hb₃' : ⌜noRefusalAt clusterCfg.Bridge3'⌝ $$ []
  · iunfold cluster3.forwards at Hfw₃; icases Hfw₃ with ⟨-, %Hf⟩; ipureintro; exact Hf Hnr₃
  have hnr : ∀ a ∈ cluster3.bridges clusterCfg, noRefusalAt a := by
    intro a ha
    simp only [cluster3.bridges, List.mem_cons, List.not_mem_nil, _root_.or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact Hb₁'
    · exact Hb₂'
    · exact Hb₃'
  -- `kubernetes.New(Config{Endpoints: {the three bridges}, DialTimeout, keepalive, Logger: lg})`
  wp_apply wp_slice_literal
  try (isplitr; (ipureintro; rfl))
  iintro %eps ⟨Heps, -⟩
  simp only [go.arrayLiteralSize, List.foldl]
  (try wp_auto)
  imod ownSlice_persist _ _ _ $$ Heps with #Heps
  ihave #Pkc : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3.kubernetes $$ []
  · iPkgInit
  let V : client.WEnv GF :=
    EtcdGrove.client.srvWEnv R₁ (etcdstart.srvWOf E₁ ρ₁.rd false) ρ₁.rd clusterCfg.Bridge1' [] null null [] null default
  wp_apply (wp_kNew _ [clusterCfg.Bridge1', clusterCfg.Bridge2', clusterCfg.Bridge3'] V (fun _ => iprop(True))) $$ []
    as %kc %cerr Hcl
  · iframe #
    iunfold clientCfgOk
    simp only
    iframe #
    isplitr
    · isplitr
      · iExactEq Heps; rfl
      isplitr
      · iapply ownSlice_nil
      ipureintro
      refine ⟨?_, ?_⟩
      · exact clusterCfg_ok.plainBridges
      · simp [Hlg]
    iapply clientAuthPre_anon; rfl
  icases Hcl with (⟨%Hcerr, %cl, #Hkc, #Hnc, -⟩ | %Hcfail)
  rotate_left
  · cases cerr with
    | nil => exact absurd rfl Hcfail
    | ok ei => ?_
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hcerr
  wp_auto
  -- (D29) a write sent at most once: every bridge is refusal-free
  ihave #Hone : client.clientWriteOnce (GF := GF) cl
      [clusterCfg.Bridge1', clusterCfg.Bridge2', clusterCfg.Bridge3'] $$ []
  · iunfold client.clientWriteOnce; ipureintro; exact hnr
  -- the seeding, from the cluster's start state (`σb`: no key, revision `1`), at every member
  have hboot0 : kvModelSt ρ₁.rd.kv (bootEntries (LogEntry.toEntries boot 0)) = σb := by
    rw [kvModelSt_boot _ (fun _ _ => True) _ (LogEntry.toEntries boot 0)
      (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
      etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog₁]
    rfl
  imod (seedInv_alloc ρ₁.rd.kv σb ⊤) $$ [Hetcd] with ⟨%γs, #Hsi, Hs⟩
  · rw [← hboot0]; iexact Hetcd
  ihave #Hsis := seedInvs_of_same γs ρ₁.rd.kv ms hsame $$ Hsi
  ihave #Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply (wp_seed cl ms V γs hAs (by simp [ms])) $$ [Hs] as %st0 %h0 %ok Hsd
  · simp only [ms, List.map_cons, List.map_nil]
    iframe #
    iframe Hs
  icases Hsd with (%Hok | ⟨%Hok, Hs, #Hst0, %hs, #Hh0, #Hhs⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  wp_auto
  wp_apply wp_noStreaming as %b Hb
  cases b with
  | false =>
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  | true =>
  ihave #Hrs : (k8s.rangeStreamOff : IProp GF) $$ [Hb]
  · iExactEq Hb; rfl
  wp_auto
  iclear Hsis
  imod (seedInv_cancel γs ρ₁.rd.kv σs2) $$ [Hs] with Hetcd
  · iframe #
    iframe Hs
  imod (histAuth_seed (GF := GF)) with ⟨%γh, Hhist, #Hsr⟩
  -- `etcd3.New(kc, noCompactor{}, codec{}, newObj, nil, nil, Prefix, ResourcePrefix, ...)`, as
  -- `Main`'s, over the three members
  haveI : go.UnderlyingEq k8s_io.apimachinery.pkg.runtime.Codec.ty
      k8s_io.apimachinery.pkg.runtime.Serializer.underlying :=
    ⟨(go.UnderlyingDirectedEq.underlying_unfold (t := k8s_io.apimachinery.pkg.runtime.Codec.ty)).trans
      go.UnderlyingDirectedEq.underlying_unfold⟩
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_lmc as %lmc -
  (try wp_auto)
  ihave #Hctx := client_ctx_field cl [clusterCfg.Bridge1', clusterCfg.Bridge2', clusterCfg.Bridge3'] V $$ [Hnc]
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
  wp_apply (wp_sNew DObj driverSpec kc cl ms V γh _ codecI _ func.nil func.nil go!"/registry"
      go!"/objs" ⟨[], go!"objs"⟩ versionerI identityI decoderI lmc hpc (by decide) (by decide)
      (by rfl) (by rfl) (by omega) (by rfl))
    as %sp %err Hnew
  · simp only [ms, List.map_cons, List.map_nil]
    iframe #
    imodintro
    iintro %Φ' HΦ'
    wp_apply wp_newObj as %o %ho
    iapply HΦ'
    ipureintro; exact ho
  icases Hnew with ⟨%Herr, %mt, %lt, #Hstore⟩
  subst Herr
  wp_auto
  -- `go cluster3.Partitioner(srvs, brs, sched)`: every member's place in the network, every
  -- bridge owned (as the k8s compactor's `MainPartition`)
  ihave Hmem : ([∗list] s ∈ [s₁, s₂, s₃], ∃ id : w64, etcdstart.srvPeerCtl γn s id)
    $$ [Hctl₁ Hctl₂ Hctl₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₁]
    · iexists id₁; iexact Hctl₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₂]
    · iexists id₂; iexact Hctl₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ s => iprop(∃ id : w64, etcdstart.srvPeerCtl (GF := GF) γn s id))).2
    isplitl [Hctl₃]
    · iexists id₃; iexact Hctl₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  ihave Hobs : ([∗list] br ∈ [br₁, br₂, br₃], ∃ addr : GoString, bridge.ownBridge br addr false)
    $$ [Hob₁ Hob₂ Hob₃]
  · iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₁]
    · iexists clusterCfg.Client1'; iexact Hob₁
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₂]
    · iexists clusterCfg.Client2'; iexact Hob₂
    iapply (BigSepL.bigSepL_cons
      (Φ := fun _ br => iprop(∃ addr : GoString, bridge.ownBridge (GF := GF) br addr false))).2
    isplitl [Hob₃]
    · iexists clusterCfg.Client3'; iexact Hob₃
    iapply BigSepL.bigSepL_nil.2
    itrivial
  wp_apply wp_fork $$ [Hobs Hmem]
  · wp_apply (wp_Partitioner inferInstance γn _ _ sched [s₁, s₂, s₃] [br₁, br₂, br₃] steps)
      $$ [Hobs Hmem]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- the driver's invariant at the seeded state, at every member, and `Check`
  let c : k8s.StoreCfg GF DObj :=
    { S := driverSpec, codec := codecI, vi := versionerI, ti := identityI, di := decoderI,
      pathPrefix := go!"/registry", resourcePrefix := go!"/objs", gr := ⟨[], go!"objs"⟩, kc := kc,
      cl := cl, ms := ms, V := V, mt := mt, lt := lt, γh := γh }
  imod (kInv_seed ρ₁.rd.kv c rfl rfl ⊤) $$ [Hetcd Hhist] with ⟨%γ, #Hinv, Hks⟩
  · iframe
    iexact Hsr
  ihave #Hinvs := kInvs_of_same γ c g0s ρ₁.rd.kv ms hsame $$ Hinv
  wp_apply (wp_Check γ sp c g0s st0 h0 hs clients ops (W64 0) rfl rfl rfl rfl rfl hAs hse
      (by omega)
      (by intro y hy; apply hnr; simp only [c, ms, List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
          rcases hy with rfl | rfl | rfl <;> simp [cluster3.bridges])
      (by simp [c, ms]) (by omega) H0 H31 Hops Hmul
      (by rw [g0s_len, σs2_rev]; show st3.items.length + 3 < _; rw [st3_items]; simp))
    $$ [Hks] as %r %hr
  · iframe #
    iframe Hks
    isplitr
    · iExactEq Hst0; rfl
    iExactEq Hhs; rfl
  have hok : r = go!"Ok" := hr.2 (by decide)
  subst hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
