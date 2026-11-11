/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/MainPartition.lean` (K6 of
`notes/k8s-compactor-plan.md`, step 5). Lean-first.

The cluster side as `examples/etcd/partition`'s `Main`/`MainWatch`, the compactor side as the
one-member `Main`'s. The cluster (`cluster3.StartCluster` at `clusterCfg`, in compaction mode: every
member's server `cmp = true`, the KV names at retention `0`), with the example's invariant allocated
at its start store (no key; `cinv_alloc`). Each member's watch facts (`memberWatch_of_cinv`: the
store's fact for watches, no revision writes a key twice, `noDupKeys_of_one` from the member's KV
facts and the invariant's `oneChangeAu`), the members' `Watch` streams at the bridges, so the
watcher's facts at every connection to the bridges (`cluster3.watchEnv_conn`). The members at their
bridges (`ms`): their registrations through the bridges (`cluster3.isGrpcRpc_forwards`), the
bridges refusal-free (D29), their starts (`srvStart_alloc`). Then the writer's client and its
readiness check, the partitioner forked on the schedule, the writer forked, and the five API
servers, each with its own client of the three bridges (its KV handle, `isKv_of_newClient` over the
three members, and its watcher, `isNewClient_watcher_of`), forked under a wait group that
`MainPartition` waits for; the three bridges claimed for the cluster from the registry's authority
(`epOf_alloc`), for the API servers sharing the process's compactor.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.clusterConfig
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ready
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.StartCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.NewClient
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Partitioner
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.WatchEnv
public import Spec.go_uber_org.zap.NewNop
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.KvOfNew
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Perennial.Proof.sync.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.NoDup
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Main

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_compactor

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.compactor.Assumptions]

/-- **A member's watch facts in the compacting cluster** (`cluster3.memberWatch`): its read view,
its watch server, its names the history's, and the store's fact for watches (no revision writes a
key twice: `noDupKeys_of_one`, from the member's KV facts and the invariant's `oneChangeAu`). -/
theorem memberWatch_of_cinv (γr : ReadNames) (s : Loc) (E : apply.AEnv GF) (ρ : ReqNames)
    (R : v3rpc.WSrv GF) (γc : CNames) (hR : R.E = E) (hm : v3rpc.memberOf γr.raft γr.kv ρ.rd)
    (hst : kvSame ρ.rd.kv γr.kv) (hlog : ρ.rd.kv.log0 = [[], []])
    (hrb : receiptBound GF ≤ 2 ^ 62) :
    isServerRead s E ρ.rd ∗ (∃ pw : Loc, v3rpc.isWatchServer pw R) ∗
      client.srvWLaws (etcdstart.srvWOf E ρ.rd false) ∗ cinv γr.kv γc ⊢
      cluster3.memberWatch γr s E ρ R := by
  iintro ⟨#Hrd, ⟨%pw, #Hws⟩, #Hwl, #Hinv⟩
  iunfold cluster3.memberWatch
  isplitr
  · iexact Hrd
  isplitr
  · iexists pw; iexact Hws
  isplitr
  · ipureintro; exact ⟨hR, hm, hst⟩
  iframe Hwl
  subst hR
  -- (R9) the watch condition: no revision writes a key twice (each has one change)
  iapply (srvOnce_of_one (client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"" [] null null go!"" null γr.kv) γr.kv rfl)
  isplitr
  · iapply client.srvKVFacts_of_off (client.srvWEnv R (etcdstart.srvWOf R.E ρ.rd false) ρ.rd go!"" [] null null go!"" null γr.kv) ρ.rd hst hlog hrb rfl rfl
    iapply srvKVInvs_of_read s R.E ρ.rd $$ Hrd
  iapply oneChangeAu $$ Hinv

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
theorem MainPartition.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_clusterConfig : clusterConfig.spec (GF := GF) (hG := hG))
    (wp_StartCluster : cluster3.StartCluster.spec (GF := GF) (hG := hG))
    (wp_NewClient : cluster3.NewClient.spec (GF := GF) (hG := hG))
    (wp_Partitioner : cluster3.Partitioner.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_ready : ready.spec (GF := GF) (hG := hG))
    (wp_writer : writer.spec (GF := GF) (hG := hG))
    (wp_apiserver : apiserver.spec (GF := GF) (hG := hG)) :
    MainPartition.spec (GF := GF) (hG := hG) := by
  intro CS CRE CEC N id₁ id₂ id₃ ps ctxs boot sched steps Hbf Htb Hrb48 HrbN HwbN Hck Haf Hbuq
    Hrf Hdbo Hms hAs
  wp_start as ⟨Hstart, #Hsched, Htok,
    #Hprem, Hreg⟩
  -- the imports' package facts
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs)
    iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Pcli : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.v3 $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
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
  -- `cluster3.StartCluster(cfg, lg)`, in compaction mode
  wp_apply (wp_StartCluster clusterCfg N id₁ id₂ id₃ ps ctxs boot lg true .none clusterCfg_ok Hbf Htb
      Hrb48 HrbN HwbN Hck Haf Hbuq Hrf Hdbo Hms lease.runCfg_none (by decide) (fun h => absurd rfl h))
    $$ [Hstart Htok] as %srvs %brs %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hok
  (try wp_auto)
  iunfold cluster3.clusterUp at Hup
  icases Hup with ⟨%γ, %γn, %ρ₁, %ρ₂, %ρ₃, %E₁, %E₂, %E₃, %cid₁, %cid₂, %cid₃, %mid₁, %mid₂,
    %mid₃, %R₁, %R₂, %R₃, %s₁, %s₂, %s₃, %br₁, %br₂, %br₃, Hcl⟩
  iunfold cluster3.clusterAt at Hcl
  icases Hcl with ⟨#Hsrvs, #Hbrs, #Hm₁, #Hm₂, #Hm₃, Hctl₁, Hctl₂, Hctl₃, Hob₁, Hob₂, Hob₃, Hetcd,
    %Hal⟩
  obtain ⟨hst₂, hst₃, hkc, hkr⟩ := Hal
  isimp only [cluster3.memberAt_none] at Hm₁ Hm₂ Hm₃
  icases Hm₁ with ⟨#Hfw₁, #Hrd₁, #HPut₁, #HRange₁, #HDel₁, #HTxn₁, #HCmp₁, %Hnr₁, #Hws₁,
    %HR₁, #Hwl₁, #Hstr₁, %Hp₁⟩
  icases Hm₂ with ⟨#Hfw₂, #Hrd₂, #HPut₂, #HRange₂, #HDel₂, #HTxn₂, #HCmp₂, %Hnr₂, #Hws₂,
    %HR₂, #Hwl₂, #Hstr₂, %Hp₂⟩
  icases Hm₃ with ⟨#Hfw₃, #Hrd₃, #HPut₃, #HRange₃, #HDel₃, #HTxn₃, #HCmp₃, %Hnr₃, #Hws₃,
    %HR₃, #Hwl₃, #Hstr₃, %Hp₃⟩
  obtain ⟨hr₁, hc₁, hch₁, hlog₁, -⟩ := Hp₁
  obtain ⟨hr₂, hc₂, hch₂, hlog₂, -⟩ := Hp₂
  obtain ⟨hr₃, hc₃, hch₃, hlog₃, -⟩ := Hp₃
  obtain ⟨r₁, hr₁⟩ := hr₁
  obtain ⟨r₂, hr₂⟩ := hr₂
  obtain ⟨r₃, hr₃⟩ := hr₃
  have hm₁ : v3rpc.memberOf ρ₁.rd.raft ρ₁.rd.kv ρ₁.rd :=
    v3rpc.memberOf_of_eq _ _ _ rfl rfl rfl rfl
  have hm₂ : v3rpc.memberOf ρ₁.rd.raft ρ₁.rd.kv ρ₂.rd :=
    ⟨by rw [hr₂, hr₁], hc₂.trans hc₁.symm, hch₂.trans hch₁.symm, hlog₂.trans hlog₁.symm⟩
  have hm₃ : v3rpc.memberOf ρ₁.rd.raft ρ₁.rd.kv ρ₃.rd :=
    ⟨by rw [hr₃, hr₁], hc₃.trans hc₁.symm, hch₃.trans hch₁.symm, hlog₃.trans hlog₁.symm⟩
  have hrb : receiptBound GF ≤ 2 ^ 62 := by omega
  have htb : threadBound GF ≤ 2 ^ 31 := by omega
  -- the example's invariant, at the cluster's start store (no key)
  have hboot0 : kvModelSt ρ₁.rd.kv (bootEntries (LogEntry.toEntries boot 0)) =
      kvStateOf [[], []] := by
    rw [kvModelSt_boot _ (fun _ _ => True) _ (LogEntry.toEntries boot 0)
      (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
      etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog₁]
  rw [hboot0] at *
  imod (cinv_alloc ρ₁.rd.kv ⊤) $$ Hetcd with ⟨%γc, #Hinv⟩
  -- each member's watch facts, and its `Watch` stream at its bridge
  ihave #Hmw₁ := memberWatch_of_cinv ρ₁.rd s₁ E₁ ρ₁ R₁ γc HR₁.2 hm₁ (kvSame_refl _) hlog₁ hrb
    $$ [Hrd₁ Hws₁ Hwl₁ Hinv]
  · iframe #
  ihave #Hmw₂ := memberWatch_of_cinv ρ₁.rd s₂ E₂ ρ₂ R₂ γc HR₂.2 hm₂ hst₂ hlog₂ hrb
    $$ [Hrd₂ Hws₂ Hwl₂ Hinv]
  · iframe #
  ihave #Hmw₃ := memberWatch_of_cinv ρ₁.rd s₃ E₃ ρ₃ R₃ γc HR₃.2 hm₃ hst₃ hlog₃ hrb
    $$ [Hrd₃ Hws₃ Hwl₃ Hinv]
  · iframe #
  ihave #Hb₁ := cluster3.isGrpcStream_forwards clusterCfg.Bridge1' clusterCfg.Client1' _ _ _
    $$ [Hfw₁ Hstr₁]
  · iframe #
  ihave #Hb₂ := cluster3.isGrpcStream_forwards clusterCfg.Bridge2' clusterCfg.Client2' _ _ _
    $$ [Hfw₂ Hstr₂]
  · iframe #
  ihave #Hb₃ := cluster3.isGrpcStream_forwards clusterCfg.Bridge3' clusterCfg.Client3' _ _ _
    $$ [Hfw₃ Hstr₃]
  · iframe #
  -- the watcher's facts at every connection to the bridges
  let V := cluster3.watchEnv clusterCfg R₁ R₂ R₃ (etcdstart.srvWOf E₁ ρ₁.rd false) (etcdstart.srvWOf E₂ ρ₂.rd false) (etcdstart.srvWOf E₃ ρ₃.rd false) ρ₁.rd go!"k"
  ihave #Hconn := cluster3.watchEnv_conn wp_ErrAny hAs clusterCfg clusterCfg_ok R₁ R₂ R₃ ρ₁.rd
    go!"k" (by decide) hlog₁ hrb s₁ s₂ s₃ E₁ E₂ E₃ ρ₁ ρ₂ ρ₃ HR₁.2 HR₂.2 HR₃.2
    $$ [Pcli Ppb Pctx Heo Hmw₁ Hmw₂ Hmw₃ Hb₁ Hb₂ Hb₃]
  · iframe #
  -- the members at their bridges: their registrations there, their starts, refusal-free (D29)
  let ms : List (client.SrvAt GF) :=
    [⟨clusterCfg.Bridge1', E₁, ρ₁.rd, cid₁, mid₁⟩, ⟨clusterCfg.Bridge2', E₂, ρ₂.rd, cid₂, mid₂⟩,
      ⟨clusterCfg.Bridge3', E₃, ρ₃.rd, cid₃, mid₃⟩]
  have hms : ms.map client.SrvAt.addr = cluster3.bridges clusterCfg := rfl
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
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
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
  -- the cluster's KV invariant (the read-side law, `apiserver`'s)
  ihave #Hinvs := srvKVInvs_of_read s₁ E₁ ρ₁.rd $$ Hrd₁
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#Hkvi, -⟩
  -- `wcli, err := cluster3.NewClient(cfg, lg)`
  wp_apply (wp_NewClient clusterCfg lg V clusterCfg_ok htb) as %wcl %werr Hwc
  · iframe #
  icases Hwc with (⟨%Hwerr, #Hwnc, -⟩ | %Hwfail)
  rotate_left
  · obtain ⟨Hwerr, -⟩ := Hwfail
    cases werr with
    | nil => exact absurd rfl Hwerr
    | ok ei => ?_
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hwerr
  (try wp_auto)
  -- `ready(wcli)`
  wp_apply (wp_ready wcl ms V) $$ [] as %b -
  · iframe #
    rw [hms]; iexact Hwnc
  cases b
  · (try wp_auto)
    iapply HΦ; itrivial
  (try wp_auto)
  -- the writer's client: refusal-free, its KV handle
  ihave #Hone1 : client.clientWriteOnce (GF := GF) wcl (cluster3.bridges clusterCfg) $$ []
  · iunfold client.clientWriteOnce; ipureintro; exact hnr
  imod (client.isKv_of_newClient wcl ms (cluster3.bridges clusterCfg) V ρ₁.rd.kv hms hsame hrb)
    $$ [Hwnc Hone1 Hregs] with ⟨%wapi, #Hwkvf, #Hwkv⟩
  · iframe #
  ihave #Hwko : k8s.clientKvOk (GF := GF) wcl ρ₁.rd.kv $$ []
  · iunfold k8s.clientKvOk; iexists wapi, false; iframe #
  -- `go cluster3.Partitioner(srvs, brs, sched)`: every member's place in the network, every
  -- bridge owned
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
  -- `go writer(wcli)`
  wp_apply wp_fork $$ []
  · (try wp_auto)
    wp_apply (wp_writer wcl ρ₁.rd.kv γc) $$ []
    · iframe #
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- the bridges, claimed for the cluster (the API servers sharing the process's compactor)
  imod (k8s.epOf_alloc (∅ : GMap GoString GName) clusterCfg.Bridge1' ρ₁.rd.kv
      (fun _ => iprop(True)) rfl) $$ Hreg with ⟨%γa₁, Hreg, #Hep₁⟩
  imod (k8s.epOf_alloc _ clusterCfg.Bridge2' ρ₁.rd.kv (fun _ => iprop(True))
      (by simp only [GMap.lookup_insert_eq_iff, clusterCfg_ok.b12, ↓reduceIte]; rfl)) $$ Hreg with ⟨%γa₂, Hreg, #Hep₂⟩
  imod (k8s.epOf_alloc _ clusterCfg.Bridge3' ρ₁.rd.kv (fun _ => iprop(True))
      (by simp only [GMap.lookup_insert_eq_iff, clusterCfg_ok.b23, clusterCfg_ok.b13,
        ↓reduceIte]; rfl)) $$ Hreg
    with ⟨%γa₃, -, #Hep₃⟩
  ihave #Heps : ([∗list] ep ∈ ms.map client.SrvAt.addr,
      k8s.epOf (GF := GF) ep ρ₁.rd.kv (fun _ => iprop(True))) $$ []
  · rw [hms]
    iapply BigSepL.bigSepL_cons.2; iframe Hep₁
    iapply BigSepL.bigSepL_cons.2; iframe Hep₂
    iapply BigSepL.bigSepL_cons.2; iframe Hep₃
    iapply BigSepL.bigSepL_nil.2; itrivial
  ihave IH : (∃ (n : w64) (k : w32), "i" ∷ i_ptr ↦ n ∗
      "Hadd" ∷ sync.join.ownAdder wg_ptr k iprop(True) ∗
      "%Hk" ∷ ⌜sint.Z k ≤ sint.Z n ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ 5 ∧ 0 ≤ sint.Z k⌝ : IProp GF)
    $$ [i Hadd]
  · iexists _, (W32 0); iframe; ipureintro; decide
  wp_for IH
  wp_if_destruct
  · -- `cli, err := cluster3.NewClient(cfg, lg)`
    wp_apply (wp_NewClient clusterCfg lg V clusterCfg_ok htb) as %cl %cerr Hc
    · iframe #
    icases Hc with (⟨%Hcerr, #Hnc, -⟩ | %Hcfail)
    rotate_left
    · obtain ⟨Hcerr, -⟩ := Hcfail
      cases cerr with
      | nil => exact absurd rfl Hcerr
      | ok ei => ?_
      (try wp_auto)
      wp_for_post
      (try wp_auto)
      wp_apply (sync.join.WaitGroup.wp_Wait iprop(True) k wg_ptr) $$ [Hadd] as -
      · iframe #; iframe
      (try wp_auto)
      iapply HΦ; itrivial
    subst Hcerr
    (try wp_auto)
    ihave #Hone2 : client.clientWriteOnce (GF := GF) cl (cluster3.bridges clusterCfg) $$ []
    · iunfold client.clientWriteOnce; ipureintro; exact hnr
    imod (client.isKv_of_newClient cl ms (cluster3.bridges clusterCfg) V ρ₁.rd.kv hms hsame hrb)
      $$ [Hnc Hone2 Hregs] with ⟨%capi, #Hckvf, #Hckv⟩
    · iframe #
    ihave #Hcko : k8s.clientKvOk (GF := GF) cl ρ₁.rd.kv $$ []
    · iunfold k8s.clientKvOk; iexists capi, false; iframe #
    -- its watcher handle, with the watcher's facts at the bridges
    ihave ⟨%w, %conn, %wc, %lgw, %ics, #HWf, #Hcw⟩ := isNewClient_watcher_of cl
      (cluster3.bridges clusterCfg) V $$ [Hnc Hconn]
    · iframe #
    ihave #Hcwo : k8s.clientWatchOk (GF := GF) cl ρ₁.rd.kv $$ []
    · iunfold k8s.clientWatchOk; iexists w, _; iframe #; ipureintro; rfl
    -- `wg.Add(1)`
    wp_apply (sync.join.WaitGroup.wp_Add iprop(True) wg_ptr iprop(True) k) $$ [Hadd]
      as ⟨Hadd, Hdone⟩
    · iframe #; iframe
      ipureintro; omega
    ihave Hadd := sync.join.ownAdder_wand iprop(True) _ _ _ $$ [] Hadd
    · iintro _; itrivial
    (try wp_auto)
    -- `go func() { apiserver(cli, shared); wg.Done() }()`
    wp_apply wp_fork $$ [Hdone cli shared]
    · (try wp_auto)
      wp_apply (wp_apiserver cl ms V ρ₁.rd.raft ρ₁.rd.kv γc _ hsame hkc hkr) $$ []
      · iframe #
        rw [hms]
        iframe #
      (try wp_auto)
      wp_apply sync.join.WaitGroup.wp_Done iprop(True) _ $$ [Hdone]
      · iframe #; iframe
      (try wp_auto)
      (try itrivial)
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, (k + W32 1)
    iframe
    ipureintro
    exact loop_step n k Hk Hif
  · (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Wait iprop(True) k wg_ptr) $$ [Hadd] as -
    · iframe #; iframe
    (try wp_auto)
    iapply HΦ; itrivial

end proof

end k8s_compactor
end EtcdGrove
end Perennial
