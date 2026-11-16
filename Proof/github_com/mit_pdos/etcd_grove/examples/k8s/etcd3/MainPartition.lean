/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/etcd3/MainPartition.lean` (stage A of
`notes/k8s-7f6-scope.md`: `k` members). Lean-first (no Rocq counterpart).

`MainCluster`'s proof (`MainCluster.lean`), keeping what it drops of the cluster's start: each
member's place in the network (`etcdstart.srvPeerCtl`) and each bridge owned
(`bridge.ownBridge … false`), from `k8s_etcd3N.clusterUp`. Once the store is made, they go to the
forked `cluster3.Partitioner` (its `PeerPausable` premise by `inferInstance`), as txnlinfaultsN's
`Main`; the rest, the seeding, the store and `Check`, is `MainCluster`'s.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MainPartition
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Partitioner
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.startCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.DirN
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Check
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.seed
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.noStreaming
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.watchList
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newObj
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.New
public import Spec.k8s_io.apiserver.pkg.storage.etcd3.NewDefaultLeaseManagerConfig
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
    (wp_startCluster : startCluster.spec (GF := GF) (hG := hG))
    (wp_Partitioner : cluster3.Partitioner.spec (GF := GF) (hG := hG))
    (wp_seed : seed.spec (GF := GF) (hG := hG))
    (wp_noStreaming : noStreaming.spec (GF := GF) (hG := hG))
    (wp_watchList : watchList.spec (GF := GF) (hG := hG))
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
  intro CS EK RT SC ST VA k N ids ps ctxs boot clients ops sched steps ThB RcB RcN HLv hk1 hk Hlen Hbf HwbN
    Haf Hbuq Hrf Hdbo Hms hAs hse Hty H0 H31 Hops Hmul
  have Htb := ThreadBoundLe.le (GF := GF) (2 ^ 28)
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
  have hcon := driver_contractOk wp_Encode wp_cEncode wp_Upd wp_Prep wp_ORV wp_Parse wp_From wp_To
    wp_Dec wp_SetZero wp_UID wp_RV (driverSpec_tyOk Hty)
  wp_start as ⟨Hstart, Hbrs, #Hsched, Htok, #Hprem⟩
  -- `k == 0` is false
  have hk0 : decide ((W64 (k : Int)) = W64 0) = false := by
    rw [decide_eq_false_iff_not]; intro h
    have := congrArg BitVec.toNat h; simp [W64] at this; omega
  (try wp_auto)
  simp only [hk0]
  (try wp_auto)
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
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  -- the cluster and its client (`startCluster(k, lg)`)
  wp_apply (wp_startCluster k N ids ps ctxs boot lg hk1 hk Hlen Hbf HLv HwbN Haf
      Hbuq Hrf Hdbo Hms) $$ [Hstart Hbrs Htok] as %srvs %brs %kc %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    (try wp_auto)
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  (try wp_auto)
  iunfold k8s_etcd3N.clusterUp at Hup
  icases Hup with ⟨%γk, %γn, %ss, %bs, %cl, %V, %ms, #Hss, #Hbs, #Hkc, #Hnc, %Hal, #Hregs, Hctl,
    Hobs, Hetcd⟩
  obtain ⟨-, Hsva, hlog₁, Hsv⟩ := Hal
  have hsame : ∀ x ∈ ms, kvSame x.γr.kv γk := fun x hx => (Hsv x hx).1
  have hnr : ∀ a ∈ k8s_etcd3N.bridges k, noRefusalAt a := by
    intro a ha
    rw [← Hsva] at ha
    obtain ⟨sv, hsv, rfl⟩ := List.mem_map.1 ha
    exact (Hsv sv hsv).2
  have hmsne : ms ≠ [] := by
    intro h
    have := congrArg List.length Hsva
    rw [h, k8s_etcd3N.bridges_length] at this; simp at this; omega
  -- (D29) a write sent at most once: every bridge is refusal-free
  ihave #Hone : client.clientWriteOnce (GF := GF) cl (k8s_etcd3N.bridges k) $$ []
  · iunfold client.clientWriteOnce; ipureintro; exact hnr
  -- the seeding, from the cluster's start state (`σb`: no key, revision `1`), at every member
  have hboot0 : kvModelSt γk (bootEntries (LogEntry.toEntries boot 0)) = σb := by
    rw [kvModelSt_boot _ (fun _ _ => True) _ (LogEntry.toEntries boot 0)
      (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
      etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog₁]
    rfl
  imod (seedInv_alloc γk σb ⊤) $$ [Hetcd] with ⟨%γs, #Hsi, Hs⟩
  · rw [← hboot0]; iexact Hetcd
  ihave #Hsis := seedInvs_of_same γs γk ms hsame $$ Hsi
  ihave #Hkc' := Hkc
  iStructNamed Hkc'
  (try wp_auto)
  wp_apply (wp_seed cl ms V γs hAs hmsne) $$ [Hs] as %st0 %h0 %ok Hsd
  · rw [Hsva]
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
  -- (k8s 7f-5, T5-c) `watchList()`: `WatchList` on, unused until the store's watch (7f-6)
  wp_apply wp_watchList as %b2 -
  cases b2 with
  | false =>
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  | true =>
  wp_auto
  iclear Hsis
  imod (seedInv_cancel γs γk σs2) $$ [Hs] with Hetcd
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
  ihave #Hctx := client_ctx_field cl (k8s_etcd3N.bridges k) V $$ [Hnc]
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
  · rw [Hsva]
    iframe #
    imodintro
    iintro %Φ' HΦ'
    wp_apply wp_newObj as %o %ho
    iapply HΦ'
    ipureintro; exact ho
  icases Hnew with ⟨%Herr, %mt, %lt, #Hstore, -⟩
  subst Herr
  wp_auto
  -- `go cluster3.Partitioner(srvs, brs, sched)`: every member's place in the network, every bridge
  -- owned (as txnlinfaultsN's `Main`)
  wp_apply wp_fork $$ [Hobs Hctl]
  · wp_apply (wp_Partitioner inferInstance γn _ _ sched ss bs steps) $$ [Hobs Hctl]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- the driver's invariant at the seeded state, at every member, and `Check`
  let c : k8s.StoreCfg GF DObj :=
    { S := driverSpec, codec := codecI, vi := versionerI, ti := identityI, di := decoderI,
      pathPrefix := go!"/registry", resourcePrefix := go!"/objs", gr := ⟨[], go!"objs"⟩, kc := kc,
      cl := cl, ms := ms, V := V, mt := mt, lt := lt, γh := γh }
  imod (kInv_seed γk c rfl rfl ⊤) $$ [Hetcd Hhist] with ⟨%γ, #Hinv, Hks⟩
  · iframe
    iexact Hsr
  ihave #Hinvs := kInvs_of_same γ c g0s γk ms hsame $$ Hinv
  wp_apply (wp_Check γ sp c g0s st0 h0 hs clients ops (W64 0) rfl rfl rfl rfl rfl hAs hse
      (by omega)
      (by intro y hy; apply hnr; rw [← Hsva]; exact List.mem_map_of_mem hy)
      hmsne (by omega) H0 H31 Hops Hmul
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
