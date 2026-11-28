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
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.newStore
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WatchQ
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WatchEnvN
public import Spec.context.ErrAny
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.SeedRun

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
    (wp_newStore : newStore.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_Check : Check.spec (GF := GF) (hG := hG)) :
    MainPartition.spec (GF := GF) (hG := hG) := by
  intro EK RT SC ST VA k N ids ps ctxs boot clients ops watchers wops sched steps ThB RcB RcN HLv hk1 hk
    Hlen Hbf HwbN Haf Hbuq Hrf Hdbo Hms hAs hse Hty H0 Hw0 H31 Hops Hwops Hmul
  have Htb := ThreadBoundLe.le (GF := GF) (2 ^ 28)
  have Hrb48 := ReceiptBoundLe.le (GF := GF) (2 ^ 48)
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
  icases Hup with ⟨%γk, %γn, %ss, %bs, %cl, %V, %ms, %ws, %γrc, %m0, #Hss, #Hbs, #Hkc, #Hnc, %Hal,
    #Hregs, Hctl, Hobs, Hetcd, #Hwregs, %Hwf⟩
  obtain ⟨-, Hsva, hlog₁, Hsv⟩ := Hal
  obtain ⟨hsrc, hlogc, hmem, hV⟩ := Hwf
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
  imod (histAuth_seed (GF := GF)) with ⟨%γh, Hhist, #Hsr⟩
  -- `newStore(kc)`: the seed, the features, `etcd3.New`
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, Htok⟩
  wp_apply (wp_newStore kc cl ms V γs γh hAs hmsne (by omega)) $$ [$Hlt Hs] as %s %st0 %h0 %ok ⟨Hlt, Hns⟩
  · rw [Hsva]
    iframe #
    iframe Hs
  ihave Htok := (threadTok_level0 (GF := GF)).2 $$ [Hlt Htok]
  · iframe
  icases Hns with (%Hok | ⟨%Hok, Hs, Hst0, ⟨%hs, #Hh0, Hhs⟩, #Hrs, #Hwl, %sp, %mt, %lt, %Hsp,
    #Hstore, #Hsw⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok Hsp
  wp_auto
  iclear Hsis
  imod (seedInv_cancel γs γk σs2) $$ [Hs] with Hetcd
  · iframe #
    iframe Hs
  -- the driver's invariant at the seeded state, at every member
  imod (kInv_seed γk (storeCfgD kc cl ms V mt lt γh) rfl rfl ⊤) $$ [Hetcd Hhist] with
    ⟨%γ, #Hinv, Hks⟩
  · simp only [storeCfgD]
    iframe
    iexact Hsr
  ihave #Hinvs := kInvs_of_same γ (storeCfgD kc cl ms V mt lt γh) g0s γk
    ((storeCfgD kc cl ms V mt lt γh).K.kvs) (fun y hy => by
      simp only [storeCfgD, k8s.inProcEtcd, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy; exact hsame z hz) $$ Hinv
  -- (stage E) the client's watcher over the cluster's KV, so the store's watch fields
  ihave #Hone1 := one_read_au γ (storeCfgD kc cl ms V mt lt γh) g0s γk $$ Hinv
  ihave #Pio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Heo : client.eofOk (GF := GF) $$ []
  · iapply (client.eofOk_of_init hAs) $$ Pio
  ihave #Pctx : isPkgInit (PROP := IProp GF) pkg_id.context $$ []
  · iPkgInit
  ihave #Hcw := k8s_etcd3N.clientWatchOk_of_regs wp_ErrAny hAs cl V ms ws γrc m0 γk hV
    (by rw [Hsva]; exact k8s_etcd3N.bridges_nodup k hk) hmsne hmem (fun x hx => (Hsv x hx).1)
    hsrc hlogc (by omega) $$ [Pcli Ppb Pctx Heo Hnc Hwregs Hone1]
  · rw [Hsva]
    iframe #
  ihave #Hswk := Hsw $$ Hcw
  -- `go cluster3.Partitioner(srvs, brs, sched)`: every member's place in the network, every bridge
  -- owned (as txnlinfaultsN's `Main`)
  wp_apply wp_fork $$ [Hobs Hctl]
  · wp_apply (wp_Partitioner inferInstance γn _ _ sched ss bs steps) $$ [Hobs Hctl]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- `Check(s, st0, h0, clients, ops, watchers, wops, 0)`
  ihave Hst0 : storeOwn st0 g0s.st $$ [Hst0]
  · iExactEq Hst0; rfl
  ihave Hhs : [∗list] x;g ∈ hs;g0s.hist, storeOwn x g $$ [Hhs]
  · iExactEq Hhs; rfl
  ihave #Pst : isPkgInit (PROP := IProp GF) pkg_id.k8s_io.apiserver.pkg.storage.etcd3 $$ []
  · iPkgInit
  ihave #Hpd : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 $$ []
  · iPkgInit
  wp_apply (wp_Check γ sp (storeCfgD kc cl ms V mt lt γh) g0s γk st0 h0 hs clients ops watchers wops
      (W64 0) rfl rfl rfl rfl rfl hAs hse (by omega)
      (by intro y hy; apply hnr; rw [← Hsva]; exact List.mem_map_of_mem hy)
      (by simpa [storeCfgD, k8s.inProcEtcd] using hmsne) (by omega) H0 Hw0 H31 Hops Hwops Hmul
      (by rw [g0s_len, σs2_rev]; show st3.items.length + 3 < _; rw [st3_items]; simp)
      (by simp [g0s, st3]) runOk_g0s)
    $$ [Hks Hst0 Hhs] as %r %hr
  · iframe #
    iframe Hks Hst0 Hhs
  have hok : r = go!"Ok" := hr.2 (by decide)
  subst hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end k8s_etcd3
end EtcdGrove
end Perennial
