/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/compactor/MainPartition.lean` (K6 of
`notes/k8s-compactor-plan.md`, step 5; on `k` members since `notes/k8s-compactor-n-plan.md`). Lean-first.

The cluster side as the k8s etcd3 driver's `MainPartition`, the compactor side as the one-member
`Main`'s. The cluster (`startCluster`, in compaction mode, the KV names at retention `0`), with the
example's invariant allocated at its start store (no key; `cinv_alloc`), at the first member's KV
names `γK`. The writer's client of the `k` bridges (`etcdstart.NewClients`) and its readiness check,
the partitioner forked on the schedule, the writer forked, and the five API servers, each with its own
client of the bridges (its KV handle, `isKv_of_newClient` over the members, and its watcher,
`k8s_etcd3N.clientWatchOk_of_regs` from the members' watch registrations and the invariant's read
update `oneChangeAu`), forked under a wait group that `MainPartition` waits for; the `k` bridges
claimed for the cluster from the registry's authority (`epOfs_alloc`), for the API servers sharing the
process's compactor.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.MainPartition
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.startCluster
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.ready
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.writer
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.apiserver
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.NewClients
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Partitioner
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.DirN
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.WatchEnvN
public import Spec.go_uber_org.zap.NewNop
public import Spec.context.ErrAny
public import Proof.go_etcd_io.etcd.client.v3.KvOfNew
public import Proof.go_etcd_io.etcd.client.v3.InvServerKV
public import Proof.go_etcd_io.etcd.client.v3.InvClientNewResult
public import Perennial.Proof.sync.Results
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.compactor.NoDup
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.OneMember

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

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 8192 in
theorem MainPartition.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startCluster : startCluster.spec (GF := GF) (hG := hG))
    (wp_NewClients : etcdstart.NewClients.spec (GF := GF) (hG := hG))
    (wp_Partitioner : cluster3.Partitioner.spec (GF := GF) (hG := hG))
    (wp_ErrAny : context.ErrAny.spec (GF := GF) (hG := hG))
    (wp_ready : ready.spec (GF := GF) (hG := hG))
    (wp_writer : writer.spec (GF := GF) (hG := hG))
    (wp_apiserver : apiserver.spec (GF := GF) (hG := hG)) :
    MainPartition.spec (GF := GF) (hG := hG) := by
  intro CS k N ids ps ctxs boot sched steps hk1 hk Hlen Hbf Htb HLv Hrb48 HrbN HwbN Haf
    Hbuq Hrf Hdbo Hms hAs
  haveI : ThreadBoundLe GF (2 ^ 28) := ⟨Htb⟩
  haveI : ReceiptBoundLe GF (2 ^ 48) := ⟨Hrb48⟩
  haveI : ReceiptBoundLe GF (N + 1) := ⟨HrbN⟩
  wp_start as ⟨Hstart, Hbrs, #Hsched, Htok, #Hprem, Hreg⟩
  -- `k == 0` is false
  have hk0 : decide ((W64 (k : Int)) = W64 0) = false := by
    rw [decide_eq_false_iff_not]; intro h
    have := congrArg BitVec.toNat h; simp [W64] at this; omega
  (try wp_auto)
  simp only [hk0]
  (try wp_auto)
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
  ihave #Pes : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart $$ []
  · iPkgInit
  (try wp_auto)
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  -- `startCluster(k, lg)`, in compaction mode
  wp_apply (wp_startCluster k N ids ps ctxs boot lg hk1 hk Hlen Hbf HLv HwbN Haf Hbuq Hrf Hdbo Hms)
    $$ [Hstart Hbrs Htok] as %srvs %brs %baddrs %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    (try wp_auto)
    iapply HΦ; itrivial
  subst Hok
  (try wp_auto)
  iunfold k8s_compactorN.clusterUp at Hup
  icases Hup with ⟨%γk, %γn, %ss, %bs, %ms, %ws, %γrc, #Hss, Hbs, Hba, %Hal, #Hregs, Hctl, Hobs,
    Hetcd, #Hwregs, %Hwf⟩
  imod ownSlice_persist _ _ _ $$ Hbs with #Hbs
  imod ownSlice_persist _ _ _ $$ Hba with #Hba
  obtain ⟨-, Hsva, hlog₁, hkc₀, hkr₀, Hsv⟩ := Hal
  obtain ⟨hsrc, hlogc, hmem⟩ := Hwf
  have hnr : ∀ a ∈ k8s_compactorN.bridges k, noRefusalAt a := by
    intro a ha
    rw [← Hsva] at ha
    obtain ⟨sv, hsv, rfl⟩ := List.mem_map.1 ha
    exact (Hsv sv hsv).2
  have hmsne : ms ≠ [] := by
    intro h
    have := congrArg List.length Hsva
    rw [h, k8s_compactorN.bridges_length] at this; simp at this; omega
  ihave %Hwsl := BigSepL2.bigSepL2_length $$ Hwregs
  -- the first member: its KV names are the example's (`γK`), its read view gives the KV invariant
  obtain ⟨sv0, hsv0⟩ : ∃ sv0, ms[0]? = some sv0 := by
    cases ms with
    | nil => exact absurd rfl hmsne
    | cons x _ => exact ⟨x, rfl⟩
  obtain ⟨w0, hw0⟩ : ∃ w0, ws[0]? = some w0 := by
    cases ws with
    | nil => cases ms with
      | nil => exact absurd rfl hmsne
      | cons _ _ => simp at Hwsl
    | cons x _ => exact ⟨x, rfl⟩
  have hsv0m : sv0 ∈ ms := List.mem_of_getElem? hsv0
  have hs0 : kvSame sv0.γr.kv γk := (Hsv sv0 hsv0m).1
  have hsame : ∀ x ∈ ms, kvSame x.γr.kv sv0.γr.kv :=
    fun x hx => kvSame_trans (Hsv x hx).1 (kvSame_symm hs0)
  have hkc : sv0.γr.kv.cmp = true := by rw [hs0.2.2.2.2.2.1]; exact hkc₀
  have hkr : sv0.γr.kv.cret = 0 := by rw [hs0.2.2.2.2.2.2]; exact hkr₀
  have hrb : receiptBound GF ≤ 2 ^ 62 := by omega
  have htb : threadBound GF ≤ 2 ^ 30 := by omega
  ihave ⟨-, #Hrd0⟩ := k8s_etcd3N.regs_lookup ms ws 0 sv0 w0 hsv0 hw0 $$ Hwregs
  ihave #Hinvs := srvKVInvs_of_read w0.1 sv0.E sv0.γr $$ Hrd0
  iunfold srvKVInvs at Hinvs
  icases Hinvs with ⟨#Hkvi, -⟩
  -- the example's invariant, at the cluster's start store (no key)
  have hboot0 : kvModelSt γk (bootEntries (LogEntry.toEntries boot 0)) = kvStateOf [[], []] := by
    rw [kvModelSt_boot _ (fun _ _ => True) _ (LogEntry.toEntries boot 0)
      (srvBootLogOk_of_BootLog _ _ _ Hbf.boot),
      etcdstart.kvModel_boot _ _ _ (srvBootLogOk_of_BootLog _ _ _ Hbf.boot), hlog₁]
  rw [hboot0] at *
  ihave Hetcd : etcdKV (GF := GF) sv0.γr.kv (kvStateOf [[], []]) $$ [Hetcd]
  · rw [← etcdKV_congr γk sv0.γr.kv hs0.1.symm]; iexact Hetcd
  imod (cinv_alloc sv0.γr.kv ⊤) $$ Hetcd with ⟨%γc, #Hinv⟩
  ihave #Hau : kvReadAu sv0.γr.kv (fun σ => iprop(⌜k8s_etcd3.OneChange σ⌝)) $$ []
  · rw [show (fun σ => iprop(⌜k8s_etcd3.OneChange σ⌝)) = (fun σ => iprop(⌜OneChange σ⌝) : KVState → IProp GF)
      from rfl]
    iapply oneChangeAu sv0.γr.kv γc $$ Hinv
  -- the clients' watch environment: the members' (`watchEnvL`)
  let m0 : etcdstart.WMem GF := (sv0.addr, w0.2, etcdstart.srvWOf sv0.E sv0.γr false)
  let V : client.WEnv GF := etcdstart.watchEnvL m0 (k8s_etcd3N.wmemsOf ms ws) γrc k8s_etcd3N.wpfx
  have hnd : (ms.map client.SrvAt.addr).Nodup := by
    rw [Hsva]; exact k8s_compactorN.bridges_nodup k hk
  have hhs : kvSame γrc.kv sv0.γr.kv := kvSame_trans hsrc (kvSame_symm hs0)
  imod (client.srvStart_alloc (GF := GF) ms) with #Hst
  have Hpl := k8s_compactorN.bridges_plain k hk1
  -- `wcli, err := etcdstart.NewClients(baddrs, lg)`
  icases (threadTok_level0 (GF := GF)).1 $$ Htok with ⟨Hlt, -⟩
  wp_apply (wp_NewClients baddrs (k8s_compactorN.bridges k) lg V htb Hpl) $$ [$Hlt] as %wcl %werr ⟨Hlt, Hwc⟩
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
  wp_apply (wp_ready wcl ms V) $$ [$Hlt] as %b ⟨Hlt, -⟩
  · iframe #
    rw [Hsva]; iexact Hwnc
  cases b
  · (try wp_auto)
    iapply HΦ; itrivial
  (try wp_auto)
  -- the writer's client: refusal-free, its KV handle
  ihave #Hone1 : client.clientWriteOnce (GF := GF) wcl (k8s_compactorN.bridges k) $$ []
  · iunfold client.clientWriteOnce; ipureintro; exact hnr
  imod (client.isKv_of_newClient wcl ms (k8s_compactorN.bridges k) V sv0.γr.kv Hsva hsame hrb)
    $$ [Hwnc Hone1 Hregs] with ⟨%wapi, #Hwkvf, #Hwkv⟩
  · iframe #
  ihave #Hwko : k8s.clientKvOk (GF := GF) wcl sv0.γr.kv $$ []
  · iunfold k8s.clientKvOk; iexists wapi, false; iframe #
  -- `go cluster3.Partitioner(srvs, brs, sched)`
  wp_apply wp_fork $$ [Hobs Hctl]
  · wp_apply (wp_Partitioner inferInstance γn _ _ sched ss bs steps) $$ [Hobs Hctl]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- `go writer(wcli)`
  wp_apply wp_fork_level0 $$ []
  · iintro Hlt
    (try wp_auto)
    wp_apply (wp_writer wcl sv0.γr.kv γc) $$ [$Hlt] as ⟨Hlt, -⟩
    · iframe #
    (try wp_auto)
    iframe Hlt; try itrivial
  (try wp_auto)
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- the bridges, claimed for the cluster (the API servers sharing the process's compactor)
  imod (epOfs_alloc sv0.γr.kv (k8s_compactorN.bridges k) (∅ : GMap GoString GName)
      (k8s_compactorN.bridges_nodup k hk) (fun _ _ => rfl)) $$ Hreg with ⟨%M', -, #Heps⟩
  ihave #Heps' : ([∗list] ep ∈ ms.map client.SrvAt.addr,
      k8s.epOf (GF := GF) ep sv0.γr.kv (fun _ => iprop(True))) $$ []
  · rw [Hsva]; iexact Heps
  ihave IH : (∃ (n : w64) (c : w32), "i" ∷ i_ptr ↦ n ∗
      "Hadd" ∷ sync.join.ownAdder wg_ptr c iprop(True) ∗ "Hlt" ∷ levelTok 0 ∗
      "%Hk" ∷ ⌜sint.Z c ≤ sint.Z n ∧ 0 ≤ sint.Z n ∧ sint.Z n ≤ 5 ∧ 0 ≤ sint.Z c⌝ : IProp GF)
    $$ [i Hadd Hlt]
  · iexists _, (W32 0); iframe; ipureintro; decide
  wp_for IH
  wp_if_destruct
  · -- `cli, err := etcdstart.NewClients(baddrs, lg)`
    wp_apply (wp_NewClients baddrs (k8s_compactorN.bridges k) lg V htb Hpl) $$ [$Hlt] as %cl %cerr ⟨Hlt, Hc⟩
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
      wp_apply (sync.join.WaitGroup.wp_Wait iprop(True) c wg_ptr) $$ [Hadd] as -
      · iframe #; iframe
      (try wp_auto)
      iapply HΦ; itrivial
    subst Hcerr
    (try wp_auto)
    ihave #Hone2 : client.clientWriteOnce (GF := GF) cl (k8s_compactorN.bridges k) $$ []
    · iunfold client.clientWriteOnce; ipureintro; exact hnr
    imod (client.isKv_of_newClient cl ms (k8s_compactorN.bridges k) V sv0.γr.kv Hsva hsame hrb)
      $$ [Hnc Hone2 Hregs] with ⟨%capi, #Hckvf, #Hckv⟩
    · iframe #
    ihave #Hcko : k8s.clientKvOk (GF := GF) cl sv0.γr.kv $$ []
    · iunfold k8s.clientKvOk; iexists capi, false; iframe #
    -- its watcher over the cluster's KV, from the members' watch registrations
    ihave #Hcwo := k8s_etcd3N.clientWatchOk_of_regs wp_ErrAny hAs cl V ms ws γrc m0 sv0.γr.kv rfl
      hnd hmsne hmem hsame hhs hlogc hrb $$ [Pcli Ppb Pctx Heo Hnc Hwregs Hau]
    · rw [Hsva]
      iframe #
    -- `wg.Add(1)`
    wp_apply (sync.join.WaitGroup.wp_Add iprop(True) wg_ptr iprop(True) c) $$ [Hadd]
      as ⟨Hadd, Hdone⟩
    · iframe #; iframe
      ipureintro; omega
    ihave Hadd := sync.join.ownAdder_wand iprop(True) _ _ _ $$ [] Hadd
    · iintro _; itrivial
    (try wp_auto)
    -- `go func() { apiserver(cli, shared); wg.Done() }()`
    wp_apply wp_fork_level0 $$ [Hdone cli shared]
    · iintro Hlt
      (try wp_auto)
      wp_apply (wp_apiserver cl ms V sv0.γr.raft sv0.γr.kv γc _ hsame hkc hkr) $$ [$Hlt] as ⟨Hlt, -⟩
      · iframe #
        rw [Hsva]
        iframe #
      (try wp_auto)
      wp_apply sync.join.WaitGroup.wp_Done iprop(True) _ $$ [Hdone]
      · iframe #; iframe
      (try wp_auto)
      iframe Hlt; try itrivial
    (try wp_auto)
    wp_for_post
    iframe
    iexists _, (c + W32 1)
    iframe
    ipureintro
    exact loop_step n c Hk Hif
  · (try wp_auto)
    wp_apply (sync.join.WaitGroup.wp_Wait iprop(True) c wg_ptr) $$ [Hadd] as -
    · iframe #; iframe
    (try wp_auto)
    iapply HΦ; itrivial


end proof

end k8s_compactor
end EtcdGrove
end Perennial
