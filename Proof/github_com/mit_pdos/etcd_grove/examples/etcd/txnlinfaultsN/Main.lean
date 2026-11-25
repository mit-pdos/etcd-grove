/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/txnlinfaultsN/Main.lean`
(`notes/txnlinfaultsN-plan.md`). Lean-first (no Rocq counterpart).

partition's `Main` (`partition/Main.lean`) over `k` members: `k = 0` is excluded by the premise (the
early return is not taken); the logger; the cluster (`startCluster`: `clusterUp`); the partitioner
forked on the schedule (every member's place in the network, every bridge owned and not
blackholed); the instance's invariant at the cluster's start store (txnlin's `linkvInv_alloc_boot`,
at the cluster's KV names, every member's by `etcd_partition.linkvInv_congr`), so each client has
partition's `Apply.spec`'s premises (`etcd_partition.clientOk`: the `k` members at their bridges'
addresses, the bridges refusal-free); partition's `Check(clis, clients, ops, 0)`, which returns `Ok`
(`timeout = 0`), so the panic on `Illegal` is not taken. A failed start ends `Main` with `Unknown`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.startCluster
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Dir
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Alloc
public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.cluster3.Partitioner
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.partition.Check
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.txnlin.Boot
public import Spec.go_uber_org.zap.NewNop
public import Proof.github_com.mit_pdos.etcd_grove.PkgInitMemo

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_txnlinfaultsN

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3 go_etcd_io.etcd.server.v3.etcdserver

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The instance's invariant at every member's KV names** (`etcd_partition.linkvInv_congr`): the
members' KV state variables are the cluster's. -/
theorem linkvInvs_of (γl : etcd_txnlin.LinkvNames) (γk : KVNames)
    (svs : List (EtcdGrove.client.SrvAt GF)) (h : ∀ sv ∈ svs, sv.γr.kv.st = γk.st) :
    □ etcd_txnlin.linkvInv (GF := GF) γl γk ⊢ [∗list] sv ∈ svs, etcd_txnlin.linkvInv γl sv.γr.kv :=
  BigSepL.bigSepL_intro fun _ sv hk => by
    rw [etcd_partition.linkvInv_congr γl sv.γr.kv γk (h sv (List.mem_of_getElem? hk))]
    exact intuitionistically_elim

end lemmas

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN.Assumptions]

set_option maxHeartbeats 1000000 in
theorem Main.wp_proof
    (wp_NewNop : zap.NewNop.spec (GF := GF) (hG := hG))
    (wp_startCluster : startCluster.spec (GF := GF) (hG := hG))
    (wp_partitioner : cluster3.Partitioner.spec (GF := GF) (hG := hG))
    (wp_Check : etcd_partition.Check.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS k N ids ps ctxs boot clients ops sched steps hk1 hk Hlen Hbf Htb HLv Hrb48 HrbN
    HwbN Haf Hbuq Hrf Hdbo Hms hAs H0 H31 Hops Hmul
  wp_start as ⟨Hstart, Hbrs, #Hsched, Htok, #Hprem⟩
  -- `k == 0` is false
  have hk0 : decide ((W64 (k : Int)) = W64 0) = false := by
    rw [decide_eq_false_iff_not]; intro h
    have := congrArg BitVec.toNat h; simp [W64] at this; omega
  (try wp_auto)
  simp only [hk0]
  (try wp_auto)
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_apply wp_NewNop as %lg #Hlgz
  (try wp_auto)
  -- the cluster and its clients
  wp_apply (wp_startCluster k N ids ps ctxs boot lg hk1 hk Hlen Hbf Htb HLv Hrb48 HrbN HwbN Haf
      Hbuq Hrf Hdbo Hms) $$ [Hstart Hbrs Htok] as %srvs %brs %clis %ok Hup
  · iframe; iframe #
  icases Hup with (%Hok | ⟨%Hok, Htok, Hup⟩)
  · subst Hok
    wp_auto
    iapply HΦ; ipureintro; right; rfl
  subst Hok
  wp_auto
  iunfold clusterUp at Hup
  icases Hup with ⟨%γk, %γn, %ss, %bs, %cls, %svs, #Hss, #Hbs, Hcls, %Hal, #Hregs, Hctl, Hobs,
    #Hnc, Hetcd⟩
  imod ownSlice_persist _ _ _ $$ Hcls with #Hcls
  obtain ⟨Hclen, Hsva, Hlog, Hsv⟩ := Hal
  -- `go cluster3.Partitioner(srvs, brs, sched)`
  wp_apply wp_fork $$ [Hobs Hctl]
  · wp_apply (wp_partitioner inferInstance γn _ _ sched ss bs steps) $$ [Hobs Hctl]
    all_goals (try (iframe #))
    all_goals (try iframe)
    ipureintro; exact isPanic_intoVal ()
  (try wp_auto)
  -- the instance's invariant, at the cluster's start store (empty), for every member's names
  imod (etcd_txnlin.linkvInv_alloc_boot γk Hlog (fun _ _ => True) ps
      (LogEntry.toEntries boot 0) (srvBootLogOk_of_BootLog _ _ _ Hbf.boot) ⊤) $$ Hetcd
    with ⟨%γl, #Hlinv, Hst⟩
  ihave #Hinvs := linkvInvs_of γl γk svs (fun sv h => (Hsv sv h).1) $$ Hlinv
  -- (D29) the bridges' addresses are refusal-free: every client's writes are sent at most once
  have hnr : ∀ a ∈ bridges k, noRefusalAt a := by
    intro a ha
    rw [← Hsva] at ha
    obtain ⟨sv, hsv, rfl⟩ := List.mem_map.1 ha
    exact (Hsv sv hsv).2
  have hsvne : svs ≠ [] := by
    intro h
    have := congrArg List.length Hsva
    rw [h, bridges_length] at this; simp at this; omega
  ihave #Hok : ([∗list] cl ∈ cls, etcd_partition.clientOk γl cl) $$ []
  · iapply (BigSepL.bigSepL_impl (Φ := fun _ cl =>
      iprop(∃ V : EtcdGrove.client.WEnv GF, isNewClient cl (bridges k) V))) $$ Hnc
    iintro !> %i %cl %_ ⟨%V, #HV⟩
    iunfold etcd_partition.clientOk
    iexists svs, V
    rw [Hsva]
    iframe #
    isplitr
    · ipureintro; exact hsvne
    iunfold EtcdGrove.client.clientWriteOnce
    ipureintro; exact hnr
  -- `partition.Check(clis, clients, ops, 0)`
  ihave #Pp : isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.partition
    $$ []
  · iPkgInit
  ihave #Hcci : context.isClosedchanInit (GF := GF) $$ []
  · iapply context.isClosedchanInit_of_init
    iPkgInit
  wp_apply (wp_Check γl _ cls clients ops (W64 0) hAs (by omega)
      (by intro h; rw [h] at Hclen; simp at Hclen; omega) H0 H31 Hops Hmul) $$ [Hst] as %r %Hr
  · iframe; iframe #
  obtain ⟨-, Hok⟩ := Hr
  have Hok : r = go!"Ok" := Hok (by decide)
  subst Hok
  wp_auto
  iapply HΦ; ipureintro; left; rfl

end proof

end etcd_txnlinfaultsN
end EtcdGrove
end Perennial
