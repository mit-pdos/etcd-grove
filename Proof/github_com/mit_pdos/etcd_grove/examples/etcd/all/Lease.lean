/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/Lease.lean`: leaseN's triple on a
spawned goroutine, leasecatchup's on the calling thread (as `KV.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Lease
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.spawn
public import Proof.sync.WaitGroupAddMany
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_all

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.all.Assumptions]

theorem Lease.wp_proof
    (wp_spawn : spawn.spec (GF := GF) (hG := hG))
    (wp_leaseN : etcd_leaseN.Main.spec (GF := GF) (hG := hG))
    (wp_catchup : etcd_leasecatchup.Main.spec (GF := GF) (hG := hG)) :
    Lease.spec (GF := GF) (hG := hG) := by
  intro CS N k₄ ids₄ ps₄ ctxs₄ boot₄ lid₁ lid₂ lid₃ psL ctxsL bootL TB RB48 RBN HLv
    hk₄1 hk₄ hlen₄ Hbf₄ HbfL Hwb Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat
  wp_start as ⟨Hms₄, HresL, Htok, Hp₄, HpL⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #PN : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leaseN $$ []
  · iPkgInit
  ihave #PL : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.leasecatchup $$ []
  · iPkgInit
  (try wp_auto)
  ipersist k4
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- `wg.Add(1)`
  wp_apply (waitGroup.wp_Add_many sync.WaitGroup.wp_Add wg_ptr iprop(True) [iprop(True)] (by simp))
    $$ [Hadd] as ⟨Hadd, Hd1, -⟩
  · iframe #; iframe
  (try wp_auto)
  rw [recv_eq_func_mk BAnon BAnon]
  -- `spawn(&wg, func() { leaseN.Main(k4) })`
  wp_apply wp_spawn $$ [Hd1 Hms₄ Hp₄]
  · iframe #; iframe
    inext
    iintro Htok₁
    (try wp_auto)
    wp_apply (wp_leaseN k₄ N ids₄ ps₄ ctxs₄ boot₄ hk₄1 hk₄ hlen₄ Hbf₄ TB.threadBound_le HLv
      RB48.receiptBound_le RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hlp Hms Hat)
      $$ [Hms₄ Htok₁ Hp₄]
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `leasecatchup.Main()`, with the calling thread's token
  wp_apply (wp_catchup N lid₁ lid₂ lid₃ psL ctxsL bootL) $$ [HresL Htok HpL]
  · iframe
    iframe %HbfL
    isplitr
    · ipureintro; exact ⟨TB.threadBound_le, HLv, RB48.receiptBound_le, RBN.receiptBound_le, Hwb⟩
    isplitr
    · ipureintro; exact ⟨Haf, Hbuq, Hrf, Hdbo⟩
    isplitr
    · ipureintro; exact ⟨Hlp, Hlne⟩
    ipureintro; exact ⟨Hms, Hat⟩
  (try wp_auto)
  -- `wg.Wait()`
  wp_apply (sync.join.WaitGroup.wp_Wait _ _ wg_ptr) $$ [Hadd] as -
  · iframe #; iframe
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end etcd_all
end EtcdGrove
end Perennial
