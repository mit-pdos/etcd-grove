/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/Restart.lean`: restartN's triple on a
spawned goroutine, restart1's on the calling thread (as `KV.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Restart
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

theorem Restart.wp_proof
    (wp_spawn : spawn.spec (GF := GF) (hG := hG))
    (wp_restartN : etcd_restartN.Main.spec (GF := GF) (hG := hG))
    (wp_restart1 : etcd_restart1.Main.spec (GF := GF) (hG := hG)) :
    Restart.spec (GF := GF) (hG := hG) := by
  intro CS N k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR TB RB48 RBN HLv hk₅ hlen₅ Hbf₅ HbfR Hwb Haf
    Hbuq Hdbo
  wp_start as ⟨Hms₅, HresR, Htok, Hp₅, HpR⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #PN : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restartN $$ []
  · iPkgInit
  ihave #P1 : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.restart1 $$ []
  · iPkgInit
  (try wp_auto)
  ipersist k5
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
  -- `spawn(&wg, func() { restartN.Main(k5) })`
  wp_apply wp_spawn $$ [Hd1 Hms₅ Hp₅]
  · iframe #; iframe
    inext
    iintro Htok₁
    (try wp_auto)
    wp_apply (wp_restartN k₅ N ids₅ ps₅ ctxs₅ boot₅ hk₅ hlen₅ Hbf₅ HLv Hwb Haf Hbuq Hdbo)
      $$ [Hms₅ Htok₁ Hp₅]
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `restart1.Main()`, with the calling thread's token
  wp_apply (wp_restart1 N rId ctxsR bootR HbfR HLv Hwb Haf Hbuq Hdbo) $$ [HresR Htok HpR]
  · iframe; (try iframe #)
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
