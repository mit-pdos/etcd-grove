/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/Auth.lean`: authN's triple on a
spawned goroutine, authlease's on the calling thread (as `KV.lean`). Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Auth
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.spawn
public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.RunChecksJoin
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

theorem Auth.wp_proof
    (wp_spawn : spawn.spec (GF := GF) (hG := hG))
    (wp_authN : etcd_authN.Main.spec (GF := GF) (hG := hG))
    (wp_authlease : etcd_authlease.Main.spec (GF := GF) (hG := hG)) :
    Auth.spec (GF := GF) (hG := hG) := by
  intro CS ER FM RT N k₂ ids₂ ps₂ ctxs₂ boot₂ k₃ ids₃ ps₃ ctxs₃ boot₃ TB RB48 RBN HLv
    hk₂1 hk₂ hlen₂ Hbf₂ hk₃1 hk₃ hlen₃ Hbf₃ Hap Hwb Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat
  wp_start as ⟨Hms₂, Hms₃, Htok, Hp₂, Hp₃⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #PA : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authN $$ []
  · iPkgInit
  ihave #PL : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.authlease $$ []
  · iPkgInit
  (try wp_auto)
  ipersist k2
  ipersist k3
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- `wg.Add(1)`
  wp_apply (mvccrand.wp_Add_many sync.WaitGroup.wp_Add wg_ptr iprop(True) [iprop(True)] (by simp))
    $$ [Hadd] as ⟨Hadd, Hd1, -⟩
  · iframe #; iframe
  (try wp_auto)
  rw [recv_eq_func_mk BAnon BAnon]
  -- `spawn(&wg, func() { authN.Main(k2) })`
  wp_apply wp_spawn $$ [Hd1 Hms₂ Hp₂]
  · iframe #; iframe
    inext
    iintro Htok₁
    (try wp_auto)
    wp_apply (wp_authN k₂ N ids₂ ps₂ ctxs₂ boot₂ hk₂1 hk₂ hlen₂ Hbf₂ TB.threadBound_le HLv
      RB48.receiptBound_le RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hms Hat)
      $$ [Hms₂ Htok₁ Hp₂] as %r %-
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `authlease.Main(k3)`, with the calling thread's token
  wp_apply (wp_authlease k₃ N ids₃ ps₃ ctxs₃ boot₃ hk₃1 hk₃ hlen₃ Hbf₃ Hap TB.threadBound_le HLv
    RB48.receiptBound_le RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat)
    $$ [Hms₃ Htok Hp₃] as %r %-
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
