/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/Main.lean`: the four parts' triples side
by side (as `KV.lean` for the drivers): `wg.Add(3)`, `KV`, `Auth` and `Lease` spawned, `Restart` on the
main thread with its token, `wg.Wait()`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.Main
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

theorem Main.wp_proof
    (wp_spawn : spawn.spec (GF := GF) (hG := hG))
    (wp_KV : KV.spec (GF := GF) (hG := hG))
    (wp_Auth : Auth.spec (GF := GF) (hG := hG))
    (wp_Lease : Lease.spec (GF := GF) (hG := hG))
    (wp_Restart : Restart.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro CS ER FM RT N k₁ ids₁ ps₁ ctxs₁ boot₁ pid₁ pid₂ pid₃ psP ctxsP bootP cwId ctxsCW
    bootCW cId ctxsC bootC kvId ctxsK bootK k₂ ids₂ ps₂ ctxs₂ boot₂ k₃ ids₃ ps₃ ctxs₃ boot₃
    k₄ ids₄ ps₄ ctxs₄ boot₄ lid₁ lid₂ lid₃ psL ctxsL bootL k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR
    clients ops nw nops cnw cnops sched₁ sched₂ steps₁ steps₂ TB RB48 RBN HLv
    hk₁1 hk₁ hlen₁ Hbf₁ HbfP HbfCW HbfC HbfK hk₂1 hk₂ hlen₂ Hbf₂ hk₃1 hk₃ hlen₃ Hbf₃ Hap
    hk₄1 hk₄ hlen₄ Hbf₄ HbfL hk₅ hlen₅ Hbf₅ HbfR Hwb Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat
    Hc0 Hc31 Hops Hmul Hnw0 Hnw31 Hnops Hnmul Hcnw0 Hcnw31 Hcnops Hcmul
  wp_start as ⟨Hms1, Hbs1, HresP, HresCW, HresC, HresK, Hms₂, Hms₃, Hms₄, HresL, Hms₅, HresR,
    #Hs1, #Hs2, Htok, Hp1, HpP, HpCW, HpC, HpK, Hp₂, Hp₃, Hp₄, HpL, Hp₅, HpR⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  ipersist k1
  ipersist clients
  ipersist ops
  ipersist sched1
  ipersist nw
  ipersist nops
  ipersist sched2
  ipersist cnw
  ipersist cnops
  ipersist k2
  ipersist k3
  ipersist k4
  ipersist k5
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- `wg.Add(3)`
  wp_apply (mvccrand.wp_Add_many sync.WaitGroup.wp_Add wg_ptr iprop(True)
    [iprop(True), iprop(True), iprop(True)] (by simp)) $$ [Hadd] as ⟨Hadd, Hd1, Hd2, Hd3, -⟩
  · iframe #; iframe
  (try wp_auto)
  -- `spawn(&wg, func() { KV(k1, clients, ops, sched1, nw, nops, sched2, cnw, cnops) })`
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply wp_spawn $$ [Hd1 Hms1 Hbs1 HresP HresCW HresC HresK Hp1 HpP HpCW HpC HpK]
  · iframe #; iframe
    inext
    iintro Htok₁
    (try wp_auto)
    wp_apply (wp_KV N k₁ ids₁ ps₁ ctxs₁ boot₁ pid₁ pid₂ pid₃ psP ctxsP bootP cwId ctxsCW bootCW
      cId ctxsC bootC kvId ctxsK bootK clients ops nw nops cnw cnops sched₁ sched₂ steps₁ steps₂
      HLv hk₁1 hk₁ hlen₁ Hbf₁ HbfP HbfCW HbfC HbfK Hwb Haf Hbuq Hrf Hdbo Hms Hat
      Hc0 Hc31 Hops Hmul Hnw0 Hnw31 Hnops Hnmul Hcnw0 Hcnw31 Hcnops Hcmul)
      $$ [Hms1 Hbs1 HresP HresCW HresC HresK Htok₁ Hp1 HpP HpCW HpC HpK]
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `spawn(&wg, func() { Auth(k2, k3) })`
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply wp_spawn $$ [Hd2 Hms₂ Hms₃ Hp₂ Hp₃]
  · iframe #; iframe
    inext
    iintro Htok₂
    (try wp_auto)
    wp_apply (wp_Auth N k₂ ids₂ ps₂ ctxs₂ boot₂ k₃ ids₃ ps₃ ctxs₃ boot₃ HLv hk₂1 hk₂ hlen₂ Hbf₂
      hk₃1 hk₃ hlen₃ Hbf₃ Hap Hwb Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat)
      $$ [Hms₂ Hms₃ Htok₂ Hp₂ Hp₃]
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `spawn(&wg, func() { Lease(k4) })`
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply wp_spawn $$ [Hd3 Hms₄ HresL Hp₄ HpL]
  · iframe #; iframe
    inext
    iintro Htok₃
    (try wp_auto)
    wp_apply (wp_Lease N k₄ ids₄ ps₄ ctxs₄ boot₄ lid₁ lid₂ lid₃ psL ctxsL bootL HLv hk₄1 hk₄ hlen₄
      Hbf₄ HbfL Hwb Haf Hbuq Hrf Hdbo Hlp Hlne Hms Hat) $$ [Hms₄ HresL Htok₃ Hp₄ HpL]
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `Restart(k5)`, with the main thread's token
  wp_apply (wp_Restart N k₅ ids₅ ps₅ ctxs₅ boot₅ rId ctxsR bootR HLv hk₅ hlen₅ Hbf₅ HbfR Hwb Haf
    Hbuq Hdbo) $$ [Hms₅ HresR Htok Hp₅ HpR]
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
