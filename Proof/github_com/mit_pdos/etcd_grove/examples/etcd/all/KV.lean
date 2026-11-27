/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/etcd/all/KV.lean`: the five drivers' triples side
by side (`notes/etcd-unified-scope.md`, §3.1). Their preconditions share no exclusive resource, so the
proof frames each driver's resources into its call; the arguments the goroutines read are the part's
locals, read-only once the wait group is set up. The wait group is in the join idiom, `wg.Add(4)` by
`waitGroup.wp_Add_many` (one `Done` right per goroutine); `spawn` gives each spawned driver a thread
token of its own and the calling thread's goes to `cache.Main`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.all.KV
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

theorem KV.wp_proof
    (wp_spawn : spawn.spec (GF := GF) (hG := hG))
    (wp_txn : etcd_txnlinfaultsN.Main.spec (GF := GF) (hG := hG))
    (wp_part : etcd_partition.MainWatch.spec (GF := GF) (hG := hG))
    (wp_cw : etcd_compactwatch.Main.spec (GF := GF) (hG := hG))
    (wp_c : etcd_compacted.Main.spec (GF := GF) (hG := hG))
    (wp_cache : etcd_cache.Main.spec (GF := GF) (hG := hG)) :
    KV.spec (GF := GF) (hG := hG) := by
  intro CS ER FM RT N k₁ ids₁ ps₁ ctxs₁ boot₁ pid₁ pid₂ pid₃ psP ctxsP bootP cwId ctxsCW
    bootCW cId ctxsC bootC kvId ctxsK bootK clients ops nw nops cnw cnops sched₁ sched₂ steps₁ steps₂
    TB RB48 RBN HLv hk1 hk hlen Hbf HbfP HbfCW HbfC HbfK Hwb Haf Hbuq Hrf Hdbo Hms Hat
    Hc0 Hc31 Hops Hmul Hnw0 Hnw31 Hnops Hnmul Hcnw0 Hcnw31 Hcnops Hcmul
  wp_start as ⟨Hms1, Hbs1, HresP, HresCW, HresC, HresK, #Hs1, #Hs2, Htok, Hp1, HpP, HpCW, HpC,
    HpK⟩
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #P1 : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.txnlinfaultsN $$ []
  · iPkgInit
  ihave #PP : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.partition $$ []
  · iPkgInit
  ihave #PCW : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.compactwatch $$ []
  · iPkgInit
  ihave #PC : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.compacted $$ []
  · iPkgInit
  ihave #PK : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.cache $$ []
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
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- `wg.Add(4)`
  wp_apply (waitGroup.wp_Add_many sync.WaitGroup.wp_Add wg_ptr iprop(True)
    [iprop(True), iprop(True), iprop(True), iprop(True)] (by simp)) $$ [Hadd]
    as ⟨Hadd, Hd1, Hd2, Hd3, Hd4, -⟩
  · iframe #; iframe
  (try wp_auto)
  -- `spawn(&wg, func() { txnlinfaultsN.Main(k1, clients, ops, sched1) })`
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply wp_spawn $$ [Hd1 Hms1 Hbs1 Hp1]
  · iframe #; iframe
    inext
    iintro Htok₁
    (try wp_auto)
    wp_apply (wp_txn k₁ N ids₁ ps₁ ctxs₁ boot₁ clients ops sched₁ steps₁ hk1 hk hlen Hbf
      TB.threadBound_le HLv RB48.receiptBound_le RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hms Hat
      Hc0 Hc31 Hops Hmul) $$ [Hms1 Hbs1 Htok₁ Hp1] as %r %-
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `spawn(&wg, func() { partition.MainWatch(nw, nops, sched2) })`
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply wp_spawn $$ [Hd2 HresP HpP]
  · iframe #; iframe
    inext
    iintro Htok₂
    (try wp_auto)
    wp_apply (wp_part N pid₁ pid₂ pid₃ psP ctxsP bootP nw nops sched₂ steps₂ HbfP
      TB.threadBound_le HLv RB48.receiptBound_le RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hms Hat
      Hnw0 Hnw31 Hnops Hnmul) $$ [HresP Htok₂ HpP] as %r %-
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `spawn(&wg, func() { compactwatch.Main() })`
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply wp_spawn $$ [Hd3 HresCW HpCW]
  · iframe #; iframe
    inext
    iintro Htok₃
    (try wp_auto)
    wp_apply (wp_cw N cwId ctxsCW bootCW HbfCW TB.threadBound_le HLv RB48.receiptBound_le
      RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hms Hat) $$ [HresCW Htok₃ HpCW]
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `spawn(&wg, func() { compacted.Main() })`
  rw [recv_eq_func_mk BAnon BAnon]
  wp_apply wp_spawn $$ [Hd4 HresC HpC]
  · iframe #; iframe
    inext
    iintro Htok₄
    (try wp_auto)
    wp_apply (wp_c N cId ctxsC bootC HbfC TB.threadBound_le HLv RB48.receiptBound_le
      RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hms Hat) $$ [HresC Htok₄ HpC]
    · iframe; (try iframe #)
    (try wp_auto)
    (try itrivial)
  (try wp_auto)
  -- `cache.Main(cnw, cnops)`, with the calling thread's token
  wp_apply (wp_cache N kvId ctxsK bootK cnw cnops HbfK TB.threadBound_le HLv RB48.receiptBound_le
    RBN.receiptBound_le Hwb Haf Hbuq Hrf Hdbo Hms Hat Hcnw0 Hcnw31 Hcnops Hcmul)
    $$ [HresK Htok HpK] as %r %-
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
