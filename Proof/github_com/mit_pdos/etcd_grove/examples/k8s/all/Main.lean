/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/k8s/all/Main.lean`: the two drivers' triples
side by side (`notes/k8s-unified-scope.md`, §3.1). Their preconditions share no exclusive resource,
so the proof frames each driver's resources into its call; the only bookkeeping is the thread tokens.
Both triples consume the token they are given and return none: `go holdToken()` keeps its fresh token
here (`wp_fork_tok_self`; the goroutine never returns), the store's goroutine gets the token of its
`go` (`wp_fork_tok_body`), hands it to `k8setcd3.MainPartition`, and exits with the one `holdToken`'s
`go` gave; the main thread's own token goes to `compactor.MainPartition`. The wait group is in the
join idiom, as the compactor's own `MainPartition` uses it. Lean-first (no Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.Main
public import Spec.github_com.mit_pdos.etcd_grove.examples.k8s.all.holdToken
public import Perennial.Proof.sync.Results

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_all

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.all.Assumptions]

theorem Main.wp_proof
    (wp_holdToken : holdToken.spec (GF := GF) (hG := hG))
    (wp_store : k8s_etcd3.MainPartition.spec (GF := GF) (hG := hG))
    (wp_comp : k8s_compactor.MainPartition.spec (GF := GF) (hG := hG)) :
    Main.spec (GF := GF) (hG := hG) := by
  intro SE RT SC ST SV k N ids ps ctxs boot k₂ ids' ps' ctxs' boot' clients ops
    watchers wops sched₁ sched₂ steps₁ steps₂ TB RB48 RBN HLv hk1 hk hlen Hbf hk₂1 hk₂ hlen' Hbf' HwbN
    Haf Hbuq Hrf Hdbo Hms hAs Hse Hot Hc0 Hw0 Hc31 Hops Hwops Hmul
  wp_start as ⟨Hms1, Hbs1, Hms2, Hbs2, #Hs1, #Hs2, Htok, #Hprem1, #Hprem2, Hreg⟩
  ihave #Pst : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 $$ []
  · iPkgInit
  ihave #Pcp : isPkgInit (PROP := IProp GF)
      pkg_id.github_com.mit_pdos.etcd_grove.examples.k8s.compactor $$ []
  · iPkgInit
  ihave #Psync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  (try wp_auto)
  -- `go holdToken()`: the goroutine never returns, its thread token stays here
  wp_apply wp_fork_tok_self as Htok₂
  · wp_apply wp_holdToken as Hf
    iexfalso; iexact Hf
  (try wp_auto)
  -- the wait group, in the join idiom
  imod (sync.init_WaitGroup (sync.join.wgjN.@"wg") wg_ptr) $$ wg with ⟨%γwg, #Hwg, Hctr, Hwaiters⟩
  imod (sync.join.init _ γwg) $$ [Hctr Hwaiters] with Hadd
  · iframe #; iframe
  -- `wg.Add(1)`
  wp_apply (sync.join.WaitGroup.wp_Add iprop(True) wg_ptr iprop(True) (W32 0)) $$ [Hadd]
    as ⟨Hadd, Hdone⟩
  · iframe #; iframe
    ipureintro; decide
  ihave Hadd := sync.join.ownAdder_wand iprop(True) _ _ _ $$ [] Hadd
  · iintro _; itrivial
  (try wp_auto)
  -- `go func() { k8setcd3.MainPartition(k1, ..., sched1); wg.Done() }()`
  wp_apply wp_fork_tok_body $$ [Hdone Hms1 Hbs1 Htok₂ k1 clients ops watchers wops sched1]
  · iintro Htok₃
    (try wp_auto)
    wp_apply (wp_store k N ids ps ctxs boot clients ops watchers wops sched₁ steps₁ HLv hk1 hk hlen
      Hbf HwbN Haf Hbuq Hrf Hdbo Hms hAs Hse Hot Hc0 Hw0 Hc31 Hops Hwops Hmul)
      $$ [Hms1 Hbs1 Htok₃] as %r %-
    · iframe; iframe #
    (try wp_auto)
    wp_apply sync.join.WaitGroup.wp_Done iprop(True) _ $$ [Hdone]
    · iframe #; iframe
    (try wp_auto)
    iframe
  (try wp_auto)
  -- `compactor.MainPartition(k2, sched2)`, with the main thread's token
  wp_apply (wp_comp k₂ N ids' ps' ctxs' boot' sched₂ steps₂ hk₂1 hk₂ hlen' Hbf' TB.threadBound_le HLv
    RB48.receiptBound_le RBN.receiptBound_le HwbN Haf Hbuq Hrf Hdbo Hms hAs)
    $$ [Hms2 Hbs2 Htok Hreg]
  · iframe; iframe #
  (try wp_auto)
  -- `wg.Wait()`
  wp_apply (sync.join.WaitGroup.wp_Wait iprop(True) _ wg_ptr) $$ [Hadd] as -
  · iframe #; iframe
  (try wp_auto)
  iapply HΦ; itrivial

end proof

end k8s_all
end EtcdGrove
end Perennial
