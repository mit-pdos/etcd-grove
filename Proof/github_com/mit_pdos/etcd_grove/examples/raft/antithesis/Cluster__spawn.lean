/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/Cluster__spawn.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster__spawn
public import Perennial.Spec.sync.WaitGroup__Add
public import Perennial.Spec.sync.WaitGroup__Done
public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- `Cluster.spawn.spec` as it needs to be (proposed to the lead): the behaviour a function value
`f : GoFunc` (`#f` cannot panic, so `spawn`'s call and its `GoAlloc` of `f` step), whose call ends
normally (`⌜v = #()⌝`: a forked goroutine that panics is not a thread the fork rule takes). The
committed spec takes `f : val` and `{{ fun _ => threadTok }}`, which a panic value satisfies. -/
theorem Cluster.spawn.wp_proof (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    ∀ [ThreadBoundLe GF (2 ^ 31)] (c : Loc) (f : GoFunc) (k : w32) (P : IProp GF),
      sint.Z k < 2 ^ 31 - 1 →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.antithesis ∗
        sync.join.ownAdder (c.[H.Cluster, go!"behWg"]) k P ∗ threadTok ∗
        (threadTok -∗ WP (App (Val #f) (Val #())) {{ v, ⌜v = #()⌝ ∗ threadTok }}) }}
      (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Cluster.ty @!! go!"spawn")) (Val #f))
    {{ RET #(); sync.join.ownAdder (c.[H.Cluster, go!"behWg"]) (k + W32 1) iprop(P ∗ True) ∗ threadTok }} := by
  intro _ c f k P hk
  wp_start as ⟨Had, Htok, Hf⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_auto
  wp_apply (sync.join.WaitGroup.wp_Add_of wp_Add iprop(True) _ _ k) $$ [Had] as ⟨Had, Hdone⟩
  · iframe Had
    ipureintro; exact hk
  try wp_auto
  wp_apply wp_fork_tok_body $$ [Hf Hdone c f]
  · iintro Htt
    try wp_auto
    wp_bind (App (Val #f) (Val #()))
    iapply wp_wand $$ (Hf $$ Htt)
    iintro %v ⟨%hv, Htt⟩
    subst hv
    try wp_auto
    wp_apply (sync.join.WaitGroup.wp_Done_of wp_Done iprop(True) _) $$ [Hdone]
    · iframe Hdone
    try wp_auto
    iframe Htt
    try (ipureintro; rfl)
  try wp_auto
  iapply HΦ
  iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
