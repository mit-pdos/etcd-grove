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

/-- `spawn`'s call and its `GoAlloc` of `f` step as `f : GoFunc`; the goroutine's `f()` ends
normally (`⌜v = #()⌝`), then `behWg.Done()`. -/
theorem Cluster.spawn.wp_proof (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wp_Done : sync.WaitGroup.Done.spec (GF := GF) (hG := hG)) :
    Cluster.spawn.spec (GF := GF) (hG := hG) := by
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
  try wp_auto
  iapply HΦ
  iframe

end proof

end AntHarness
end EtcdGrove
end Perennial
