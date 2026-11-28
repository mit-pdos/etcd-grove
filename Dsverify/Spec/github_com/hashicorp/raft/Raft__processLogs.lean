/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/Raft__processLogs.lean (241f27e).
-/
/-
`raft.(*Raft).processLogs`'s spec (raft-internal interface).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.core.Laws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*Raft).processLogs`: Called by the main goroutine with an index of its durable prefix: sends
the committed entries `(a, idx]` to the FSM in batches (with the futures of `futures`, each a
dispatched future of the server's entry at its index, `nil` for a follower; stage 3: the entries
read from the log store, which holds them: past the compaction frontier `c ≤ a`, `logCell`), and sets
`lastApplied` to `max a idx` (stage 3: `lastApplied`'s ghost is a `mono_nat`, `applLb`). Futures at
indexes `≤ a` are dropped. -/
abbrev github_com.hashicorp.raft.Raft.processLogs.spec : Prop :=
  ∀ (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (idx : w64) (fm : GoMap)
    (M : GMap w64 Loc) (s : SState) (a c : Nat) (tid : Nat),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗ srvV rc s ∗
     ⌜uint.nat idx ≤ s.dur.1⌝ ∗
     fsmProd γ rc a ∗ monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
     monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ ⌜c ≤ a⌝ ∗ rtok tid ∗
     (⌜fm = null ∧ M = ∅⌝ ∨ fm ↦$ M) ∗
     ([∗map] k ↦ f ∈ M, ∃ e : Entry, futResp γ rc i f (uint.nat k) e ∗
        ⌜ent s.log (uint.nat k) = some e⌝) }}
    (App (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"processLogs")) (Val #idx)) (Val #fm))
  {{ RET #(); srvV rc s ∗ fsmProd γ rc (Max.max a (uint.nat idx)) ∗
      monoNatAuthOwn rc.dur.applied (1 : Qp).half (Max.max a (uint.nat idx)) ∗
      monoNatAuthOwn rc.dur.comp (1 : Qp).half c ∗ rtok tid ∗
      (⌜fm = null⌝ ∨ fm ↦$ M) }}

end spec

end Perennial
