/-
(hraft_robust R3) The spec of `disk.(*Snaps).List` (`snap.go`).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.SinkDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section sec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]
variable [dur_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

open github_com.hashicorp.raft proto github_com.hashicorp.raft.examples.hraftnet.disk EtcdGrove

/-- `s.List()`: atomically, the latest's metadata (0 or 1 pointers). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.Snaps.List.spec : Prop :=
  ∀ (g : SnapGen) (s : Loc) (Qc : SnapshotMeta → List w8 → IProp GF) (Wf : IProp GF) (Φ : val → IProp GF),
    isSnaps g s Qc Wf ∗
      (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, snapsOwn g old ∗
        (snapsOwn g old ={∅,⊤ \ ↑storeN}=∗ ∀ (sl : GoSlice) (ps : List Loc),
          sl ↦* ps -∗
          (match old with
            | none => iprop(⌜ps = []⌝)
            | some (m, _) => iprop(∃ p : Loc, ⌜ps = [p]⌝ ∗ p ↦ m)) -∗
          Φ (PairV #sl #interface.nil))) ⊢
    WP (App (Val (s @!! go.GoType.PointerType Snaps.ty @!! go!"List")) (Val #())) {{ Φ }}

end sec

end Perennial
