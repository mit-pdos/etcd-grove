/-
Lean-first (no Rocq counterpart). #33 parity B1: the steps the proofs of `node.step` and the other
inputs share beyond `HarnessInput.lean`'s:
- `lcpLen_self`: an input that keeps the log keeps the in-progress boundary at the log's end;
- `nodeOwn_drained_reset`: after a drain, the cause cell reset (`n.cause = nil`), node `j` between
  inputs again (S4's, over `Fin R.N`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.HarnessInput

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- A list's common prefix with itself is all of it. -/
theorem lcpLen_self : ∀ (l : List EntryM), lcpLen l l = l.length
  | [] => by simp [lcpLen]
  | a :: l => by
    unfold lcpLen
    simp only [List.length_cons, lcpLen_self l, ite_true]

/-- **The run's mode without B1's off features** (`ModeRun`: `γ.R.md = scopeMd γ.scope`; `DrainB1`'s
scope bits): no snapshots, no conf changes, no forwarding, no async storage. -/
theorem rMd_flags {s : H.Scope} {m : H.Mode} {R : AntSim.RunCfg} (hmr : ModeRun s m R)
    (hb1 : DrainB1 s m) :
    R.md.snapshots = false ∧ R.md.confChanges = false ∧ R.md.forwarding = false ∧
      R.md.async = false := by
  rw [hmr.2.2.2.2.1]
  obtain ⟨-, -, -, -, -, -, h1, h2, h3, h4⟩ := hb1
  exact ⟨h1, h2, h3, h4⟩

/-- A transfer request keeps the log (`TransferEndR`: kept, or a leader's sends). -/
theorem transferEndR_log {id to : w64} {r r' : RState} (h : TransferEndR id r to r') :
    r'.p.log = r.p.log := by
  rcases AntSim.transferEndR_p h with h | ⟨-, ms, -, h⟩
  · rw [h]
  · rw [h]; rfl

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]

/-- **After a drain, the cause cell reset** (`n.cause = nil`, `node.step`'s last line): node `j` is
between inputs again. -/
theorem nodeOwn_drained_reset (c : Loc) (γ : AntNames) (j : Fin γ.R.N) (n : Loc) (v : AntSim.NodeView) :
    nodeOwn (GF := GF) c γ j n v .drained ⊢
      ∃ cl : Loc, n.[H.node, go!"cause"] ↦ cl ∗
        (n.[H.node, go!"cause"] ↦ (null : Loc) -∗ nodeOwn c γ j n v .idle) := by
  unfold nodeOwn
  iintro ⟨%d, %rn, %ms, %hsl, %cl, %csl, %role, %applied, #Hd, Hmem, Hrn, Hms, Hrole, Hhs, Hcause,
    Happ, Hconf, Hv, Hl, %HN, Hdisk, %si, %rs, %qs, %ip, %r, Hstor, %Hsto, Hraw, Hnr, %Hrv, #Hhsro,
    #Hcs, %Hc0, %Hph, -⟩
  iexists cl
  iframe Hcause
  iintro Hcause
  iexists d, rn, ms, hsl, null, csl, role, applied
  iframe Hd Hmem Hrn Hms Hrole Hhs Hcause Happ Hconf Hv Hl
  isplitr
  · ipureintro; exact HN
  dsimp only
  iframe Hdisk
  iexists si, rs, qs, ip, r
  iframe Hstor Hraw Hnr Hhsro Hcs
  ipureintro
  exact ⟨Hsto, Hrv, Hc0, Hph.1, Hph.2.1, Hph.2.2.1, Hph.2.2.2.1, Hph.2.2.2.2, rfl⟩

end laws

end AntHarness
end EtcdGrove
end Perennial
