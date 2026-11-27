/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/Raft__getLatestConfiguration.lean (241f27e).
-/
/-
The proof of `raft.(*Raft).getLatestConfiguration` (stage 3, D33): an atomic load of the
`latestConfiguration` pointer from `raftConf`'s invariant cell, then a read of the read-only copy.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__getLatestConfiguration
public import Perennial.Spec.sync.atomic.Pointer__Load

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft proto gprot

/-- (To open `latestCfgCell`'s `▷ ∃ cfg`.) -/
instance configuration_inhabited_glc : Inhabited Configuration := ⟨Perennial.zero_val Configuration⟩

theorem github_com.hashicorp.raft.Raft.getLatestConfiguration.wp_proof
    (wp_Load : sync.atomic.Pointer.Load.spec (GF := GF) (hG := hG)) :
    github_com.hashicorp.raft.Raft.getLatestConfiguration.spec (GF := GF) (hG := hG) := by
  intro r γ rc i
  wp_start as #His
  ihave #Hc := isRaft_conf r γ rc i $$ His
  unfold raftConf
  icases Hc with ⟨%c0, -, -, #Hinv⟩
  wp_auto
  wp_apply (wp_Load (T' := Configuration) Configuration.ty _ (DFrac.own 1))
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  unfold latestCfgCell
  icases Hi with ⟨%p, Hv, #Hp⟩
  iexists p
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists p; iframe; iframe #
  imodintro
  icases Hp with (%Hnil | ⟨%cfg, #Hp, #Hcfg⟩)
  · -- (API-S4-2) a non-member's cell: `Configuration{}`
    subst Hnil
    wp_auto
    iapply HΦ
    unfold cfgOpt
    iexists []
    isplitr
    · iapply ownSlice_nil
    · ipureintro; left; rfl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_auto
  rw [show decide (p = null) = false from decide_eq_false (by simpa using Hnn)]
  wp_auto
  iapply HΦ
  iexact Hcfg

end proof

end Perennial
