/-
The proof of `KvNet/Spec/.../kvnet/startNode.lean` (2026-11-24, G5), generic in the store's seams:
the stats (their mutex), the first incarnation from the start resource (`startLaw`), and the node:
its fixed fields, and its mutex over the incarnation (`nodeLockInv`).
-/
module

public import KvNet.Spec.github_com.mit_pdos.etcd_grove.examples.raft.kvnet.startNode

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvnet

open Iris Iris.BI Iris.ProofMode Net go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [NetProtoGS] [StorageModel GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvnet.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]

theorem startNode.wp_proof (F : KvFacts GF) (rep : Loc → w64 → IProp GF) (stp : NodeStopper GF) :
    startNode.spec (GF := GF) (hG := hG) F rep stp := by
  intro cfg M f γ N AP R
  wp_start as ⟨#HM, HR, #Hctor, #Hstep, %Htr, #Hstop, #Hstart⟩
  try wp_auto
  -- the stats, their mutex
  generalize «$r0_ptr» = sp
  icases typedPointsto_split _ _ _ $$ «$r0» with Hs0
  simp only [TypedPointsto.typedPointstoDef]
  icases Hs0 with ⟨smu, sc, -⟩
  imod sync.init_Mutex (statsInv sp) ⊤ _ $$ smu [sc] with #Hstats
  · inext
    unfold statsInv
    iexists _
    iexact sc
  ihave #Hstats' : isStats sp $$ []
  · unfold isStats; iexact Hstats
  try wp_auto
  -- the first incarnation
  ihave #Hstart' := Hstart
  iunfold startLaw at Hstart'
  ihave #Hstart1 := Hstart' $$ %sp %f
  wp_apply Hstart1 $$ [$Hpkg $HM $HR $Hstats' $Hctor] as %r %tv ⟨%n, #Hrn, #Hrep, #Hn, Hstp⟩
  -- the node, its mutex over the incarnation
  generalize «$r0_ptr» = nd
  ihave Hnd := typedPointsto_split _ _ _ $$ «$r0»
  simp only [TypedPointsto.typedPointstoDef, named]
  icases Hnd with ⟨Hcfg, Hst, HnewT, Hmu, Hr, Ht, -⟩
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hcfg with #Hcfg
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hst with #Hst
  imod (typedPointsto_dfractional (GF := GF) _ _).dfractional_persist _ $$ HnewT with #HnewT
  imod sync.init_Mutex (nodeLockInv rep stp nd cfg M γ N cfg.ID') ⊤ _ $$ Hmu [Hr Ht Hstp] with #Hmu
  · inext
    iunfold nodeLockInv
    iexists r, tv, n
    iframe
  try wp_auto
  iapply HΦ
  iunfold isNodeS
  iexists cfg, M, sp, f
  isplitr
  · iexact Hcfg
  isplitr
  · ipureintro; rfl
  isplitr
  · iexact HM
  isplitr
  · iexact Hst
  isplitr
  · iexact Hstats'
  isplitr
  · iexact HnewT
  isplitr
  · iexact Hstep
  isplitr
  · ipureintro; exact Htr
  isplitr
  · iexists AP, R
    iframe Hctor Hstop Hstart
  iexact Hmu

end proof

end raft_kvnet
end EtcdGrove
end Perennial
