/-
Ghost steps that move a replica's state and its executor's progress only (the executor's steps,
`BeTheLeader`, the peer order): the authority's replica part and the fragments move together.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.GhostBasic

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [G : GooseGlobalGS .hasLC GF] [π : NetProtoGS]

/-- The replica's state moves (and nothing else it tracks). -/
theorem ghost_rep_step (γ : EpNames) (i : Nat) (S S' : Sys) (σ σ' : RState) (hi : i < nR)
    (hrest : ∀ j, j ≠ i → sameAt S S' j)
    (hrep : S'.rep i = σ') (hcrt : ∀ q, zz (σ.crtInstance q) ≤ zz (σ'.crtInstance q))
    (hob : S'.outbox i = S.outbox i) (hpd : S'.pending i = S.pending i)
    (hcur : S'.execCur i = S.execCur i) (hidx : S'.execIdx i = S.execIdx i)
    (hch : S'.proposeChan i = S.proposeChan i) :
    sysAuthB (GF := GF) γ S -∗ repFragB γ i σ ==∗ sysAuthB γ S' ∗ repFragB γ i σ' := by
  iintro Ha Hf
  ihave ⟨Hi, Hclose⟩ := sysAuthB_acc γ S i hi $$ Ha
  ihave %hσ := rep_agree γ S i σ $$ Hi Hf
  iunfold sysAuthRepB at Hi
  iunfold repFragB at Hf
  icases Hi with ⟨⟨%L, HL, %hL⟩, Hob, Hpd, Hcu, Hch⟩
  icases Hf with ⟨-, %L', HL', %hL'⟩
  ihave %hLL := rsAuth_agree _ _ _ _ _ $$ HL HL'
  obtain ⟨-, rfl⟩ := hLL
  imod rep_update γ i L σ σ' hi hL'.1 hL'.2 hcrt $$ HL HL' with ⟨HL, Hf⟩
  imodintro
  iframe Hf
  iapply Hclose $$ %S' %hrest
  iunfold sysAuthRepB
  rw [hrep, hob, hpd, hcur, hidx, hch]
  iframe

/-- The replica's state and its executor's progress move. -/
theorem ghost_rep_cur_step (γ : EpNames) (i : Nat) (S S' : Sys) (σ σ' : RState)
    (cur cur' : List InstId) (idx idx' : Nat) (hi : i < nR)
    (hrest : ∀ j, j ≠ i → sameAt S S' j)
    (hrep : S'.rep i = σ') (hcrt : ∀ q, zz (σ.crtInstance q) ≤ zz (σ'.crtInstance q))
    (hob : S'.outbox i = S.outbox i) (hpd : S'.pending i = S.pending i)
    (hcur : S'.execCur i = cur') (hidx : S'.execIdx i = idx')
    (hch : S'.proposeChan i = S.proposeChan i) :
    sysAuthB (GF := GF) γ S -∗ repFragB γ i σ -∗ curFragB γ i cur idx ==∗
      sysAuthB γ S' ∗ repFragB γ i σ' ∗ curFragB γ i cur' idx' := by
  iintro Ha Hf Hc
  ihave ⟨Hi, Hclose⟩ := sysAuthB_acc γ S i hi $$ Ha
  ihave %hσ := rep_agree γ S i σ $$ Hi Hf
  iunfold sysAuthRepB at Hi
  iunfold repFragB at Hf
  iunfold curFragB at Hc
  icases Hi with ⟨⟨%L, HL, %hL⟩, Hob, Hpd, Hcu, Hch⟩
  icases Hf with ⟨-, %L', HL', %hL'⟩
  icases Hc with ⟨-, Hc⟩
  ihave %hLL := rsAuth_agree _ _ _ _ _ $$ HL HL'
  obtain ⟨-, rfl⟩ := hLL
  imod rep_update γ i L σ σ' hi hL'.1 hL'.2 hcrt $$ HL HL' with ⟨HL, Hf⟩
  imod gvar_update _ _ _ (cur', idx') $$ Hcu Hc with ⟨Hcu, Hc⟩
  imodintro
  iframe Hf
  isplitl [Hclose HL Hob Hpd Hcu Hch]
  · iapply Hclose $$ %S' %hrest
    iunfold sysAuthRepB
    rw [hrep, hob, hpd, hcur, hidx, hch]
    iframe
  · iunfold curFragB
    iframe Hc
    ipureintro; exact hi

end ghost

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
