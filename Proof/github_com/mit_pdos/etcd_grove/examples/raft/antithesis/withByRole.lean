/-
Lean-first (no Rocq counterpart). #33 parity B1: the proof of
`Spec/github_com/mit_pdos/etcd_grove/examples/raft/antithesis/withByRole.lean`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.withByRole

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

theorem hasBit_or3 (h f : w32) (hf : (W32 1 ||| W32 2) &&& f = W32 0) :
    AntCheck.hasBit (h ||| W32 1 ||| W32 2) f = AntCheck.hasBit h f := by
  unfold AntCheck.hasBit
  have : (h ||| W32 1 ||| W32 2) &&& f = h &&& f := by
    rw [BitVec.or_assoc, BitVec.and_or_distrib_right, hf]; exact BitVec.or_zero
  rw [this]

theorem fieldRel_or3 {α β : Type} (h f : w32) (hf : (W32 1 ||| W32 2) &&& f = W32 0)
    (rel : α → β → Prop) (g : α) (o : Option β) :
    AntCheck.fieldRel (h ||| W32 1 ||| W32 2) f rel g o = AntCheck.fieldRel h f rel g o := by
  cases o <;> simp only [AntCheck.fieldRel, hasBit_or3 h f hf]

theorem fieldRO_or3 {α β : Type} (h f : w32) (hf : (W32 1 ||| W32 2) &&& f = W32 0)
    (rep : α → β → IProp GF) (g : α) (o : Option β) :
    AntCheck.fieldRO (h ||| W32 1 ||| W32 2) f rep g o = AntCheck.fieldRO h f rep g o := by
  cases o <;> simp only [AntCheck.fieldRO, hasBit_or3 h f hf]

theorem withByRole.wp_proof : withByRole.spec (GF := GF) (hG := hG) := by
  intro p ev by_ role
  wp_start as Hev
  iunfold eventOwn at Hev
  icases Hev with ⟨%g, Hp, %Hg, He, Hv, Ho, Hm, Hc⟩
  wp_auto
  iapply HΦ
  iunfold eventOwn
  dsimp only
  iexists _
  isplitl [Hp]
  · iExactEq Hp; rfl
  dsimp only
  have h1 : ∀ f : w32, (W32 1 ||| W32 2) &&& f = W32 0 →
      AntCheck.hasBit (g.Has' ||| W32 1 ||| W32 2) f = AntCheck.hasBit g.Has' f := fun f hf => hasBit_or3 _ f hf
  rw [fieldRO_or3 _ AntCheck.fEntries (by decide), fieldRO_or3 _ AntCheck.fVoters (by decide),
    fieldRO_or3 _ AntCheck.fOutgoing (by decide), fieldRO_or3 _ AntCheck.fMsg (by decide),
    fieldRO_or3 _ AntCheck.fCause (by decide)]
  iframe
  ipureintro
  obtain ⟨hE, hN, hB, hb, ha, hby, hro, ht, hvo, hc, hfi, hli, hlt, hap, hsn, hw, hmo, hix, hcx⟩ := Hg
  simp only [withByRoleM]
  refine ⟨hE, hN, hB, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h1 _ (by decide)]; exact hb
  · rw [h1 _ (by decide)]; exact ha
  · refine ⟨?_, rfl⟩
    unfold AntCheck.hasBit AntCheck.fBy
    intro heq
    have := congrArg (·.getLsbD 0) heq
    simp at this
  · refine ⟨?_, rfl⟩
    unfold AntCheck.hasBit AntCheck.fRole
    intro heq
    have := congrArg (·.getLsbD 1) heq
    simp at this
  all_goals first
    | (rw [fieldRel_or3 _ _ (by decide)]; assumption)
    | (simp only [AntCheck.fieldZ, AntCheck.fieldIs] at *; rw [fieldRel_or3 _ _ (by decide)]; assumption)

end proof

end AntHarness
end EtcdGrove
end Perennial
