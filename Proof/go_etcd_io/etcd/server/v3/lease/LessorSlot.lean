/-
**The lessor's heap-free history slot** (#50 F2, 2026-11-26; `notes/specs-only/ledger.md`, "2026-11-26:
`lessorAbsentStays_dist.law`"; `notes/etcd-dist-n9b.md` §11). Lean-first (no Rocq counterpart).

A lessor's reader invariant `lessorRdInv γl` is stated over the heap of the machine that runs the lessor
(`lessorRdBody` holds `lsF … ↦□` facts), so a client at another machine cannot take it as a premise.
What a client needs of it is heap-free in substance: the history's `histOnce` (`lessorAt_absent_stays`).

- `lessorHistOk γl`: that law, stated over `lessorAt` alone (persistent, heap-free), at the mask a client
  has with the slot open. The member proves it from its reader invariant when it makes the lessor.
- `lessorSlot γl`: the start's invariant for the lessor name `γl` it chooses before any machine runs
  (P-L1): either half of `γl`'s ghost map's authority at `∅` (the lessor not made yet; the member holds the
  other half and `NewLessor` takes both) or `lessorHistOk γl` (made and published in the same step). A
  lessor fact `lessorAt γl i σ` holds a pin of `γl` (`lessorPinR`), which the empty authority excludes, so a
  client holding both is in the second case: `lessorSlot_absent_stays`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.LessorHist

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open go_etcd_io.etcd.server.v3.lease
open Iris Iris.BI Iris.ProofMode

/-- The namespace of the start's lessor slots (`lessorSlot`), disjoint from the lessor's own. -/
def lessorSlotN : Namespace := nroot .@ "lessor_slot"

section slot
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [Gg : GooseGlobalGS .hasLC GF] [GoLocalContext]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]
attribute [local instance] GooseGlobalGS.gooseInvGS

/-- **The lessor `γl`'s history law** (persistent, heap-free: it mentions only `lessorAt`): a lease
absent from the history after it was in it stays absent, at the mask a client has with the slot open.
The member that makes the lessor proves it from its reader invariant (`lessorAt_absent_stays`, whose
`lessorRdInv` is over the member's heap) and publishes it in the slot. -/
def lessorHistOk (γl : GName) : IProp GF :=
  iprop(□ ∀ (i k j : Nat) (σ ρ τ : LSnap) (id : w64),
    ⌜(σ.1.lookup id).isSome ∧ i ≤ k ∧ ρ.1.lookup id = none ∧ k ≤ j⌝ -∗
    lessorAt γl i σ -∗ lessorAt γl k ρ -∗ lessorAt γl j τ -∗
    |={⊤ \ ↑lessorSlotN}=> ⌜τ.1.lookup id = none⌝)

instance lessorHistOk_persistent (γl : GName) : Persistent (lessorHistOk (GF := GF) γl) := by
  unfold lessorHistOk; infer_instance

/-- **The start's slot for the lessor name `γl`** (persistent): until the member's `NewLessor` makes the
lessor at `γl`, half of `γl`'s ghost map's authority at `∅` (the member holds the other half); after, the
lessor's history law (`lessorHistOk`). -/
def lessorSlot (γl : GName) : IProp GF :=
  iprop(inv lessorSlotN iprop(ghostMapAuth γl (1 : Qp).half (∅ : GMap Bool LessorGV) ∨ lessorHistOk γl))

instance lessorSlot_persistent (γl : GName) : Persistent (lessorSlot (GF := GF) γl) := by
  unfold lessorSlot; infer_instance

/-- **A lessor fact excludes the empty authority**: a pin of `γl` (in every `lessorAt γl i σ`) is not
in `∅`. -/
theorem lessorAt_not_empty (γl : GName) (i : Nat) (σ : LSnap) (q : Qp) :
    ghostMapAuth (GF := GF) γl q (∅ : GMap Bool LessorGV) ∗ lessorAt γl i σ ⊢ False := by
  unfold lessorAt lessorPinR lessorPinAll
  iintro ⟨Ha, %γr, ⟨%lp, %γga, %γcl, #Hp⟩, -⟩
  ihave %Hl := ghost_map_lookup $$ Ha Hp
  exact absurd Hl (by simp)

/-- **A client's "absent stays absent" at the start's lessor name** (heap-free form of
`lessorAt_absent_stays`): from the slot of `γl` and three snapshots of its history at `i ≤ k ≤ j`, the
lease `id` in the first and not in the second, it is not in the third. It spends a later credit: the slot
publishes the law, which is not timeless, in an invariant opened under a later. -/
theorem lessorSlot_absent_stays (γl : GName) (i k j : Nat) (σ ρ τ : LSnap) (id : w64)
    (hσ : (σ.1.lookup id).isSome) (hik : i ≤ k) (hρ : ρ.1.lookup id = none) (hkj : k ≤ j) :
    £ 1 ∗ lessorSlot (GF := GF) γl ∗ lessorAt γl i σ ∗ lessorAt γl k ρ ∗ lessorAt γl j τ ⊢
      |={⊤}=> ⌜τ.1.lookup id = none⌝ := by
  iintro ⟨Hlc, #Hs, #Hi, #Hk, #Hj⟩
  iunfold lessorSlot at Hs
  iinv Hs with Hb Hclose
  icases Hb with (>Ha | #Hr)
  · iexfalso
    iapply lessorAt_not_empty γl i σ (1 : Qp).half
    iframe Ha Hi
  · imod lc_fupd_elim_later (E := ⊤ \ ↑lessorSlotN) $$ Hlc Hr with #Hr'
    iunfold lessorHistOk at Hr'
    have hall : (σ.1.lookup id).isSome ∧ i ≤ k ∧ ρ.1.lookup id = none ∧ k ≤ j := ⟨hσ, hik, hρ, hkj⟩
    imod Hr' $$ %i %k %j %σ %ρ %τ %id %hall Hi Hk Hj with %Hτ
    imod Hclose $$ [] with -
    · inext; iright; iexact Hr
    imodintro
    ipureintro; exact Hτ

end slot

end lease
end EtcdGrove
end Perennial
