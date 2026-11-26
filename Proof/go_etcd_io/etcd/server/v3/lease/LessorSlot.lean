/-
**The lessor's heap-free history slot** (#50 F2, 2026-11-26; `notes/specs-only/ledger.md`, "2026-11-26:
`lessorAbsentStays_dist.law`"; `notes/etcd-dist-n9b.md` §11). Lean-first (no Rocq counterpart).

A lessor's reader invariant `lessorRdInv γl` is stated over the heap of the machine that runs the lessor
(`lessorRdBody` holds `lsF … ↦□` facts), so a client at another machine cannot take it as a premise.
What a client needs of it is heap-free in substance: the history's `histOnce` (`lessorAt_absent_stays`).

- `lessorRdInvAt γl`: the reader invariant at **some** machine's local state (`∃ L : GooseLocalGS GF`), a
  proposition over the global state `Gg` only. Any machine can hold it; its body is the member's.
- `lessorSlot γl`: the start's invariant for the lessor name `γl` it chooses before any machine runs
  (P-L1): either half of `γl`'s ghost map's authority at `∅` (the lessor not made yet; the member holds the
  other half and `NewLessor` takes both) or `lessorRdInvAt γl` (made). A lessor fact `lessorAt γl i σ`
  holds a pin of `γl` (`lessorPinR`), which the empty authority excludes, so a client holding both is in
  the second case: `lessorSlot_absent_stays`, the heap-free form of `lessorAt_absent_stays`.
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

/-- **The lessor `γl`'s reader invariant at some machine** (persistent; over the global state only):
`lessorRdInv γl` at the local state `L` of the machine whose heap holds the lessor. -/
def lessorRdInvAt (γl : GName) : IProp GF :=
  iprop(∃ L : GooseLocalGS GF, lessorRdInv (GF := GF) (hG := ⟨Gg, L⟩) γl)

instance lessorRdInvAt_persistent (γl : GName) : Persistent (lessorRdInvAt (GF := GF) γl) := by
  unfold lessorRdInvAt; infer_instance

/-- **The start's slot for the lessor name `γl`** (persistent): until the member's `NewLessor` makes the
lessor at `γl`, half of `γl`'s ghost map's authority at `∅` (the member holds the other half); after, the
lessor's reader invariant at the member (`lessorRdInvAt`). -/
def lessorSlot (γl : GName) : IProp GF :=
  iprop(inv lessorSlotN (ghostMapAuth γl (1 : Qp).half (∅ : GMap Bool LessorGV) ∨ □ lessorRdInvAt γl))

instance lessorSlot_persistent (γl : GName) : Persistent (lessorSlot (GF := GF) γl) := by
  unfold lessorSlot; infer_instance

/-- **A lessor fact excludes the empty authority**: a pin of `γl` (in every `lessorAt γl i σ`) is not
in `∅`. -/
theorem lessorAt_not_empty (γl : GName) (i : Nat) (σ : LSnap) (q : Qp) :
    ghostMapAuth (GF := GF) γl q (∅ : GMap Bool LessorGV) ∗ lessorAt γl i σ ⊢ False := by
  unfold lessorAt lessorPinR lessorPinAll
  iintro ⟨Ha, %γr, ⟨%lp, %γga, %γcl, #Hp⟩, -⟩
  ihave %Hl := ghost_map_lookup $$ Ha Hp
  exact absurd Hl (by simp [Iris.Std.PartialMap.get?]; rfl)

/-- **A client's "absent stays absent" at the start's lessor name** (heap-free form of
`lessorAt_absent_stays`): from the slot of `γl` and three snapshots of its history at `i ≤ k ≤ j`, the
lease `id` in the first and not in the second, it is not in the third. -/
theorem lessorSlot_absent_stays (γl : GName) (i k j : Nat) (σ ρ τ : LSnap) (id : w64) (E : CoPset)
    (hE : ↑lessorSlotN ⊆ E) (hE' : ↑lessorRdN ⊆ E) (hσ : (σ.1.lookup id).isSome) (hik : i ≤ k)
    (hρ : ρ.1.lookup id = none) (hkj : k ≤ j) :
    lessorSlot (GF := GF) γl ∗ lessorAt γl i σ ∗ lessorAt γl k ρ ∗ lessorAt γl j τ ⊢
      |={E}=> ⌜τ.1.lookup id = none⌝ := by
  iintro ⟨#Hs, #Hi, #Hk, #Hj⟩
  iunfold lessorSlot at Hs
  iinv Hs with Hb Hclose
  icases Hb with (>Ha | #Hr)
  · iexfalso
    iapply lessorAt_not_empty γl i σ (1 : Qp).half
    iframe Ha Hi
  · imod Hclose $$ [] with -
    · inext; iright; iexact Hr
    iunfold lessorRdInvAt at Hr
    icases Hr with ⟨%L, #Hrd⟩
    iapply (lessorAt_absent_stays (GF := GF) (hG := ⟨Gg, L⟩) γl i k j σ ρ τ id E hE' hσ hik hρ hkj)
    iframe Hrd Hi Hk Hj

end slot

end lease
end EtcdGrove
end Perennial
