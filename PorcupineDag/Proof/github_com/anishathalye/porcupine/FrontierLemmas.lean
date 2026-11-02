/- Lean-first (no Rocq counterpart).

# Lemmas of the frontier helpers' proofs (2026-11-02)

For `chains.isComplete`, `chains.removeFromFrontier` and `chains.addToFrontier`: what every
client's struct says purely (`clientFacts`, `clients_facts`), the client of a head operation
(`clientOf_opAt`), and `Check`'s answer on unrelated head operations (`linOrder_unrelated`).
-/
module

public import PorcupineDag.Proof.github_com.anishathalye.porcupine.ChainsOwn
public import PorcupineDag.Proof.github_com.anishathalye.porcupine.Oracles

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.anishathalye.porcupine

open Theory

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.anishathalye.porcupine.Assumptions]

/-- What client `c`'s struct says purely: its id, its head, its operations slice's length. -/
def clientFacts (cs : List (List Nat)) (st : ChSt) (c : Nat) (cv : client) : Prop :=
  sint.Z cv.id' = c ∧ sint.Z cv.head' = st.head c ∧
  sint.nat cv.cltOps'.len = (chain cs c).length ∧ 0 ≤ sint.Z cv.cltOps'.len

theorem clientOwn_facts (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (c : Nat)
    (cv : client) :
    clientOwn h cs st c cv ⊢ clientOwn (GF := GF) h cs st c cv ∗ ⌜clientFacts cs st c cv⌝ := by
  unfold clientOwn
  iintro ⟨%Hc, %cos, Hcl, %Hok, Hfu⟩
  ihave %Hlen := ownSlice_len $$ Hcl
  isplitl
  · isplitr
    · ipureintro; exact Hc
    iexists cos
    iframe
    ipureintro; exact Hok
  · ipureintro
    exact ⟨Hc.1, Hc.2.1, by rw [← Hlen.1, Hok.1], Hlen.2⟩

/-- Every client's `clientFacts`. -/
theorem clients_facts (h : List (Op OpV)) (cs : List (List Nat)) (st : ChSt) (cvs : List client) :
    ([∗list] c ↦ cv ∈ cvs, clientOwn h cs st c cv) ⊢
      ([∗list] c ↦ cv ∈ cvs, clientOwn (GF := GF) h cs st c cv) ∗
      ⌜∀ j cv, cvs[j]? = some cv → clientFacts cs st j cv⌝ := by
  iintro Hl
  ihave Hl := BigSepL.bigSepL_mono (fun {k x} _ => clientOwn_facts (GF := GF) h cs st k x) $$ Hl
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hl with ⟨Hl, Hp⟩
  ihave %Hp := BigSepL.bigSepL_pure_intro $$ Hp
  iframe Hl
  ipureintro; exact Hp

end heap

end github_com.anishathalye.porcupine

end Perennial
