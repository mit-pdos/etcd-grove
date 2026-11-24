/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/B/BootLem.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit B3: small laws for `NewReplica`'s proof (the executor's start state).
-/
module

public import Dsverify.Proof.gryff.B.Handler

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.unitB

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net proto
open model replica2
open Perennial.gryff.replica (XS stackOwn stackElems euOwn)

attribute [local instance] GooseGlobalGS.gooseInvGS

section
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [π : NetProtoGS] [sem : go.Semantics]

/-- The executor's own state at the empty search state (H-X-2): the search state's half, the
package's empty `stack` (`gryffGlobals`'), `ExecedUpTo` at `-1`. -/
theorem execPriv2_init (ρ : Repl2Names) (h : Loc) (euS : GoSlice) :
    ghostVar ρ.xs (1 : Qp).half xs0 ∗
      (∃ s : GoSlice, globalAddr src.gryff.stack ↦ s ∗ s ↦* ([] : List Loc) ∗
        ownSliceCap Loc s (DFrac.own 1) ∗ ⌜0 < sint.Z s.cap ∧ sint.Z s.cap < 2 ^ 60⌝) ∗
      h.[src.gryff.EPaxosRMWHandler, go!"ExecedUpTo"] ↦□ euS ∗ euOwn euS [] ⊢
    execPriv2 ρ h xs0 [] := by
  iintro ⟨Hx, ⟨%s, Hs, Hss, Hc, %Hcap⟩, #He, Heu⟩
  unfold execPriv2 stackOwn
  iframe Hx
  isplitl [Hs Hss Hc]
  · iexists s, []
    iframe
    isplitr
    · ipureintro; exact ⟨rfl, Hcap⟩
    unfold stackElems
    iapply BigSepL.bigSepL_nil.2; iempintro
  iexists euS
  iframe #
  rw [show xs0.1 = [] from rfl]
  iexact Heu

theorem list14 {α : Type _} (l : List α) (h : l.length = 14) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13, l = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13] := by
  rcases l with _ | ⟨a0, l⟩
  · simp at h
  rcases l with _ | ⟨a1, l⟩
  · simp at h
  rcases l with _ | ⟨a2, l⟩
  · simp at h
  rcases l with _ | ⟨a3, l⟩
  · simp at h
  rcases l with _ | ⟨a4, l⟩
  · simp at h
  rcases l with _ | ⟨a5, l⟩
  · simp at h
  rcases l with _ | ⟨a6, l⟩
  · simp at h
  rcases l with _ | ⟨a7, l⟩
  · simp at h
  rcases l with _ | ⟨a8, l⟩
  · simp at h
  rcases l with _ | ⟨a9, l⟩
  · simp at h
  rcases l with _ | ⟨a10, l⟩
  · simp at h
  rcases l with _ | ⟨a11, l⟩
  · simp at h
  rcases l with _ | ⟨a12, l⟩
  · simp at h
  rcases l with _ | ⟨a13, l⟩
  · simp at h
  rcases l with _ | ⟨_, l⟩
  · exact ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, rfl⟩
  · simp at h

/-- Replica id `i`'s receive cursors at its start (`idSlotRes`'), as `connectRes` holds them. -/
theorem rxCur_split (γ : ProtoNames) (i : Fin 3) :
    rxCurTok (GF := GF) γ 0 i 0 ∗ rxCurTok γ 1 i 0 ∗ rxCurTok γ 2 i 0 ⊢
      ([∗list] q ∈ peers i, rxCurTok γ q i 0) ∗ rxCurTok γ i i 0 := by
  iintro ⟨H0, H1, H2⟩
  obtain ⟨i, hi⟩ := i
  rcases i with _ | _ | _ | i
  · simp only [peers, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.filter,
      decide_eq_true_eq]
    isimp [BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
    iframe
  · simp only [peers, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.filter,
      decide_eq_true_eq]
    isimp [BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
    iframe
  · simp only [peers, List.finRange, List.ofFn, Fin.foldr, Fin.foldr.loop, List.filter,
      decide_eq_true_eq]
    isimp [BigSepL.bigSepL_cons, BigSepL.bigSepL_nil]
    iframe
  · omega

/-- Replica id `i`'s prediction, from all three's. -/
theorem predsSet_at (γ : ProtoNames) (i : Fin 3) :
    predsSet (GF := GF) γ ⊢ ∃ ws, predIdIs γ i.val ws := by
  unfold predsSet
  iintro ⟨%w0, %w1, %w2, H0, H1, H2⟩
  obtain ⟨i, hi⟩ := i
  rcases i with _ | _ | _ | i
  · iexists w0; iexact H0
  · iexists w1; iexact H1
  · iexists w2; iexact H2
  · omega

/-- Replica node `k`'s address, its IP and port (port: the kit's `portAddr k`, the lab's
`addrOf k` / `ipOf k` at `10.77.0.x:700x`). -/
theorem addrOf_split (k : Nat) (hk : k < 3) :
    portAddr k = go!"127.0.0.1" ++ go!":" ++ [go!"7502", go!"7503", go!"7504"].getD k go!"" ∧
      replicaAddrs.getD k go!"" = portAddr k := by
  rcases k with _ | _ | _ | k
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩
  · omega

/-- `PreferredPeerOrder`'s entries for replica id `id < 3` of three (N-9's list). -/
theorem ppo_list (id : w64) (hid : uint.nat id < 3) (ps : List w32) (hlen : ps.length = 3)
    (hv : ∀ m : Nat, m < 3 → ps[m]? = some (netN.ppoVal id (W64 3) m)) :
    ps = [W32 ((((uint.nat id : Nat) : Int) + 1) % 3), W32 ((((uint.nat id : Nat) : Int) + 2) % 3),
      W32 ((uint.nat id : Nat) : Int)] := by
  rcases ps with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, ps⟩⟩⟩⟩ <;> simp at hlen
  have ha := hv 0 (by decide)
  have hb := hv 1 (by decide)
  have hc := hv 2 (by decide)
  simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at ha hb hc
  subst ha hb hc
  have hidc : id = W64 0 ∨ id = W64 1 ∨ id = W64 2 := by
    have h3 : id.toNat < 3 := by simpa [uint.nat, uint.Z] using hid
    rcases h : id.toNat with _ | _ | _ | n
    · left; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · right; left; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · right; right; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
    · omega
  rcases hidc with rfl | rfl | rfl <;> decide

theorem xs0_facts : xs0.1 = [] ∧ ∀ u, xs0.numF u = 0 := by
  refine ⟨rfl, fun u => ?_⟩
  unfold XS.numF xs0
  simp

end

end Perennial.gryff.unitB
