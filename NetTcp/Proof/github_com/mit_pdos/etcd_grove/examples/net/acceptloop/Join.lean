/-
`Call`'s wait group of its two goroutines (`examples/net/acceptloop/acceptloop.go`: `wg.Add(2)`
before the `go` statements).

Perennial's join idiom (`sync.join`, `WaitGroupJoin.lean`) adds one goroutine per `Add(1)`; `Call`
adds both at once. `wp_Add_many`: one `Add(n)` gives a `Done` right for each of the `n`
propositions `Ps` and the permission to `Wait` for all of them, from `WaitGroup.Add`'s spec, as
`WaitGroupJoin`'s `wp_Add_of` (the counter below `2 ^ 31`: `n < 2 ^ 31 - 1`, the caller's). A copy
of `examples/mvccrand/RunChecksJoin.lean`'s (the main tree, which `NetTcp` does not import): a
candidate for Perennial's `WaitGroupJoin`.
-/
module

public import Perennial.Proof.sync.WaitGroupJoin
public import Perennial.Proof.TokSet
public import Perennial.Algebra.AuthProp

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode Perennial.sync Perennial.sync.join

namespace github_com.mit_pdos.etcd_grove.examples.net.acceptloop

section join
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

/-- The ghost part of `n` additions: each proposition's `Done` right, the authority's proposition
implying all of them. -/
theorem join_add_many (wg : Loc) (γ : WaitGroupJoinNames) :
    ∀ (Ps : List (IProp GF)) (P0 : IProp GF) (m : Nat),
    isWgjInv (GF := GF) wg γ ∗ ownApropAuth γ.wgApropGn P0 m ∗
        ownTokAuthDfrac γ.wgNotDoneGn (DFrac.own 1) m ⊢
      |==> ∃ P1 : IProp GF, ownApropAuth γ.wgApropGn P1 (m + Ps.length) ∗
        ownTokAuthDfrac γ.wgNotDoneGn (DFrac.own 1) (m + Ps.length) ∗
        (P1 -∗ P0 ∗ [∗list] P ∈ Ps, P) ∗ [∗list] P ∈ Ps, ownDoneDef wg P
  | [], P0, m => by
    iintro ⟨-, Ha, Hn⟩
    imodintro
    iexists P0
    simp only [List.length_nil, Nat.add_zero]
    iframe Ha Hn
    isplitl
    · iintro H; iframe H; iapply BigSepL.bigSepL_nil.2; itrivial
    · iapply BigSepL.bigSepL_nil.2; itrivial
  | P :: Ps, P0, m => by
    iintro ⟨#Hinv, Ha, Hn⟩
    imod ownApropAuth_add P γ.wgApropGn P0 m $$ Ha with ⟨Ha, HP⟩
    imod ownTokAuth_S γ.wgNotDoneGn m $$ Hn with ⟨Hn, Ht⟩
    imod join_add_many wg γ Ps iprop(P0 ∗ P) (m + 1) $$ [Ha Hn] with ⟨%P1, Ha, Hn, Himp, Hs⟩
    · iframe Hinv Ha Hn
    imodintro
    iexists P1
    simp only [List.length_cons]
    rw [show m + (Ps.length + 1) = m + 1 + Ps.length by omega]
    iframe Ha Hn
    isplitl [Himp]
    · iintro H1
      icases Himp $$ H1 with ⟨⟨H0, HQ⟩, Hrest⟩
      iframe H0
      iapply BigSepL.bigSepL_cons.2
      iframe HQ Hrest
    · iapply BigSepL.bigSepL_cons.2
      iframe Hs
      unfold ownDoneDef
      iexists γ
      iframe HP Ht Hinv

/-- **`wg.Add(n)` for `n` goroutines** (see the file header), with no goroutine added since the
last `Wait`. -/
theorem wp_Add_many (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (wg : Loc) (P : IProp GF) (Ps : List (IProp GF)) (hn : Ps.length < 2 ^ 31 - 1) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg (W32 0) P }}
      (App (Val (wg @!! go.GoType.PointerType WaitGroup.ty @!! go!"Add"))
        (Val #(W64 (Ps.length : Int))))
    {{ RET #(); ownAdder wg (W32 (Ps.length : Int)) iprop(P ∗ [∗list] Q ∈ Ps, Q) ∗
        [∗list] Q ∈ Ps, ownDone wg Q }} := by
  wp_start_folded as Ha
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core wp_Add wg (W64 (Ps.length : Int)) γ.wgGn (wgjN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (wg_mask_ndot_ne wgjN "wg" "inv" (by decide))
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  icombine Hadded Hadded_inv gives % ⟨_, Heq⟩
  subst Heq
  have h0 : sint.nat (W32 0) = 0 := rfl
  rw [h0] at Hctr_inv
  have h1 : sint.Z (W32 (sint.Z (W64 (Ps.length : Int)))) = Ps.length := by word
  have h2 : W32 (sint.Z (W64 (Ps.length : Int))) = W32 (Ps.length : Int) := by word
  rw [h1, h2]
  isplitr
  · ipureintro
    simp only [sint.nat, sint.Z] at *
    omega
  iright
  iframe Hno_waiters
  iintro Hno_waiters Hwg_ctr_inv
  imod Hmask with -
  ihave Hadded := (ownTokAuth_halves γ.wgNotDoneGn 0).2 $$ [Hadded Hadded_inv]
  · rw [h0]; iframe
  rw [h0]
  imod join_add_many wg γ Ps P0 0 $$ [Haprop Hadded]
    with ⟨%P1, Haprop, Hadded, Himp, Hdones⟩
  · iframe Haprop Hadded
    unfold isWgjInv named
    isplit <;> iassumption
  icases (ownTokAuth_halves γ.wgNotDoneGn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  have hn' : sint.nat (W32 (Ps.length : Int)) = Ps.length := by
    simp only [sint.nat]; word
  have hctr : sint.Z (ctr + W32 (Ps.length : Int)) = sint.Z ctr + Ps.length := by word
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hdone_aprop_inv Hdone_P_inv] with -
  · inext
    iexists (ctr + W32 (Ps.length : Int)), (0 + Ps.length), done, Pdone
    iframe
    ipureintro
    constructor <;> omega
  imodintro
  iapply HΦ
  simp only [ownDone_unseal]
  isplitl [Hno_waiters Haprop Hadded HimpliesP Himp]
  · iexists γ, P1
    rw [hn']
    rw [Nat.zero_add]
    iframe Hno_waiters Haprop Hadded
    isplitr
    · ipureintro; word
    isplitl
    · iintro H1
      icases Himp $$ H1 with ⟨H0, HQ⟩
      iframe HQ
      iapply HimpliesP $$ H0
    unfold isWgjInv named
    isplit <;> iassumption
  · iexact Hdones

end join

end github_com.mit_pdos.etcd_grove.examples.net.acceptloop
end Perennial
