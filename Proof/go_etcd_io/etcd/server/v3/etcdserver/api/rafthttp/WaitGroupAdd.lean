/-
**A local workaround**: the `WaitGroup` join idiom's `Add` for a delta of `4` (rafthttp stage 4d:
`pipeline.start` calls `p.wg.Add(connPerPipeline)`). Perennial's `sync.join.WaitGroup.wp_Add_of`
covers `Add(1)` only, though `WaitGroup.Add`'s spec takes any delta; the general `Add(n)` is
proposed for Perennial (`notes/perennial-changes.md`). The proof is `wp_Add_of`'s with four ghost
steps. Lean-first.
-/
module

public import Perennial.Proof.sync.WaitGroupJoin

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std OFE Iris.ProofMode sync.join

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : sync.Assumptions]

set_option maxHeartbeats 1000000 in
/-- The join idiom's `WaitGroup.Add(4)`: four `Done` permissions, each for `P'`. -/
theorem wgJoin_wp_Add4_of
    (wp_Add : sync.WaitGroup.Add.spec (GF := GF) (hG := hG))
    (P' : IProp GF) (wg : Loc) (P : IProp GF) (num_added : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.sync ∗ ownAdder wg num_added P ∗
        ⌜sint.Z num_added < 2 ^ 31 - 4⌝ }}
      (App (Val (wg @!! go.GoType.PointerType sync.WaitGroup.ty @!! go!"Add")) (Val #(W64 4)))
    {{ RET #(); ownAdder wg (num_added + W32 4) iprop(P ∗ P' ∗ P' ∗ P' ∗ P') ∗
        ownDone wg P' ∗ ownDone wg P' ∗ ownDone wg P' ∗ ownDone wg P' }} := by
  wp_start_folded as ⟨Ha, %Hoverflow⟩
  simp only [ownAdder_unseal, ownAdderDef]
  icases Ha with ⟨%γ, %P0, Ha⟩
  iNamed Ha
  iNamed Hinv
  wp_apply_core wp_Add wg (W64 4) γ.wgGn (wgjN.@"wg") $$ [] [-]
  · iframe #
  imod inv_acc (E := ⊤) (fun _ _ => CoPset.mem_full) $$ Hinv with ⟨Hi, Hclose⟩
  iapply fupd_mask_intro (sync.wg_mask_ndot_ne wgjN "wg" "inv" (by decide))
  iintro Hmask
  inext
  icases Hi with ⟨%ctr, %added, %done, %Pdone, Hi⟩
  iNamedSuffix Hi "_inv"
  iexists ctr
  iframe Hwg_ctr_inv
  icombine Hadded Hadded_inv gives % ⟨_, Heq⟩
  subst Heq
  have h1 : sint.Z (W32 (sint.Z (W64 4))) = 4 := by decide
  have h2 : W32 (sint.Z (W64 4)) = W32 4 := by decide
  rw [h1, h2]
  isplitr
  · ipureintro
    simp only [sint.nat, sint.Z] at *
    omega
  iright
  iframe Hno_waiters
  iintro Hno_waiters Hwg_ctr_inv
  imod Hmask with -
  imod ownApropAuth_add P' γ.wgApropGn P0 (sint.nat num_added) $$ Haprop with ⟨Haprop, Hd1⟩
  imod ownApropAuth_add P' γ.wgApropGn _ _ $$ Haprop with ⟨Haprop, Hd2⟩
  imod ownApropAuth_add P' γ.wgApropGn _ _ $$ Haprop with ⟨Haprop, Hd3⟩
  imod ownApropAuth_add P' γ.wgApropGn _ _ $$ Haprop with ⟨Haprop, Hd4⟩
  ihave Hadded := (ownTokAuth_halves γ.wgNotDoneGn (sint.nat num_added)).2 $$ [Hadded Hadded_inv]
  · iframe
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Ht1⟩
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Ht2⟩
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Ht3⟩
  imod ownTokAuth_S γ.wgNotDoneGn _ $$ Hadded with ⟨Hadded, Ht4⟩
  icases (ownTokAuth_halves γ.wgNotDoneGn _).1 $$ Hadded with ⟨Hadded, Hadded_inv⟩
  have hn : sint.nat (num_added + W32 4) = sint.nat num_added + 1 + 1 + 1 + 1 := by
    simp only [sint.nat] at *; word
  imod Hclose $$ [Hwg_ctr_inv Hadded_inv Hdone_toks_inv Hdone_aprop_inv Hdone_P_inv] with -
  · inext
    iexists (ctr + W32 4), (sint.nat num_added + 1 + 1 + 1 + 1), done, Pdone
    iframe
    ipureintro
    simp only [sint.nat] at *
    constructor <;> word
  imodintro
  iapply HΦ
  simp only [ownAdder_unseal, ownAdderDef, ownDone_unseal, ownDoneDef]
  isplitl [Hno_waiters Haprop Hadded HimpliesP]
  · iexists γ, iprop((((P0 ∗ P') ∗ P') ∗ P') ∗ P')
    rw [hn]
    iframe
    isplitr
    · ipureintro; simp only [sint.nat] at *; word
    isplitl
    · iintro ⟨⟨⟨⟨H0, H1⟩, H2⟩, H3⟩, H4⟩
      iframe H1 H2 H3 H4
      iapply HimpliesP $$ H0
    unfold isWgjInv named
    isplit <;> iassumption
  isplitl [Hd1 Ht1]
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption
  isplitl [Hd2 Ht2]
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption
  isplitl [Hd3 Ht3]
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption
  · iexists γ
    iframe
    unfold isWgjInv named
    isplit <;> iassumption

end proof

end EtcdGrove
end Perennial
