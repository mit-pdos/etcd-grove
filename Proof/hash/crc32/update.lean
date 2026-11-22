/-
The proof of `Spec/hash/crc32/update.lean` over the translated dispatch (`crc32.go:202-214`): once
`haveCastagnoli` is set (its invariant, `haveInv`), `updateCastagnoli` computes CRC-32C (`updSpec`);
the IEEE path is excluded, `tab` holding the Castagnoli table and `IEEETable` the IEEE one; otherwise
`simpleUpdate` over the Castagnoli table.
-/
module

public import Spec.hash.crc32.update
public import Spec.hash.crc32.simpleUpdate
public import Perennial.Proof.sync.atomic.Link

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [hash.crc32.Assumptions]

theorem hash.crc32.crcUpdate_castagnoli (c : w32) (bs : List w8) :
    _root_.Perennial.hash.crc32.crcUpdate _root_.Perennial.hash.crc32.castagnoliTableArr.arr c bs =
      _root_.Perennial.hash.crc32.crc32c c bs := rfl

theorem hash.crc32.update.wp_proof (hsimple : hash.crc32.simpleUpdate.spec (GF := GF) (hG := hG)) :
    hash.crc32.update.spec (GF := GF) (hG := hG) := by
  intro c tab s bs dq b
  wp_start as ⟨#Ht, Hs⟩
  ihave #Hf : (hash.crc32.crc32Init : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  iunfold hash.crc32.crc32Init at Hf
  icases Hf with ⟨⟨%tI, #HI, #HtI⟩, -, #Hinv⟩
  ihave %hne : ⌜tab ≠ tI⌝ $$ []
  · iintro %h
    subst h
    icombine Ht HtI gives %Heq
    exact absurd Heq.symm hash.crc32.ieeeTableArr_ne
  wp_auto
  wp_apply_core sync.atomic.Bool.wp_Load $$ [] [-]
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iunfold hash.crc32.haveInv at Hi
  icases Hi with ⟨%v, Hb, Hr⟩
  iexists v
  iframe Hb
  iintro Hb
  imod Hmask with _
  cases v
  · imod Hclose $$ [Hb Hr] with _
    · inext; iunfold hash.crc32.haveInv; iexists false; iframe
    imodintro
    try wp_auto
    rw [decide_eq_false hne]
    try wp_auto
    wp_apply hsimple $$ [Hs] as ⟨-, Hs⟩
    · iframe Hs; iexact Ht
    try wp_auto
    rw [hash.crc32.crcUpdate_castagnoli]
    iapply HΦ $$ Hs
  · simp only [↓reduceIte]
    icases Hr with ⟨#Hready, %u, #Hu, #Hus⟩
    imod Hclose $$ [Hb] with _
    · inext; iunfold hash.crc32.haveInv; iexists true; iframe; simp only [↓reduceIte]
      iframe #
    imodintro
    iunfold hash.crc32.castagnoliReady at Hready
    icases Hready with ⟨%t, #Hct, #Htt⟩
    try wp_auto
    by_cases htt : tab = t
    · subst htt
      simp only [_root_.decide_true]
      try wp_auto
      iunfold hash.crc32.updSpec at Hus
      wp_apply Hus $$ [Hs] as Hs
      · iexact Hs
      try wp_auto
      iapply HΦ $$ Hs
    · simp only [htt, _root_.decide_false]
      try wp_auto
      try wp_auto
      rw [decide_eq_false hne]
      try wp_auto
      wp_apply hsimple $$ [Hs] as ⟨-, Hs⟩
      · iframe Hs; iexact Ht
      try wp_auto
      rw [hash.crc32.crcUpdate_castagnoli]
      iapply HΦ $$ Hs

end proof

end EtcdGrove
end Perennial
