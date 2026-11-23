/- Lean-first (no Rocq counterpart).

`errors.IsPathErrnoEof.spec` proved (2026-11-22): `io.EOF` and `io.ErrUnexpectedEOF` are `*errorString`s whose
messages are none of the four `Errno.Is` compares with (`errors.errorString_ne`), so the `Errno`'s `Is` answers
`false` (`ErrnoIsPost`); neither error of the tree (`pathErrno_walkTree`) is of their type: `errors.wp_Is_tree`
answers `false`.
-/
module

public import Spec.errors.IsPathErrnoEof
public import Proof.errors.PathErrnoTree

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions] [os.Assumptions] [_root_.Perennial.errors.Assumptions]

omit [syscall.Assumptions] [_root_.Perennial.errors.Assumptions] in
/-- `io.EOF` or `io.ErrUnexpectedEOF` is an `*errorString` whose message is one of theirs. -/
theorem eofVar_es (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢
      (globalAddr _root_.Perennial.io.EOF ↦□ eof ∨ globalAddr _root_.Perennial.io.ErrUnexpectedEOF ↦□ eof) -∗
      ∃ (x : Loc) (m : GoString), ⌜eof = esErr x ∧ (m = go!"EOF" ∨ m = go!"unexpected EOF")⌝ ∗
        x.[errors.errorString, go!"s"] ↦□ m := by
  iintro #Hio #Heof
  ihave #Hi := _root_.Perennial.io.isInit_access $$ Hio
  icases Hi with ⟨-, -, -, -, #HE, #HU, -⟩
  iunfold _root_.Perennial.errors.newVar at HE HU
  icases HE with ⟨%xE, #GE, #SE, -⟩
  icases HU with ⟨%xU, #GU, #SU, -⟩
  icases Heof with (#H | #H)
  · icombine H GE gives %h
    iexists xE, _
    iframe SE
    ipureintro; exact ⟨h, Or.inl rfl⟩
  · icombine H GU gives %h
    iexists xU, _
    iframe SU
    ipureintro; exact ⟨h, Or.inr rfl⟩

theorem errors.IsPathErrnoEof.wp_proof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG) := by
  intro err eof e he
  iintro #Hos #Heof #Hp
  ihave #Hsys : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave ⟨%xPe, %xEx, %xNE, %xUn, #Hv⟩ := errnoIsVars_of_init $$ Hsys
  ihave ⟨%x, %m, %hxm, #Hm⟩ := eofVar_es eof $$ Hio Heof
  obtain ⟨heof, hm⟩ := hxm
  ihave %hdist : ⌜x ≠ xPe ∧ x ≠ xEx ∧ x ≠ xNE ∧ x ≠ xUn⌝ $$ []
  · iunfold errnoIsVars at Hv
    icases Hv with ⟨-, -, -, -, #SPe, #SEx, #SNE, #SUn⟩
    rcases hm with rfl | rfl
    all_goals
      ihave %g1 := _root_.Perennial.errors.errorString_ne x xPe _ _ (by decide) $$ Hm SPe
      ihave %g2 := _root_.Perennial.errors.errorString_ne x xEx _ _ (by decide) $$ Hm SEx
      ihave %g3 := _root_.Perennial.errors.errorString_ne x xNE _ _ (by decide) $$ Hm SNE
      ihave %g4 := _root_.Perennial.errors.errorString_ne x xUn _ _ (by decide) $$ Hm SUn
      ipureintro; exact ⟨g1, g2, g3, g4⟩
  obtain ⟨h1, h2, h3, h4⟩ := hdist
  subst heof
  have hesInj : ∀ y z : Loc, esErr y = esErr z → y = z := by
    intro y z h
    unfold esErr interface.mkOk at h
    injection h with h
    injection h with _ h
    exact go.intoVal_inj h
  ihave %hex_pe : ⌜∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ $$ []
  · iunfold os.errnoPathErr at Hp
    icases Hp with ⟨%pe, %_, %_, %h, -⟩
    ipureintro; exact ⟨pe, h⟩
  obtain ⟨pe, hpe⟩ := hex_pe
  have ht : ErrnoIsTarget (esErr x) := errnoIsTarget_pointer _ ⟨_, x, rfl, rfl⟩
  ihave #Htree := (pathErrno_walkTree err e he (esErr x) ht xPe xEx xNE xUn (fun b => b = false)
    (fun b hb => hb.2 (fun h => h1 (hesInj _ _ h)) (fun h => h2 (hesInj _ _ h)) (fun h => h3 (hesInj _ _ h))
      (fun h => h4 (hesInj _ _ h)))) $$ [Hv Hp]
  · iframe #
  ihave #Htree' := _root_.Perennial.errors.errorIsTree_of_walk _ _ _ _ $$ Htree
  have htyped := peS_treeTyped pe e he (esErr x) (fun tii h => by cases h; exact ⟨_, rfl⟩)
  rw [← hpe] at htyped
  iintro !> %Φ - HΦ
  wp_apply +noauto _root_.Perennial.errors.wp_Is_tree (peS err e) _ err (esErr x)
    (fun tii h => by cases h; exact ⟨_, x, rfl, rfl⟩) htyped $$ [$Herr $Htree'] as %b ⟨-, -, %Hsome⟩
  · ipureintro; exact Or.inl rfl
  have hb : b = false := by
    cases b
    · rfl
    · exfalso
      have herrne : err ≠ interface.nil := by subst hpe; intro h; cases h
      obtain ⟨ii, hii, hm⟩ := Hsome _ rfl ⟨_, x, rfl, rfl⟩ herrne rfl
      rcases hm with hm | hm
      · rcases hii with hii | hii
        · rw [hii, hpe] at hm; exact pathError_ne_es pe x hm
        · rw [hii] at hm; exact errno_ne_es e he x hm
      · obtain ⟨hA, hB, hC⟩ := hm
        by_cases hx : interface.ok ii = err
        · exact absurd (hA hx) (by decide)
        · by_cases hy : interface.ok ii = errnoErr e
          · exact absurd (hB hy) (by decide)
          · exact absurd (hC hx hy) (by decide)
  subst hb
  iapply HΦ
  ipureintro; rfl

end proof

end EtcdGrove
end Perennial
