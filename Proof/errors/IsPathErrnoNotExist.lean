/- Lean-first (no Rocq counterpart).

`errors.IsPathErrnoNotExist.spec` (`Spec/errors/IsPathErrnoNotExist.lean`) proved
(2026-11-22): `os.ErrNotExist` holds internal/oserror's `ErrNotExist` (`os`'s package fact,
`os.errNotExist_oserror_of_pkgInit`), at which `Errno.Is` answers `e == ENOENT` (`ErrnoIsPost`); the walk of the
two-error tree (`pathErrno_walkTree`, exact relations) answers what the `Errno`'s `Is` does (`isWalk_det`).
-/
module

public import Spec.errors.IsPathErrnoNotExist
public import Proof.errors.PathErrnoTree
public import Perennial.Proof.errors.Link

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

theorem errors.IsPathErrnoNotExist.wp_proof : errors.IsPathErrnoNotExist.spec (GF := GF) (hG := hG) := by
  intro err e he
  iintro #Hos #Hp
  ihave #Hsys : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Herr : isPkgInit (PROP := IProp GF) pkg_id.errors $$ []
  · iPkgInit
  ihave ⟨%xPe, %xEx, %xNE, %xUn, #Hv⟩ := errnoIsVars_of_init $$ Hsys
  ihave ⟨%x, #Hx, #Hxo⟩ := os.errNotExist_oserror_of_pkgInit $$ Hos
  ihave %hx : ⌜x = xNE⌝ $$ []
  · iunfold errnoIsVars at Hv
    icases Hv with ⟨-, -, #ONE, -⟩
    icombine Hxo ONE gives %h
    ipureintro
    unfold esErr interface.mkOk at h
    injection h with h
    injection h with _ h
    exact go.intoVal_inj h
  subst hx
  ihave %hex_pe : ⌜∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe⌝ $$ []
  · iunfold os.errnoPathErr at Hp
    icases Hp with ⟨%pe, %_, %_, %h, -⟩
    ipureintro; exact ⟨pe, h⟩
  obtain ⟨pe, hpe⟩ := hex_pe
  have hen : errnoErr e = interface.mkOk syscall.Errno.ty #e := by
    unfold errnoErr; simp only [he, ↓reduceIte]
  have ht : ErrnoIsTarget (esErr x) := errnoIsTarget_pointer _ ⟨_, x, rfl, rfl⟩
  let Ie : Bool → Prop := fun b => b = decide (e = W64 2)
  ihave #Htree := (pathErrno_walkTree err e he (esErr x) ht xPe xEx x xUn Ie (fun b hb => hb.1 rfl)) $$ [Hv Hp]
  · iframe #
  have htyped := peS_treeTyped pe e he (esErr x) (fun tii h => by cases h; exact ⟨_, rfl⟩)
  rw [← hpe] at htyped
  have hc := _root_.Perennial.errors.comparableTarget_pointer (GF := GF) (hG := hG) (peS err e) (esErr x)
    (fun tii h => by cases h; exact ⟨_, x, rfl, rfl⟩) htyped
  unfold errIsNotExist
  iintro !> %t %Φ #Ht HΦ
  ihave %htx : ⌜t = esErr x⌝ $$ []
  · icombine Ht Hx gives %h
    ipureintro; exact h
  subst htx
  wp_apply +noauto _root_.Perennial.errors.wp_Is (peS err e) (peI err e Ie) (peU err e) err (esErr x) hc
    $$ [$Herr $Htree] as %b ⟨-, %Hw⟩
  · ipureintro; exact Or.inl rfl
  have herrne : err ≠ interface.nil := by subst hpe; intro h; cases h
  have hW := Hw herrne (by intro h; cases h)
  -- the walk this tree has, answering `e == ENOENT`
  have hne1 : err ≠ errnoErr e := by
    rw [hpe, hen]; unfold interface.mkOk; intro h
    injection h with h
    injection h with h
    exact errno_ne_ptr _ h.symm
  obtain ⟨peii, hpeii⟩ : ∃ ii, err = interface.ok ii := ⟨_, hpe⟩
  obtain ⟨eii, heii⟩ : ∃ ii, errnoErr e = interface.ok ii := ⟨_, hen⟩
  have hU1 : peU err e peii [errnoErr e] := ⟨fun _ => rfl, fun h => absurd hpeii.symm h⟩
  have hU2 : peU err e eii [] := ⟨fun h => absurd (heii.trans h).symm hne1, fun _ => rfl⟩
  have hI1 : peI err e Ie peii false :=
    ⟨fun _ => rfl, fun h => absurd (hpeii.trans h) hne1, fun h => absurd hpeii.symm h⟩
  have hI2 : ∀ d, d = decide (e = W64 2) → peI err e Ie eii d := fun d hd =>
    ⟨fun h => absurd (heii.trans h).symm hne1, fun _ => hd, fun _ h => absurd heii.symm h⟩
  have hn1 : interface.ok peii ≠ esErr x := by rw [← hpeii, hpe]; exact pathError_ne_es pe x
  have hn2 : interface.ok eii ≠ esErr x := by rw [← heii]; exact errno_ne_es e he x
  have hL : _root_.Perennial.errors.IsWalkL true (peI err e Ie) (peU err e) (esErr x) [interface.ok eii]
      (decide (e = W64 2)) := by
    cases hd : decide (e = W64 2)
    · exact .miss (fun _ => hn2) (hI2 false hd.symm) hU2 .done .done
    · exact .is (fun _ => hn2) (hI2 true hd.symm)
  have hL' : _root_.Perennial.errors.IsWalkL true (peI err e Ie) (peU err e) (esErr x) [errnoErr e]
      (decide (e = W64 2)) := by
    have hl : [errnoErr e] = [interface.ok eii] := by rw [heii]
    rw [hl]; exact hL
  have hW0' := _root_.Perennial.errors.IsWalk.children (fun _ => hn1) hI1 hU1 hL'
  have hW0 : _root_.Perennial.errors.IsWalk true (peI err e Ie) (peU err e) (esErr x) err
      (decide (e = W64 2)) := by
    have hl : [err] = [interface.ok peii] := by rw [hpeii]
    show _root_.Perennial.errors.IsWalkL _ _ _ _ [err] _
    rw [hl]; exact hW0'
  have hdet := _root_.Perennial.errors.isWalk_det (c := true) (I := peI err e Ie) (U := peU err e)
    (target := esErr x)
    (fun ii b b' h h' => by
      by_cases hx : interface.ok ii = err
      · rw [h.1 hx, h'.1 hx]
      · by_cases hy : interface.ok ii = errnoErr e
        · exact (h.2.1 hy).trans (h'.2.1 hy).symm
        · rw [h.2.2 hx hy, h'.2.2 hx hy])
    (fun ii cs cs' h h' => by
      by_cases hx : interface.ok ii = err
      · rw [h.1 hx, h'.1 hx]
      · rw [h.2 hx, h'.2 hx])
    hW hW0
  rw [hdet]
  have h2 : (W64 2) = Fs.ENOENT := rfl
  rw [h2]
  iapply HΦ

end proof

end EtcdGrove
end Perennial
