/-
A nonzero errno's error is one Go's `fmt` formats by its `Error()` (`fmtErrorOk`,
`Spec/fmt/ErrorOk.lean`), with a message of at most `syscall.errnoMsgMax` bytes (`fmtErrorOkLe`):
`syscall.Errno`'s method set has `Error() string` and no `Format` (goose's
`Errno.TypeAssumptions`), and its `Error()` (translated with its body since 2026-11-24, fmt stage 1:
`syscall_unix.go`) returns the entry of the error table `errors` when there is a nonempty one, else
`"errno " + strconv.Itoa(int(e))`. It reads the table, so it needs `syscall`'s package fact
(`errorsOk`, `PkgInit.lean`: every entry at most `errnoMsgMax` bytes) and `internal/strconv`'s
(`Itoa`): `syscall.errnoOk`. Used by the specs of
`syscall`'s, `golang.org/x/sys/unix`'s and `os`'s models, whose errors are `errnoErr e` (or a
`*PathError` wrapping one, `Proof/os/ErrorOk.lean`).
-/
module

public import Proof.syscall.Base
public import Proof.syscall.PkgInit
public import Perennial.Proof.internal.strconv.Link
public import Spec.fmt.ErrorOk

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : syscall.Assumptions]

/-- The message `"errno " + Itoa(int(e))` has at most 27 bytes. -/
theorem errno_itoa_length_le (e : w64) :
    (go!"errno " ++ internal.strconv.fmtInt e (W64 10) : GoString).length ≤ syscall.errnoMsgMax := by
  have h := internal.strconv.fmtUint10_length_le e
  have h' := internal.strconv.fmtUint10_length_le (-e)
  unfold internal.strconv.fmtInt syscall.errnoMsgMax
  rw [List.length_append]
  split <;> simp_all <;> omega

/-- **`Errno(e).Error()`** returns at most `errnoMsgMax` bytes: a nonempty entry of `errors`, else
`"errno " + Itoa(int(e))`. -/
theorem errno_stringMethodSpecLe (e : w64) :
    syscall.errnoOk (GF := GF) ⊢
      EtcdGrove.stringMethodSpecLe (GF := GF) ⟨syscall.Errno.ty, #e⟩ go!"Error"
        syscall.errnoMsgMax := by
  unfold syscall.errnoOk
  iintro ⟨#Htab, #Hstr⟩
  unfold EtcdGrove.stringMethodSpecLe
  imodintro
  iintro %Φ HΦ
  simp only [method_unfold]
  unfold syscall.Errno.Error.impl
  wp_auto
  wp_if_destruct
  · wp_if_destruct
    · have h0 : 0 ≤ sint.Z e := by simpa using ‹sint.Z (W64 0) ≤ sint.Z e›
      have h1 : sint.Z e < 133 := by
        rw [show sint.Z (W64 133) = 133 from rfl] at Hif; exact Hif
      unfold syscall.errorsOk
      icases Htab with ⟨%tbl, #Htbl, %Hle⟩
      obtain ⟨arr⟩ := tbl
      icases array_len _ _ _ _ $$ Htbl with %Hlen
      obtain ⟨v, hv⟩ : ∃ v, arr[(sint.Z e).toNat]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩)]
      icases array_acc (V := GoString) _ (sint.Z e) _ _ ⟨arr⟩ v (by omega) hv $$ Htbl with ⟨Hv, -⟩
      wp_auto
      have hvle : v.length ≤ syscall.errnoMsgMax := Hle v (List.mem_of_getElem? hv)
      wp_if_destruct
      · wp_apply internal.strconv.wp_Itoa
        iapply HΦ
        ipureintro; exact errno_itoa_length_le _
      · iapply HΦ
        ipureintro; exact hvle
    · wp_apply internal.strconv.wp_Itoa
      iapply HΦ
      ipureintro; exact errno_itoa_length_le _
  · wp_apply internal.strconv.wp_Itoa
    iapply HΦ
    ipureintro; exact errno_itoa_length_le _

/-- **A nonzero errno's error is `fmtErrorOkLe errnoMsgMax`.** -/
theorem errnoErr_fmtErrorOkLe (e : w64) (he : e ≠ 0) :
    syscall.errnoOk (GF := GF) ⊢
      EtcdGrove.fmtErrorOkLe (GF := GF) syscall.errnoMsgMax (errnoErr e) := by
  iintro #Hpkg
  unfold errnoErr
  simp only [he, ↓reduceIte, interface.mkOk, EtcdGrove.fmtErrorOkLe]
  isplitr
  · ipureintro
    have h1 := (go.MethodSetIs.method_set_is (t := syscall.Errno.ty) go!"Format")
    have h2 := (go.MethodSetIs.method_set_is (t := syscall.Errno.ty) go!"Error")
    simp only [go.methodSetLookup] at h1 h2
    exact ⟨by simpa using h1, by simpa [EtcdGrove.noArgStringSig] using h2⟩
  · iapply errno_stringMethodSpecLe $$ Hpkg

/-- **A nonzero errno's error is `fmtErrorOk`.** -/
theorem errnoErr_fmtErrorOk (e : w64) (he : e ≠ 0) :
    syscall.errnoOk (GF := GF) ⊢ EtcdGrove.fmtErrorOk (GF := GF) (errnoErr e) := by
  iintro #Hpkg
  iapply EtcdGrove.fmtErrorOk_of_le
  iapply errnoErr_fmtErrorOkLe e he $$ Hpkg

end wps

end Perennial
