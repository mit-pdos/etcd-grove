/-
What a client of `net` needs of `errors.Is` on `net`'s errors (D14), from Perennial's spec
(`errors.Is.spec`, `Perennial/Spec/errors/Is.lean`) and `OpError.Unwrap`'s
(`Net/Spec/net/OpError__Unwrap.lean`): for a failure of kind `closed` or `timeout` (`opErr` with
`kindErr`), `errors.Is(err, ed)`, `ed` the value of `poll.ErrDeadlineExceeded` (which is
`os.ErrDeadlineExceeded`), is `true` exactly for the timeout (`errors_Is_deadline`).

Not covered, two gaps of Perennial (`notes/perennial-changes.md`, "net's errors and
`errors.Is`"): `errors.Is(err, net.ErrClosed)`, whose target `poll.ErrNetClosing` is a struct
value, not a pointer, which `errors.Is.spec` does not admit (`IsPointerError`); and a failure of
kind `sys`, whose `Err`, an `*os.SyscallError`, has an `Unwrap` method that no translation gives a
body (`os` is names-only there), so the walk is stuck at it. And the premise that `ed` is a
`*DeadlineExceededError` (`&DeadlineExceededError{}`, `internal/poll/fd.go`): `poll`'s package fact
says only that the variable holds some error.
-/
module

public import Net.Spec.net.OpError__Unwrap
public import Perennial.Spec.errors.Is

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net errors

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]
variable [errors_sem : errors.Assumptions]
variable [go.BasicIntoValInj]

/-- The `Is` and `Unwrap` methods of the errors the walk meets. -/
theorem opError_noIs :
    methodSet (go.GoType.PointerType OpError.ty) !! go!"Is" = none := by
  have h := go.MethodSetIs.method_set_is (t := go.GoType.PointerType OpError.ty) go!"Is"
  simpa [go.methodSetLookup] using h

theorem opError_unwrap :
    methodSet (go.GoType.PointerType OpError.ty) !! go!"Unwrap" =
      some (go.Signature [] false [go.error]) := by
  have h := go.MethodSetIs.method_set_is (t := go.GoType.PointerType OpError.ty) go!"Unwrap"
  simpa [go.methodSetLookup] using h

theorem errNetClosing_leaf (m : GoString) (hm : m = go!"Is" ∨ m = go!"Unwrap") :
    methodSet internal.poll.errNetClosing.ty !! m = none := by
  have h := go.MethodSetIs.method_set_is (t := internal.poll.errNetClosing.ty) m
  rcases hm with rfl | rfl <;> simpa [go.methodSetLookup] using h

theorem deadline_leaf (m : GoString) (hm : m = go!"Is" ∨ m = go!"Unwrap") :
    methodSet (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) !! m = none := by
  have h := go.MethodSetIs.method_set_is
    (t := go.GoType.PointerType internal.poll.DeadlineExceededError.ty) m
  rcases hm with rfl | rfl <;> simpa [go.methodSetLookup] using h

theorem errNetClosing_ty_ne_ptr' (t : go.GoType) :
    internal.poll.errNetClosing.ty ≠ go.GoType.PointerType t := by
  unfold internal.poll.errNetClosing.ty; intro h; cases h

theorem opError_ty_ne_deadline :
    go.GoType.PointerType OpError.ty ≠
      go.GoType.PointerType internal.poll.DeadlineExceededError.ty := by
  unfold OpError.ty internal.poll.DeadlineExceededError.ty; intro h; cases h

/-- D14. `errors.Is(err, ed)` for the error `err` of a failure of kind `closed` or `timeout`, `ed`
the value of `poll.ErrDeadlineExceeded` (`os.ErrDeadlineExceeded`): `true` exactly for a timeout.
(The file header says why not for `sys`, nor for the target `net.ErrClosed`.) -/
theorem errors_Is_deadline (Is_spec : errors.Is.spec (GF := GF) (hG := hG))
    (Unwrap_spec : OpError.Unwrap.spec (GF := GF) (hG := hG))
    (k : NetErr) (hk : k ≠ .sys) (op : GoString) (src addr e err ed : GoInterface)
    (nm : GoString → Prop) (ld : Loc)
    (hed : ed = interface.mkOk (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #ld) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.errors ∗ opErr (GF := GF) op src addr e err ∗
        kindErr (GF := GF) k (some ed) nm e }}
      (App (App (Val (@! errors.Is)) (Val #err)) (Val #ed))
    {{ (b : Bool), RET #b; ⌜b = decide (k = .timeout)⌝ }} := by
  subst hed
  cases k with
  | sys => exact absurd rfl hk
  | closed =>
    wp_start_folded as ⟨Ho, Hk⟩
    unfold kindErr
    icases Hk with %He
    unfold opErr
    icases Ho with ⟨%pe, %nw, %Herr, #Hpe⟩
    obtain ⟨Herr, -⟩ := Herr
    subst Herr
    let ed : GoInterface :=
      interface.mkOk (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #ld
    let fU : GoInterfaceOk → List GoError := fun ii =>
      if ii.ty = go.GoType.PointerType OpError.ty then [e] else []
    have hI : ∀ (ii : GoInterfaceOk) (b b' : Bool), b = false → b' = false → b = b' := by
      intro _ _ _ h h'; rw [h, h']
    have hU : ∀ (ii : GoInterfaceOk) (cs cs' : List GoError), cs = fU ii → cs' = fU ii → cs = cs' :=
      by intro _ _ _ h h'; rw [h, h']
    have hne : ∀ (t : go.GoType) (v : val), t ≠ go.GoType.PointerType internal.poll.DeadlineExceededError.ty →
        true = true → interface.ok ⟨t, v⟩ ≠ ed := by
      intro t v ht _ h
      exact ht (congrArg GoInterfaceOk.ty (GoInterface.ok.inj h))
    have hUop : fU ⟨go.GoType.PointerType OpError.ty, #pe⟩ = [e] := by simp [fU]
    have hptr : IsPointerError ⟨go.GoType.PointerType internal.poll.DeadlineExceededError.ty, #ld⟩ :=
      ⟨_, ld, rfl, rfl⟩
    subst He
    have hUe : fU ⟨internal.poll.errNetClosing.ty, #(zero_val internal.poll.errNetClosing)⟩ = [] := by
      simp [fU, errNetClosing_ty_ne_ptr']
    have htarg : ∀ tii, ed = interface.ok tii → IsPointerError tii :=
      fun tii h => by obtain rfl := (GoInterface.ok.inj h).symm; exact hptr
    have htyped : TreeTyped (fun x => x = interface.mkOk (go.GoType.PointerType OpError.ty) #pe ∨
        x = closedErr) ed := by
            rintro ii tii (h | h) htii hty
            · cases h; exact ⟨pe, rfl⟩
            · cases h
              obtain rfl := GoInterface.ok.inj htii
              exact absurd hty (errNetClosing_ty_ne_ptr' _)
    wp_apply Is_spec (fun x => x = interface.mkOk (go.GoType.PointerType OpError.ty) #pe ∨
        x = closedErr) (fun _ b => b = false) (fun ii cs => cs = fU ii)
        (interface.mkOk (go.GoType.PointerType OpError.ty) #pe) ed
        (_root_.Perennial.errors.comparableTarget_pointer _ _ htarg htyped) $$ []
      as %b ⟨-, %Hb⟩
    · iframe #
      isplitl
      · iintro !> %ii %hS
        unfold errorWalkNode
        rcases hS with h | h
        · cases h
          rw [opError_noIs, opError_unwrap]
          simp only [reduceCtorEq, ↓reduceIte]
          isplitr
          · itrivial
          iintro !> %Φ' - HΦ'
          wp_apply Unwrap_spec pe _ $$ Hpe
          iapply HΦ'
          ipureintro
          exact ⟨.inr rfl, hUop.symm⟩
        · cases h
          rw [errNetClosing_leaf _ (.inl rfl), errNetClosing_leaf _ (.inr rfl)]
          simp only [reduceCtorEq, ↓reduceIte]
          isplitr
          · itrivial
          · ipureintro; exact hUe.symm
      · ipureintro; left; rfl
    iapply HΦ
    ipureintro
    have hw := Hb (by intro h; cases h) (by intro h; simp only [ed] at h; cases h)
    have hw0 : IsWalk true (fun _ b => b = false) (fun ii cs => cs = fU ii) ed
        (interface.mkOk (go.GoType.PointerType OpError.ty) #pe) false :=
      .miss (hne _ _ opError_ty_ne_deadline) rfl hUop.symm
        (.miss (hne _ _ (errNetClosing_ty_ne_ptr' _)) rfl hUe.symm .done .done) .done
    rw [isWalk_det hI hU hw hw0]
    rfl
  | timeout =>
    wp_start_folded as ⟨Ho, Hk⟩
    unfold kindErr
    icases Hk with %He
    unfold opErr
    icases Ho with ⟨%pe, %nw, %Herr, #Hpe⟩
    obtain ⟨Herr, -⟩ := Herr
    subst Herr
    let ed : GoInterface :=
      interface.mkOk (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #ld
    let fU : GoInterfaceOk → List GoError := fun ii =>
      if ii.ty = go.GoType.PointerType OpError.ty then [e] else []
    have hI : ∀ (ii : GoInterfaceOk) (b b' : Bool), b = false → b' = false → b = b' := by
      intro _ _ _ h h'; rw [h, h']
    have hU : ∀ (ii : GoInterfaceOk) (cs cs' : List GoError), cs = fU ii → cs' = fU ii → cs = cs' :=
      by intro _ _ _ h h'; rw [h, h']
    have hne : ∀ (t : go.GoType) (v : val), t ≠ go.GoType.PointerType internal.poll.DeadlineExceededError.ty →
        true = true → interface.ok ⟨t, v⟩ ≠ ed := by
      intro t v ht _ h
      exact ht (congrArg GoInterfaceOk.ty (GoInterface.ok.inj h))
    have hUop : fU ⟨go.GoType.PointerType OpError.ty, #pe⟩ = [e] := by simp [fU]
    have hptr : IsPointerError ⟨go.GoType.PointerType internal.poll.DeadlineExceededError.ty, #ld⟩ :=
      ⟨_, ld, rfl, rfl⟩
    subst He
    have hUe : fU ⟨go.GoType.PointerType internal.poll.DeadlineExceededError.ty, #ld⟩ = [] := by
      simp [fU, Ne.symm opError_ty_ne_deadline]
    have htarg : ∀ tii, ed = interface.ok tii → IsPointerError tii :=
      fun tii h => by obtain rfl := (GoInterface.ok.inj h).symm; exact hptr
    have htyped : TreeTyped (fun x => x = interface.mkOk (go.GoType.PointerType OpError.ty) #pe ∨
        x = ed) ed := by
      rintro ii tii (h | h) htii hty
      · cases h; exact ⟨pe, rfl⟩
      · obtain rfl := GoInterface.ok.inj h; exact ⟨ld, rfl⟩
    wp_apply Is_spec (fun x => x = interface.mkOk (go.GoType.PointerType OpError.ty) #pe ∨
        x = ed) (fun _ b => b = false) (fun ii cs => cs = fU ii)
        (interface.mkOk (go.GoType.PointerType OpError.ty) #pe) ed
        (_root_.Perennial.errors.comparableTarget_pointer _ _ htarg htyped) $$ []
      as %b ⟨-, %Hb⟩
    · iframe #
      isplitl
      · iintro !> %ii %hS
        unfold errorWalkNode
        rcases hS with h | h
        · cases h
          rw [opError_noIs, opError_unwrap]
          simp only [reduceCtorEq, ↓reduceIte]
          isplitr
          · itrivial
          iintro !> %Φ' - HΦ'
          wp_apply Unwrap_spec pe _ $$ Hpe
          iapply HΦ'
          ipureintro
          exact ⟨.inr rfl, hUop.symm⟩
        · obtain rfl := GoInterface.ok.inj h
          rw [deadline_leaf _ (.inl rfl), deadline_leaf _ (.inr rfl)]
          simp only [reduceCtorEq, ↓reduceIte]
          isplitr
          · itrivial
          · ipureintro; exact hUe.symm
      · ipureintro; left; rfl
    iapply HΦ
    ipureintro
    have hw := Hb (by intro h; cases h) (by intro h; simp only [ed] at h; cases h)
    have hw0 : IsWalk true (fun _ b => b = false) (fun ii cs => cs = fU ii) ed
        (interface.mkOk (go.GoType.PointerType OpError.ty) #pe) true :=
      .hit (hne _ _ opError_ty_ne_deadline) rfl hUop.symm (.eq rfl rfl)
    rw [isWalk_det hI hU hw hw0]
    rfl

end proof

end net
end Perennial
