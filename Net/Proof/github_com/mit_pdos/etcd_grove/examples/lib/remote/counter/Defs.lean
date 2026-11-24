/-
# remote's counter instance: the far side's store (`notes/remote-port-plan.md`, R4)

The counter on the server node (`lintest/counter`'s `Counter`, logically atomic over
`counterState γ n`, a ghost variable's half: `Counter.Apply.spec`), as `remote`'s far-side store
(`RBase`, `remote/Defs.lean`):

- `cB`: the base store, an `int64` counter; an input is a `bool` (`true`: increment, a write;
  `false`: read); the output is the counter's value after the step.
- `cR γ`: its state is half of a ghost variable `γ` allocated at the deployment's start (timeless),
  which the server keeps in step with its `Counter`'s state (`counterState`, allocated by `New` at
  run time) in an invariant at `syncN`, the operation's mask (`Server.lean`),
  the inputs boxed `bool`s (`boxB`), the outputs boxed `Out{false, n}` (`outV`), the unknown output
  `Out{true, 0}`; the bytes are `Codec()`'s: an input one byte, an output a byte (unknown or not)
  and the value's 8 little-endian bytes (`encOutV`).
- `cDec`: porcupine's operations as the model's: a boxed `bool` and a boxed `Out`, unknown or not.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend
public import Perennial.Proof.encoding.binary.Base

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory

namespace github_com.mit_pdos.etcd_grove.examples.lib.remote.counter

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote

/-- The counter's base store: `true` increments (a write), `false` reads; the output is the
counter's value after the step. -/
def cB : linkv.PendSpec w64 Bool w64 where
  init := W64 0
  step b n := if b then (n + W64 1, n + W64 1) else (n, n)
  isWrite b := b

section vals
variable [GooseExts] [GoGlobalContext]

/-- An input, boxed (`any` holding a `bool`). -/
abbrev boxB (b : Bool) : GoInterface := interface.mkOk go.bool #b

/-- An output, boxed (`any` holding an `Out`). -/
abbrev outV (u : Bool) (n : w64) : GoInterface := interface.mkOk Out.ty #(Out.mk u n)

/-- `Codec()`'s bytes of an output `Out{u, n}`. -/
def encOutB (u : Bool) (n : w64) : List w8 := (if u then W8 1 else W8 0) :: u64Le n

open Classical in
/-- `Codec()`'s bytes of a value: an `Out`'s, or nothing for any other value (never encoded). -/
def encOutV (v : GoInterface) : List w8 :=
  if h : ∃ p : Bool × w64, v = outV p.1 p.2 then encOutB (choose h).1 (choose h).2 else []

open Classical in
/-- porcupine's operations as the model's: a boxed `bool` and a boxed `Out`, unknown (`err`) or
not (`ok n`); anything else decodes to nothing. -/
def cDec (io : OpV) : Option (Bool × linkv.Ans w64) :=
  if h : ∃ (b u : Bool) (n : w64), io = (boxB b, outV u n) then
    let b := choose h
    let u := choose (choose_spec h)
    let n := choose (choose_spec (choose_spec h))
    some (b, if u then .err else .ok n)
  else none

end vals

/-- The server's invariant tying the start's ghost variable to its counter's. -/
def syncN : Namespace := nroot.@"remote_counter_sync"

section base
variable [GooseExts] [GoGlobalContext] {GF : BundledGFunctors} [AllG GF]

/-- **The far side's store** (see the file header), over the counter's ghost variable `γ`. -/
def cR (γ : GName) : RBase GF w64 Bool w64 where
  B := cB
  sysState n := ghostVar γ (1 : Qp).half n
  Eop := ↑syncN
  iv := boxB
  ov n := outV false n
  unk _ := outV true (W64 0)
  encIn b := [if b then W8 1 else W8 0]
  encOut := encOutV
  reads_stay i st h := by cases i <;> simp_all [cB]
  encIn_len _ := by simp
  encOut_len v := by
    unfold encOutV; split <;> simp [encOutB, u64Le_length]

instance cR_timeless (γ : GName) (n : w64) : Timeless ((cR (GF := GF) γ).sysState n) := by
  unfold cR; simp only; infer_instance

end base

section inj
variable [GooseExts] [go_gctx : GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Assumptions]

/-- An `Out` value determines its fields (its fields' loads are deterministic). -/
instance out_intoValInj : go.IntoValInj Out where
  intoVal_inj x y h := by
    have hu : ∀ z : Out, is_go_step_pure (StructFieldGet Out.underlying go!"Unknown")
        #z = Eq (Val #(z.Unknown')) := fun z =>
      (Out.TypeAssumptions.get'Unknown z).isGoStep_det_internal.isGoStep_pure_det
    have hn : ∀ z : Out, is_go_step_pure (StructFieldGet Out.underlying go!"N")
        #z = Eq (Val #(z.N')) := fun z =>
      (Out.TypeAssumptions.get'N z).isGoStep_det_internal.isGoStep_pure_det
    have e1 := hu x
    rw [h, hu y] at e1
    have e2 := hn x
    rw [h, hn y] at e2
    have f1 : Val #(x.Unknown') = Val #(y.Unknown') := by
      have := congrFun e1 (Val #(x.Unknown')); simp only [eq_iff_iff, iff_true] at this
      exact this.symm
    have f2 : Val #(x.N') = Val #(y.N') := by
      have := congrFun e2 (Val #(x.N')); simp only [eq_iff_iff, iff_true] at this; exact this.symm
    injection f1 with f1
    injection f2 with f2
    cases x; cases y
    simp only [Out.mk.injEq]
    exact ⟨GoGlobalContext.intoVal_inj_bool f1, GoGlobalContext.intoVal_inj_w64 f2⟩

theorem codec_outV_inj {u u' : Bool} {n n' : w64} (h : outV u n = outV u' n') : u = u' ∧ n = n' := by
  simp only [outV, interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq, true_and] at h
  have h' := go.intoVal_inj h
  simp only [Out.mk.injEq] at h'
  exact h'

/-- `Out{u, n}`'s bytes. -/
theorem encOutV_outV (u : Bool) (n : w64) : encOutV (outV u n) = encOutB u n := by
  unfold encOutV
  split
  · rename_i h
    obtain ⟨h1, h2⟩ := codec_outV_inj h.choose_spec
    rw [← h1, ← h2]
  · rename_i h
    exact absurd ⟨(u, n), rfl⟩ h

/-- Distinct outputs have distinct bytes (`Run`'s premise: node 0 tells a read's answer by its
bytes). -/
theorem cR_encOut_inj (γ : GName) {GF : BundledGFunctors} [AllG GF] (o o' : w64)
    (h : (cR (GF := GF) γ).encOut ((cR (GF := GF) γ).ov o) =
      (cR (GF := GF) γ).encOut ((cR (GF := GF) γ).ov o')) : o = o' := by
  simp only [cR, encOutV_outV, encOutB] at h
  exact u64Le_inj (List.cons.inj h).2

end inj

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
