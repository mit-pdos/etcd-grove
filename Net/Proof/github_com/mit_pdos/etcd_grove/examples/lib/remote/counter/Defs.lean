/-
# remote's counter instance: the far side's store (`notes/remote-port-plan.md`, R4)

The counter on the server node (`lintest/counter`'s `Counter`, logically atomic over
`counterState γ n`, a ghost variable's half: `Counter.Apply.spec`), as `remote`'s far-side store
(`RBase`, `remote/Defs.lean`):

- `cB`: the base store, an `int64` counter; an input is a `bool` (`true`: increment, a write;
  `false`: read); the output is the counter's value after the step.
- `cR γ`: its state is `counterState γ` (timeless), the operation's mask `∅` (`Counter.Apply`'s),
  the inputs boxed `bool`s (`boxB`), the outputs boxed `Out{false, n}` (`outV`), the unknown output
  `Out{true, 0}`; the bytes are `Codec()`'s: an input one byte, an output a byte (unknown or not)
  and the value's 8 little-endian bytes (`encOutV`).
- `cDec`: porcupine's operations as the model's: a boxed `bool` and a boxed `Out`, unknown or not.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.counter.Base
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.lib.remote.Pend

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

section base
variable [GooseExts] [GoGlobalContext] {GF : BundledGFunctors} [AllG GF]

/-- **The far side's store** (see the file header), over the counter's ghost variable `γ`. -/
def cR (γ : GName) : RBase GF w64 Bool w64 where
  B := cB
  sysState n := ghostVar γ (1 : Qp).half n
  Eop := ∅
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

end github_com.mit_pdos.etcd_grove.examples.lib.remote.counter
end Perennial
