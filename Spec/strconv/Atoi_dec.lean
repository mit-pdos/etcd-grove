/-
`strconv.Atoi`'s spec on a decimal it wrote (`strconv.Itoa`'s output): the number back, no error. A
parser of `Itoa`'s output needs it (the hraft kit's `service.Store.Restore`, notes/dsv-hraft.md, S5).
Proved (`Proof/strconv/Atoi_dec.lean`) from Perennial's functional `strconv.Atoi.spec` (its result is
`parseInt s 10 0`'s) and the round trip `internal.strconv.parseInt_fmtInt10_0`.
-/
module

public import Perennial.Proof.strconv.Base
public import Perennial.Proof.internal.strconv.FormatBasics

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : strconv.Assumptions]

/-- `strconv.Atoi(Itoa(n))` of an `n ≥ 0` returns `n` and a nil error. -/
abbrev strconv.Atoi_dec.spec : Prop :=
  ∀ (n : w64), 0 ≤ sint.Z n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.strconv }}
      (App (Val (@! strconv.Atoi)) (Val #(internal.strconv.fmtInt n (W64 10))))
    {{ RET (PairV #n #interface.nil); True }}

end spec

end Perennial
