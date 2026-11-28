/-
`strconv.Atoi`'s spec on a decimal it wrote (`strconv.Itoa`'s output): the number back, no error.
Perennial's `strconv.Atoi.spec` does not say which number (it gives the errors only), which a parser
of `Itoa`'s output needs (the hraft kit's `service.Store.Restore`, notes/dsv-hraft.md, S5). The
statement is true of Go's `Atoi`: Perennial has the round trip for its slow path
(`internal.strconv.parseInt_fmtInt10`, through `ParseInt`); its fast path (1 to 18 bytes) is a loop
of digits. **Not yet proved**: a hypothesis of the proofs that take it (notes/perennial-changes.md:
a functional `Atoi` spec, proposed to Perennial).
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
