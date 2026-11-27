/-
**Trust-boundary axiom** (dsv-fix4, mit-pdos/etcd-grove#49 fix 4): `fmt.Println(a...)` of operands `printOk` allows (`nil` or a well-formed basic value,
`fmt.ArgWf`; or an error whose `Error()` returns, `models_lab.errAny`, that is not a
`fmt.Formatter`) returns, giving the slice back (the spec `raxos.hyp.fmt.Println.spec`,
`Dsverify/Proof/raxos/Hyp.lean`). Perennial leaves `fmt.Println` untranslated
(`Perennial/Code/fmt.toml`). Go's `print.go`: `Println` is `Fprintln(os.Stdout, a...)`, which
formats each operand with `%v` (`printArg`: a basic value by its kind, no method; an error's
`Error()` after checking `Formatter`) and writes the result once to `os.Stdout`, returning the write
error, never panicking on it. The premise `raxos.hyp.PrintlnHyp` of QuePaxa's statement until
dsv-fix4, its field verbatim. **Condition** (the review's): `os.Stdout` holds the runtime's valid
`*os.File` (Go panics after `os.Stdout = &os.File{}`); Perennial's model leaves `os.Stdout`
unallocated, so no proof here can write it: when Perennial models it as a writable variable, this
axiom needs that premise. Review: `notes/axiom-review/dsv-fix4/quepaxa-misc.md`.
-/
module

public import Dsverify.Proof.raxos.Hyp

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section ax
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]

/-- **Trust-boundary axiom** (the file header). -/
axiom raxos.hyp.fmt.Println.wp_proof : raxos.hyp.fmt.Println.spec (GF := GF) (hG := hG)

end ax

end Perennial
