/-
`github.com/mit-pdos/gokv/trusted_proph.ResolveBytes`'s spec. Lean-first (no Rocq counterpart).
A trusted function (`Code/github_com/mit_pdos/gokv/trusted_proph.toml`): its model is Perennial's
(`Perennial/TrustedCode/github_com/mit_pdos/gokv/trusted_proph.lean`), which converts the slice to
a string and resolves the prophecy with it.
-/
module

public import GeneratedProof.github_com.mit_pdos.gokv.trusted_proph
public import Perennial.Proof.github_com.goose_lang.primitive.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.gokv.trusted_proph.Assumptions]

/-- `ResolveBytes(p, b)`: resolves the prophecy `p` with the string of `b`'s bytes `s`, the head
of the values it was prophesied to be resolved with; `b` is only read. -/
abbrev github_com.mit_pdos.gokv.trusted_proph.ResolveBytes.spec : Prop :=
  ∀ (p : github_com.goose_lang.primitive.ProphId) (pvs : List val) (sl : GoSlice) (s : GoString) (dq : DFrac),
    {{ (proph p pvs : IProp GF) ∗ sl ↦*{dq} s }}
      (App (App (Val (@! github_com.mit_pdos.gokv.trusted_proph.ResolveBytes)) (Val #p))
        (Val #sl))
    {{ (pvs' : List val), RET #(); ⌜pvs = #s :: pvs'⌝ ∗ proph p pvs' ∗ sl ↦*{dq} s }}

end spec

end Perennial
