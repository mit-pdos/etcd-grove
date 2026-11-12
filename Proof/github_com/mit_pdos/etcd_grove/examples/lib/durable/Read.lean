/-
The proof of `Spec/github_com/mit_pdos/etcd_grove/examples/lib/durable/Read.lean`. Lean-first (no Rocq
counterpart): `Read` is the extension's `"Read"` (its trusted model), whose atomic spec is
`wp_DurableRead_atomic`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.lib.durable.Read

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.lib.durable.Assumptions]

theorem github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.wp_proof :
    github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.spec (GF := GF) (hG := hG) :=
  fun o name _ => by
  iintro %Φ HAU
  wp_func_call
  unfold github_com.mit_pdos.etcd_grove.examples.lib.durable.Read.impl
  wp_pures
  iapply wp_DurableRead_atomic o name $$ HAU

end proof

end Perennial
