/-
`hraftnet.ServerAddrs`'s spec (the hraft kit's generated addresses, notes/dsv-hraft.md, S5d).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Addrs
public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet

/-- `ServerAddrs()`: a new slice of `serverAddrs`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.ServerAddrs.spec : Prop :=
  {{ (True : IProp GF) }}
    (App (Val (@! ServerAddrs)) (Val #()))
  {{ (sl : GoSlice), RET #sl; ∃ L, sl ↦* L ∗ ⌜L = serverAddrs⌝ }}

end spec

end Perennial
