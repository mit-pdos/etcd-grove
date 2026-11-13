/-
`wire.Forever()`: `select {}`, which blocks forever: it never returns (postcondition `False`).
Proved in `NetTcp/Proof/github_com/mit_pdos/etcd_grove/examples/net/wire/Forever.lean`.
-/
module

public import NetTcp.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.mit_pdos.etcd_grove.examples.net.wire

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Tcp.tcpExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : wire.Assumptions]

/-- See the file header. -/
abbrev Forever.spec : Prop :=
  {{ (True : IProp GF) }} (App (Val (@! wire.Forever)) (Val #())) {{ RET #(); False }}

end spec

end github_com.mit_pdos.etcd_grove.examples.net.wire
end Perennial
