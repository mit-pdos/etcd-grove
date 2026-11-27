/- Lean-first (no Rocq counterpart).

# `net/rpcdriver`: what a machine's boot returns

`bootRes`: net/http's and net/rpc's first-run state and the driver's variables, which
`boot_rpcdriver` (`BootLinked.lean`) returns and each command's `main` takes.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver.Defs
public import Net.Proof.net.rpc.InitFirst
public import Net.Proof.net.http.MuxDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- A machine's boot resources: net/http's and net/rpc's first-run state (net/http's: the right to
register on `DefaultServeMux` and its server's variables), and the driver's variables. -/
def bootRes : IProp GF :=
  iprop(net.http.muxOwn (GF := GF) (hG := hG) (globalAddr net.http.defaultServeMux) [] ∗ net.http.httpSrvEnv (GF := GF) ∗
    net.rpc.rpcFirstRes (GF := GF) ∗ drvFacts)

end boot

end Perennial.github_com.mit_pdos.etcd_grove.examples.net.rpcdriver
