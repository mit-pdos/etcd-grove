/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: what a machine's boot returns

`bootRes`: what net/http's first initialization leaves that the server reads (Go 1.22's matcher,
`use121 ↦□ false`, under the environment premise `GodebugHttpmuxgo121Not1`; `maxSlice`'s value; the
server's variables, `httpSrvEnv`), and the driver's variable (`drvFacts`), which `boot_httpdriver`
(`BootLinked.lean`) returns and each command's `main` takes.
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.Defs
public import Net.Proof.net.http.MuxDefs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial.github_com.mit_pdos.etcd_grove.examples.net.httpdriver

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section boot
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : Assumptions] [net.FieldAssumptions]

/-- A machine's boot resources (see the file header). -/
def bootRes : IProp GF :=
  iprop(globalAddr net.http.use121 ↦□ false ∗ (∃ ms : w64, globalAddr net.http.maxSlice ↦□ ms) ∗
    net.http.httpSrvEnv (GF := GF) ∗ drvFacts)

instance bootRes_persistent : Persistent (bootRes (GF := GF)) := by
  unfold bootRes; infer_instance

end boot

end Perennial.github_com.mit_pdos.etcd_grove.examples.net.httpdriver
