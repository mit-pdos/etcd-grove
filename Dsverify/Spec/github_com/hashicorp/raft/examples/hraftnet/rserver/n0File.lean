/-
`rserver.n0File`'s spec (hraft_robust; `rserver.go`): the first-start marker's path in `dir`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rserver.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.rserver.Assumptions]

/-- `n0File(dir)`: `dir + "/n0"`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rserver.n0File.spec : Prop :=
  ∀ (dir : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver }}
      (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.rserver.n0File)) (Val #dir))
    {{ RET #(dir ++ go!"/n0"); True }}

end spec

end Perennial
