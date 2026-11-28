/-
`rserver.rnd`'s spec (hraft_robust; the copy in `rserver/helpers.go` of hraftnet's `rnd`): hraftnet's
`rnd.spec`, at rserver's package.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ServerDefs
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

open github_com.hashicorp.raft github_com.hashicorp.raft.examples.hraftnet

/-- `rnd(n)`, `n > 0`: a number below `n` (any). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.rserver.rnd.spec : Prop :=
  ∀ (n : w64), 0 < uint.Z n →
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.rserver }}
      (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.rserver.rnd)) (Val #n))
    {{ (r : w64), RET #r; ⌜uint.Z r < uint.Z n⌝ }}

end spec

end Perennial
