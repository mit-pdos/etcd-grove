/-
`hraftnet.command`'s spec (the hraft kit, notes/dsv-hraft.md, S5f).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.ClientDefs

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

/-- `command(c, seq, x)`: a fresh slice of the log command of client `c`'s operation `seq` on `x`
(`cmdB`: the kind, `opID`'s bytes, a put's value). -/
abbrev github_com.hashicorp.raft.examples.hraftnet.command.spec : Prop :=
  ∀ (c s : w64) (put : Bool) (way : w64) (v : GoString),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet }}
      (App (App (App (Val (@! command)) (Val #c)) (Val #s)) (Val #(In.mk put way v)))
    {{ (sl : GoSlice), RET #sl; sl ↦* cmdB c s put v }}

end spec

end Perennial
