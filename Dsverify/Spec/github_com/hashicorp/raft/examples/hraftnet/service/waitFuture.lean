/-
`service.waitFuture`'s spec (the hraft kit's state machine, notes/dsv-hraft.md, S5).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.service.FsmDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.service.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.service github_com.hashicorp.raft
  github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

/-- `waitFuture(f, d)`: `f.Error()` (on a goroutine of its own) and `true` if it answers within `d`;
`false` (and nothing) else. The answer `Q` is the caller's: `f.Error()`'s spec, from `P`. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.service.waitFuture.spec : Prop :=
  ∀ (x : GoInterfaceOk) (P : IProp GF) (Q : GoInterface → IProp GF) (d : time.Duration),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ P }}
      (App (Val #(methods x.ty go!"Error" x.v)) (Val #()))
    {{ (err : GoInterface), RET #err; Q err }} →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.service ∗ P }}
    (App (App (Val (@! github_com.hashicorp.raft.examples.hraftnet.service.waitFuture))
      (Val #(GoInterface.ok x))) (Val #d))
  {{ (err : GoInterface) (ok : Bool), RET (PairV #err #ok); ⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ Q err) }}

end spec

end Perennial
