/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `State.LogInv()`: `LogInv`
(`State.logInv`) where it is defined.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Etcdraft

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Assumptions]

/-- `s.LogInv()`: whether any two servers' committed entries are one a prefix of the other, where
`LogInv` is defined (where it is not, a `Committed(i)` past `i`'s log, TLC fails and the Go panics
with an `EvalError`, which a triple cannot state: `Committed`'s premise). -/
abbrev State.LogInv.spec : Prop :=
  ∀ (p : Loc) (st : State) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜st.logInv = .ok b⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"LogInv")) (Val #()))
  {{ RET #b; True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
