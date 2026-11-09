/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `State.MoreUpToDateCorrectInv()`:
`MoreUpToDateCorrectInv` (`State.moreUpToDateCorrectInv`) where it is defined.
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

/-- `s.MoreUpToDateCorrectInv()`: whether every server's log at least as up to date as another's
extends the other's committed entries, where `MoreUpToDateCorrectInv` is defined (where it is not,
a `Committed(j)` past `j`'s log, TLC fails and the Go panics with an `EvalError`, which a triple
cannot state: `Committed`'s premise). (The invariant is false of raft and not checked:
`issues/raft-tla-more-up-to-date-cut-batches.md`.) -/
abbrev State.MoreUpToDateCorrectInv.spec : Prop :=
  ∀ (p : Loc) (st : State) (b : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜st.moreUpToDateCorrectInv = .ok b⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"MoreUpToDateCorrectInv")) (Val #()))
  {{ RET #b; True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
