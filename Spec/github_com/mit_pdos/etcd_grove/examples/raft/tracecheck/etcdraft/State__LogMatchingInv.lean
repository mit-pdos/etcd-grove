/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `State.LogMatchingInv()`:
`LogMatchingInv` (`State.logMatchingInv`).
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

/-- `s.LogMatchingInv()`: whether any two servers' logs agree up to every index where their
entries' terms agree. The logs shorter than `2^63 - 1` (the Go's index runs to the shorter log's
length plus one in `int`). -/
abbrev State.LogMatchingInv.spec : Prop :=
  ∀ (p : Loc) (st : State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜∀ i ∈ st.server, ((st.s i).log.length : Int) < 2 ^ 63 - 1⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"LogMatchingInv")) (Val #()))
  {{ RET #(st.logMatchingInv); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
