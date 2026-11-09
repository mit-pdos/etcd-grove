/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.HasNoConflict(i, index, ents)`: `HasNoConflict(i, index, ents)`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Own

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

/-- `s.HasNoConflict(i, index, ents)`, of a server `i` of the state, an index at least 1 (an append
request's `prevLogIndex + 1`; at `index ≤ 0` the Go reads `log[index-1]`, out of range, where the Lean
reads `log[0]`), the index and the logs far from overflow: `hasNoConflict i index ents`. -/
abbrev State.HasNoConflict.spec : Prop :=
  ∀ (p : Loc) (st : State) (i index : w64) (el : GoSlice) (ents : List Entry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ logRO el ents ∗
      ⌜uint.nat i ∈ st.server ∧ 1 ≤ sint.Z index ∧ sint.Z index < 2 ^ 62 ∧
        (st.s (uint.nat i)).log.length < 2 ^ 62 ∧ ents.length < 2 ^ 62⌝ }}
    (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"HasNoConflict")) (Val #i)) (Val #index)) (Val #el))
  {{ RET #(st.hasNoConflict (uint.nat i) (sint.Z index) ents); True }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
