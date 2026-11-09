/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.applyConfigUpdate(i, k)`, on a clone being
built: `ApplyConfigUpdate(i, k)`.
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

/-- `s.applyConfigUpdate(i, k)`, on a clone being built, of a server `i` with a `k`-th entry: the clone
holds `st.applyConfigUpdate i k` (server `i`'s configuration that entry's: the Go reads its value's
configuration fields, empty where it is not a configuration record, as the Lean's default). -/
abbrev State.applyConfigUpdate.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (i k : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗
      ⌜uint.nat i ∈ st.server ∧ 1 ≤ sint.Z k ∧ sint.Z k ≤ ((st.s (uint.nat i)).log.length : Int)⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"applyConfigUpdate")) (Val #i)) (Val #k))
  {{ RET #(); stateOwn p (st.applyConfigUpdate (uint.nat i) (sint.nat k)) (uint.nat i :: M) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
