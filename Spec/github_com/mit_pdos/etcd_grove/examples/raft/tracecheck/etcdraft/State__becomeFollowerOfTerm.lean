/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.becomeFollowerOfTerm(i, t)`: `BecomeFollowerOfTerm(i, t)`, on a clone being built.
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

/-- `s.becomeFollowerOfTerm(i, term)` on a clone being built, of a server of the state:
`becomeFollowerOfTerm i term`; server `i` is then a copy being written. -/
abbrev State.becomeFollowerOfTerm.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (i term : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"becomeFollowerOfTerm")) (Val #i)) (Val #term))
  {{ RET #(); stateOwn p (st.becomeFollowerOfTerm (uint.nat i) (sint.Z term)) (uint.nat i :: M) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
