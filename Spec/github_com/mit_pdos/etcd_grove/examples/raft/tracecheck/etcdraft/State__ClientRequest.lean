/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.ClientRequest(i, v)`: the action `ClientRequest(i, v)`.
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

/-- `s.ClientRequest(i, val)`, of a server `i` of the state: `clientRequest i val`'s successor, a new
read-only state, or `nil` where it is not enabled. -/
abbrev State.ClientRequest.spec : Prop :=
  ∀ (p : Loc) (st : State) (i val : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ ⌜uint.nat i ∈ st.server⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"ClientRequest")) (Val #i)) (Val #val))
  {{ (q : Loc), RET #q;
      match st.clientRequest (uint.nat i) (sint.Z val) with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
