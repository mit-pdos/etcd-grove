/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.pendingFrom(i)`: `PendingMessages(i)`.
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

/-- `s.pendingFrom(i)`: the pending messages sent by `i`, a new read-only bag. -/
abbrev State.pendingFrom.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"pendingFrom")) (Val #i))
  {{ (g : G.Bag), RET #g; bagRO g (st.pendingFrom (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
