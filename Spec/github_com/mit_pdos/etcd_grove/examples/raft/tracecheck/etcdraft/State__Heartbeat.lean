/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.Heartbeat(i, j)`: the action `Heartbeat(i, j)`.
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

/-- `s.Heartbeat(i, j)`: `AppendEntriesInRangeToPeer`'s spec with subtype `"heartbeat"`, range `<<1,
1>>`. -/
abbrev State.Heartbeat.spec : Prop :=
  ∀ (p : Loc) (st : State) (i j : w64) (o : Option State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜uint.nat i ∈ st.server ∧ st.pendingMessages.Ok ∧ st.heartbeat (uint.nat i) (uint.nat j) = .ok o⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"Heartbeat")) (Val #i)) (Val #j))
  {{ (q : Loc), RET #q;
      match o with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
