/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.RejectAppendEntriesRequest(i, j, m, logOk)`: the action `RejectAppendEntriesRequest(i, j, m, logOk)`.
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

/-- `s.RejectAppendEntriesRequest(i, j, m, logOk)`, of a server `i` of the state whose bags the Go's
`Bag` handles (`Bag.Ok`): `rejectAppendEntriesRequest i j m logOk`'s successor, a new read-only state,
or `nil` where it is not enabled. -/
abbrev State.RejectAppendEntriesRequest.spec : Prop :=
  ∀ (p : Loc) (st : State) (i j : w64) (q : Loc) (m : Msg) (logOk : Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗ msgRO q m ∗
      ⌜uint.nat i ∈ st.server ∧ st.pendingMessages.Ok ∧ st.messages.Ok⌝ }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"RejectAppendEntriesRequest")) (Val #i)) (Val #j)) (Val #q)) (Val #logOk))
  {{ (r : Loc), RET #r;
      match st.rejectAppendEntriesRequest (uint.nat i) (uint.nat j) m logOk with
      | none => ⌜r = null⌝
      | some st' => stateRO r st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
