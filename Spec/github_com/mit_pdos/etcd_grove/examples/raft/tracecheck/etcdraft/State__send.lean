/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.send(m)`: `Send(m)`, on a clone being built.
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

/-- `s.send(m)` on a clone being built: `send m`. The pending bag's messages distinct and `m`'s
count below `2^63 - 1` (`Bag.With`'s premises). -/
abbrev State.send.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ msgRO q m ∗
      ⌜(st.pendingMessages.map Prod.fst).Nodup ∧ (st.pendingMessages.count m : Int) + 1 < 2 ^ 63⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"send")) (Val #q))
  {{ RET #(); stateOwn p (st.send m) M }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
