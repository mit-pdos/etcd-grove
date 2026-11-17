/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.Ready(i)`: the action `Ready(i)`.
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

/-- `s.Ready(i)`, of a server `i` of the state whose pending bag's messages are distinct and whose
two bags' counts sum below `2^63` (`Bag.Plus`'s and `Bag.Minus`'s premises): `ready i`, a new
read-only state. -/
abbrev State.Ready.spec : Prop :=
  ∀ (p : Loc) (st : State) (i : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜uint.nat i ∈ st.server ∧ (st.pendingMessages.map Prod.fst).Nodup ∧
        (((st.pendingMessages.map Prod.snd).sum + (st.messages.map Prod.snd).sum : Nat) : Int) < 2 ^ 63⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"Ready")) (Val #i))
  {{ (q : Loc), RET #q; stateRO q (st.ready (uint.nat i)) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
