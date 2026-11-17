/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.reply(response, request)`: `Reply(response, request)`, on a clone being built.
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

/-- `s.reply(response, request)` on a clone being built: `reply response request`. The bags'
messages distinct and the response's count below `2^63 - 1` (`Bag.With`'s and `Bag.Without`'s
premises). -/
abbrev State.reply.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (q : Loc) (m : Msg) (r : Loc) (n : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ msgRO q m ∗ msgRO r n ∗
      ⌜(st.pendingMessages.map Prod.fst).Nodup ∧ (st.pendingMessages.count m : Int) + 1 < 2 ^ 63 ∧
        (st.messages.map Prod.fst).Nodup⌝ }}
    (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"reply")) (Val #q)) (Val #r))
  {{ RET #(); stateOwn p (st.reply m n) M }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
