/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.discard(m)`: `Discard(m)`, on a clone being built.
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

/-- `s.discard(m)` on a clone being built: `discard m`. The bag's messages distinct (`Bag.Without`'s
premise). -/
abbrev State.discard.spec : Prop :=
  ∀ (p : Loc) (st : State) (M : List ID) (q : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateOwn p st M ∗ msgRO q m ∗
      ⌜(st.messages.map Prod.fst).Nodup⌝ }}
    (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"discard")) (Val #q))
  {{ RET #(); stateOwn p (st.discard m) M }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
