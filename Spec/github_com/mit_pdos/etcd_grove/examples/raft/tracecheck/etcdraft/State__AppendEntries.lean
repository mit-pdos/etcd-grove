/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.AppendEntries(i, j, b, e)`: the action `AppendEntries(i, j, <<b, e>>)`.
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

/-- `s.AppendEntries(i, j, b, e)`: `AppendEntriesInRangeToPeer`'s spec with subtype `"app"`. -/
abbrev State.AppendEntries.spec : Prop :=
  ∀ (p : Loc) (st : State) (i j b e : w64) (o : Option State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜uint.nat i ∈ st.server ∧ st.pendingMessages.Ok ∧
        -2 ^ 62 < sint.Z b ∧ sint.Z b < 2 ^ 62 ∧ -2 ^ 62 < sint.Z e ∧ sint.Z e < 2 ^ 62 ∧
        st.appendEntries (uint.nat i) (uint.nat j) (sint.Z b) (sint.Z e) = .ok o⌝ }}
    (App (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"AppendEntries")) (Val #i)) (Val #j)) (Val #b)) (Val #e))
  {{ (q : Loc), RET #q;
      match o with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
