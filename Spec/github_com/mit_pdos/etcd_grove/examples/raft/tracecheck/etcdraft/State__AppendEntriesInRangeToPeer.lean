/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `s.AppendEntriesInRangeToPeer(subtype, i, j, b, e)`: the action `AppendEntriesInRangeToPeer(subtype, i, j, <<b, e>>)`.
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

/-- `s.AppendEntriesInRangeToPeer(subtype, i, j, b, e)`, of a server `i` of the state whose pending
bag the Go's `Bag` handles (`Bag.Ok`), the range's ends far from overflow, where the Lean action
evaluates (`.ok o`: TLC's evaluation error is a panic of the Go's `SubSeq`, which a triple cannot
state; the caller checks the range): `o`'s successor, a new read-only state, or `nil` where it is
not enabled. -/
abbrev State.AppendEntriesInRangeToPeer.spec : Prop :=
  ∀ (p : Loc) (st : State) (gsub : GoString) (sub : String) (i j b e : w64) (o : Option State),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      stateRO p st ∗
      ⌜strRel gsub sub ∧ uint.nat i ∈ st.server ∧ st.pendingMessages.Ok ∧
        -2 ^ 62 < sint.Z b ∧ sint.Z b < 2 ^ 62 ∧ -2 ^ 62 < sint.Z e ∧ sint.Z e < 2 ^ 62 ∧
        st.appendEntriesInRangeToPeer sub (uint.nat i) (uint.nat j) (sint.Z b) (sint.Z e) = .ok o⌝ }}
    (App (App (App (App (App (Val (p @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.State.ty
      @!! go!"AppendEntriesInRangeToPeer")) (Val #gsub)) (Val #i)) (Val #j)) (Val #b)) (Val #e))
  {{ (q : Loc), RET #q;
      match o with
      | none => ⌜q = null⌝
      | some st' => stateRO q st' }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
