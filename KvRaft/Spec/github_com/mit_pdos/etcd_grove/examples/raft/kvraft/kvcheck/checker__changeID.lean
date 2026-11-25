/-
`c.changeID(cs)` (kvcheck.go): the id a random change names: one of the conf state `cs`'s voters,
outgoing voters and learners (`cs` read-only, or `nil`), or, one time in four or when it has none,
a random replica's (`randomID`).
-/
module

public import KvRaft.Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvcheck

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.Assumptions]

/-- See the file header. -/
abbrev checker.changeID.spec : Prop :=
  ∀ (c : Loc) (γ : CheckerCnt GF) (ls : List GoString) (csp : Loc) (cs : ConfStateM), 0 < ls.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck ∗ isChecker c γ ls ∗ csOpt csp DFrac.discard cs }}
    (App (Val (c @!! go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.raft.kvraft.kvcheck.checker.ty @!! go!"changeID")) (Val #csp))
  {{ (id : w64), RET #id;
      ⌜id ∈ cs.Voters' ++ cs.VotersOutgoing' ++ cs.Learners' ∨
        (1 ≤ uint.nat id ∧ uint.nat id ≤ ls.length)⌝ }}

end spec

end raft_kvcheck
end EtcdGrove
end Perennial
