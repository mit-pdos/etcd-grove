/-
`(*consistentIndex).SetRaftTerm(raftTerm)` (keepfix (c), fork b1512efdd). Lean-first (no Rocq counterpart);
see `InvCindex.lean`.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvCindex

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.etcdserver.cindex

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

/-- `ci.SetRaftTerm(r)`, under the pair mutex, raises the raft term field to `r` if `r` is larger
(`rtMax rt r`). The caller holds the field's mirror (`ciRaftTerm γ rt`, updated) and shows that the
client's predicate of every stored triple survives the raise. -/
abbrev consistentIndex.SetRaftTerm.spec : Prop :=
  ∀ (ci : Loc) (γ : CINames) (P : w64 → w64 → w64 → IProp GF) (rt r : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex ∗ isCI ci γ P ∗
      ciRaftTerm γ rt ∗ □ (∀ k t : w64, iprop(P k t rt -∗ P k t (rtMax rt r))) }}
    (App (Val (ci @!! go.GoType.PointerType consistentIndex.ty @!! go!"SetRaftTerm")) (Val #r))
  {{ RET #(); ciRaftTerm γ (rtMax rt r) }}

end spec

end EtcdGrove
end Perennial
