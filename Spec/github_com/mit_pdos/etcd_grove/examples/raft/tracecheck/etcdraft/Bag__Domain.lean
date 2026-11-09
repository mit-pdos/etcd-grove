/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.Domain()`: `DOMAIN b` (`Bag.domain`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Rep

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

/-- `b.Domain()`: a fresh slice of `b`'s messages, in order. -/
abbrev Bag.Domain.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"Domain")) (Val #()))
  {{ (sl : GoSlice), RET #sl; msgsRO sl b.domain }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
