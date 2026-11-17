/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.find(m)`: the position of `m` in `b`'s items, or -1.
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

/-- `b.find(m)`: the position of the first item holding `m` (`List.findIdx?`), or -1. -/
abbrev Bag.find.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (p : Loc) (m : Msg),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗ msgRO p m }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"find")) (Val #p))
  {{ (k : w64), RET #k;
      ⌜sint.Z k = match b.findIdx? (fun it => it.1 == m) with | some i => (i : Int) | none => -1⌝ }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
