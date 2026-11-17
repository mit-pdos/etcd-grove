/-
Lean-first (no Rocq counterpart). Layer C (2026-11-09): `b.Filter(p)`: the sub-bag of `b`'s messages satisfying `p` (`Bag.filterMsgs`).
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

/-- `b.Filter(p)`: a fresh bag, `b`'s items whose message satisfies `p`, where the Go `p` computes
`pred` on every message (read-only). -/
abbrev Bag.Filter.spec : Prop :=
  ∀ (g : G.Bag) (b : Bag) (pf : GoFunc) (pred : Msg → Bool),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft ∗
      bagRO g b ∗
      □ (∀ (q : Loc) (m : Msg),
          {{ msgRO q m }} (App (Val #pf) (Val #q)) {{ RET #(pred m); True }}) }}
    (App (Val (g @!! github_com.mit_pdos.etcd_grove.examples.raft.tracecheck.etcdraft.Bag.ty @!! go!"Filter")) (Val #pf))
  {{ (g' : G.Bag), RET #g'; bagRO g' (b.filterMsgs pred) }}

end spec

end Etcdraft
end EtcdGrove
end Perennial
