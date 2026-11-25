/-
`client.MainReady(w, eps, nodes, ready)`, **kv arm only** (M1): of a `kv` workload (kind 0) the switch
reaches `RunKV` alone; the other arms are N7's. Proved for any precondition `OP` of `Orch`.
Lean-first (no Rocq counterpart); N7-kv, M1 (`notes/etcd-dist-n7kv.md`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.KvDefs
@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.etcd.dist

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : client.Assumptions]

/-- Of a `kv` workload, from `Orch`'s precondition at `nodes` and `w.ops`, `MainReady` does not panic. -/
abbrev MainReady.spec (OP : List GoString → w64 → IProp GF) : Prop :=
  ∀ (w : Workload) (eps nodes : GoSlice) (ns : List GoString) (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜w.kind = W64 0⌝ ∗ nodes ↦*□ ns ∗ readySpec ready ∗ OP ns w.ops }}
    (App (App (App (App (Val (@! client.MainReady)) (Val #w.val)) (Val #eps)) (Val #nodes)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
