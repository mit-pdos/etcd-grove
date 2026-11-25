/-
`client.RunKV(nodes, ops, ready)` (the kv workload's orchestration): `ready()`, then `kvremote.Orch`, and a
panic only on porcupine's `Illegal`. Proved for any precondition `OP` of `Orch` (`Orch.specWith OP`).
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

/-- From `Orch`'s precondition at `nodes` and `ops`, `RunKV` does not panic. -/
abbrev RunKV.spec (OP : List GoString → w64 → IProp GF) : Prop :=
  ∀ (nodes : GoSlice) (ns : List GoString) (ops : w64) (ready : GoFunc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      nodes ↦*□ ns ∗ readySpec ready ∗ OP ns ops }}
    (App (App (App (Val (@! client.RunKV)) (Val #nodes)) (Val #ops)) (Val #ready))
  {{ (r : client.Result), RET #r; True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
