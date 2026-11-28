/-
`kvremote.Orch(nodes, ops, timeout)`, at any precondition `OP nodes ops` (the schema the kv dispatch is
proved over until P9's `Orch.spec` exists, `client/KvDefs.lean`): it returns a verdict that is not
porcupine's `Illegal`. P9's spec gives an instance (`OP` its precondition past the package and the
address slice), at the timeout `client.RunKV` passes (0: no timeout, porcupine's search runs to its verdict): the
dispatch needs no other, and a timeout-agnostic `Orch.spec` (`∀ tmo`) gives the instance by specializing.
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
variable [package_sem : kvremote.Assumptions]

/-- `Orch` at timeout 0 (none) is safe from `OP nodes ops` and never returns `Illegal`. -/
abbrev Orch.specWith (OP : List GoString → w64 → IProp GF) : Prop :=
  ∀ (nodes : GoSlice) (ns : List GoString) (ops : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗
      nodes ↦*□ ns ∗ OP ns ops }}
    (App (App (App (Val (@! kvremote.Orch)) (Val #nodes)) (Val #ops)) (Val #(W64 0)))
  {{ (r : GoString), RET #r; ⌜r ≠ go!"Illegal"⌝ }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
