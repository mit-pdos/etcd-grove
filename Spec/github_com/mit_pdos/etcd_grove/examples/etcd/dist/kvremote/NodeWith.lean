/-
`kvremote.Node(c, addr, eps)`, at any precondition `NP c addr eps` (the schema the kv dispatch is
proved over until P9's `Node.spec` exists, `client/KvDefs.lean`): it is safe (it never returns in Go
once its client is made; the post claims nothing). P9's spec gives an instance.
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

/-- `Node` is safe from `NP c addr eps` and its own endpoint slice. -/
abbrev Node.specWith (NP : w64 → GoString → List GoString → IProp GF) : Prop :=
  ∀ (c : w64) (addr : GoString) (eps : GoSlice) (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.kvremote ∗
      eps ↦* epsL ∗ NP c addr epsL }}
    (App (App (App (Val (@! kvremote.Node)) (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
