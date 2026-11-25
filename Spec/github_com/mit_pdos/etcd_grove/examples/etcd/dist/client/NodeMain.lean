/-
`client.NodeMain(w, c, addr, eps)`, **kv arm only** (M1): of a `kv` workload, when `c` is one of its
client machines and `eps` is not empty, `kvremote.Node(c, addr, Rotate(eps, c))`; otherwise it returns.
Proved for any precondition `NP` of `Node`. `Rotate`'s index
arithmetic needs `c + len(eps)` within `int`, for a `c` that passes the guard (`0 ≤ c < clients`): the
premise (a well-formed deployment's client count is below `2 ^ 31`, its members at most 64).
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

/-- Of a `kv` workload, from `Node`'s precondition at `c`, `addr` and the rotated endpoints, `NodeMain`
does not panic. -/
abbrev NodeMain.spec (NP : w64 → GoString → List GoString → IProp GF) : Prop :=
  ∀ (w : Workload) (c : w64) (addr : GoString) (eps : GoSlice) (epsL : List GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      ⌜w.kind = W64 0 ∧
        (0 ≤ sint.Z c → sint.Z c < sint.Z w.clients → sint.Z c + epsL.length ≤ 2 ^ 63)⌝ ∗ eps ↦*□ epsL ∗ NP c addr (rotateL epsL (sint.nat c)) }}
    (App (App (App (App (Val (@! client.NodeMain)) (Val #w.val)) (Val #c)) (Val #addr)) (Val #eps))
  {{ RET #(); True }}

end spec

end etcd_dist
end EtcdGrove
end Perennial
