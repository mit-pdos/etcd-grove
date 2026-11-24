/- Lean-first (no Rocq counterpart).

`MainN(k)` (check.go; 2026-11-16, kvraftN): `Main()` on `k` voters, with up to `k + 4` replicas
(`RandomConfigN(k)`): `Run` of the random configuration with a counter clock, a panic unless
porcupine answers `Ok`, then `Stop`; for `k` outside `[1, 1000]` it returns at once (2026-11-24, the
range check: until then the spec took `1 ≤ k < 2^59` and the top-level statement `1 ≤ k ≤ 1000`).
It returns, for every `k` and executions of fewer than `2^61` steps (`receiptBound GF ≤ 2^61`), from package initialization and `context`'s
`isClosedchanInit` (as `Main`, `Main.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Assumptions]

/-- See the file header. -/
abbrev MainN.spec : Prop :=
  ∀ (k : w64),
  -- (2026-11-02, durability stage II (l), at the landing: raft's `RestartNode` takes `readyFits`;
  -- until then `2^63`)
  receiptBound GF ≤ 2 ^ 61 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf ∗
      context.isClosedchanInit }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.MainN)) (Val #k))
  {{ RET #(); True }}

end spec

end raft_kvreconf
end EtcdGrove
end Perennial
