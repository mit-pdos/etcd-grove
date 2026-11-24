/- Lean-first (no Rocq counterpart).

`MainN(dir, k)` (check.go; 2026-11-16, kvraftN): `Main(dir)` on `k` voters, with up to `k + 4` replicas
(`RandomConfigN(k)`): `Run` of the random configuration with a counter clock and the replicas' files in
`dir`, a panic unless porcupine answers `Ok`, then `Stop`; for `k` outside `[1, 1000]` it returns at
once (2026-11-24, the range check: until then the spec took `1 ≤ k < 2^59` and the top-level statement
`1 ≤ k ≤ 1000`). It returns, for every `k`, from the program's files, none of which is a replica's file in `dir` (`kdFileName dir i` for the ids `i` in
`1 … k + 4`), and executions of fewer than `2^61` steps (`receiptBound GF ≤ 2^61`), from package
initialization and `context`'s `isClosedchanInit` (as `Main`, `Main.lean`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.kvreconf.Alloc

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace raft_kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.Assumptions]

/-- See the file header. -/
abbrev MainN.spec : Prop :=
  ∀ (dir : GoString) (fs : DurableState) (k : w64),
  receiptBound GF ≤ 2 ^ 61 →
  (∀ i ∈ raft_kvreconf.bootVoters (uint.nat k + 4), fs !! kdFileName dir i = none) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.raft.kvdurable ∗
      context.isClosedchanInit ∗ durableOwn fs }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.raft.kvdurable.MainN)) (Val #dir)) (Val #k))
  {{ RET #(); True }}

end spec

end raft_kvdurable
end EtcdGrove
end Perennial
