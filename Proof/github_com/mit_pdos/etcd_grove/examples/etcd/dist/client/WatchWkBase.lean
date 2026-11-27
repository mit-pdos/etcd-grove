/-
**The watch workload's vocabulary** (W4d of `notes/watch-cut-plan.md`, 2026-10-22; watchkv's,
`Proof/.../watchkv/Defs.lean`, for linkv3p's copy of its program). Lean-first (no Rocq
counterpart).

The program's structs by short names (`wkv`, `wev`, `wrec`), the prefix `wkPfx`, `genPut`'s keys
and values (`genKeys`, `genVals`), `pairOf` (a `kv`'s key and value), `GenKv` (a `kv` `genPut`
may return), `CheckOk` (what `checkWatch` needs not to panic).

Moved here from `partition/` (2026-11-27): the multi-machine theorem reuses these facts, and no example's
package `Base` is imported (names and namespace `etcd_partition` unchanged).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchBase

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_partition


section pure
variable [GooseExts]

/-- The program's structs (`kv`, `event`, `putRec`), by short names. -/
abbrev wkv := etcdstart.wkv
abbrev wev := etcdstart.wev
abbrev wrec := etcdstart.wrec

/-- The prefix the writers' keys are under and the watch covers. -/
abbrev wkPfx : GoString := go!"wk/"

/-- The keys `genPut` picks from. -/
abbrev genKeys : List GoString := [go!"wk/k0", go!"wk/k1", go!"wk/k2"]

/- The values `Gen` picks from, a `KV`'s pair, a `KV` `Gen` may return, what `Check` needs not to
panic: the shared start's (`common/WatchBase.lean`). -/
export etcdstart (genVals pairOf GenKv CheckOk)

end pure

end etcd_partition
end EtcdGrove
end Perennial
