/-
**The cache workload's vocabulary** (the part the multi-machine theorem reuses, moved here from the
cache example's `cache/Defs.lean` and `Spec/.../cache/hasKey.lean` on 2026-11-27, names and namespace
`etcd_cache` unchanged). Lean-first (no Rocq counterpart).

* The program's structs (`ckv`, `cev`), the prefix the writers' keys are under and the cache's watch
  covers (`ckPfx`), and the shared start's values (`genVals`, `pairOf`, `GenKv`, `CheckOk`).
* `kvsHold ps s`: the pointers `ps` hold etcd's key-values `s`, index by index, read-only (what
  `hasKey`'s and `checkGet`'s specs take of the cache's answer).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.WatchBase
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section pure
variable [GooseExts]

/-- The program's structs (`kv`, `event`, `putRec`), by short names. -/
abbrev ckv := etcdstart.wkv
abbrev cev := etcdstart.wev

/-- The prefix the writers' keys are under and the watch covers. -/
abbrev ckPfx : GoString := go!"ck/"

/- The values `Gen` picks from, a `KV`'s pair, a `KV` `Gen` may return, what `Check` needs not to
panic: the shared start's (`common/WatchBase.lean`). -/
export etcdstart (genVals pairOf GenKv CheckOk)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The answer's key-values, read-only**: the pointers `ps` hold `s`, index by index. -/
def kvsHold (ps : List Loc) (s : List EtcdKv) : IProp GF :=
  iprop(⌜ps.length = s.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (v : EtcdKv), ⌜ps[i]? = some p⌝ -∗ ⌜s[i]? = some v⌝ -∗ kvValAt p v)

instance kvsHold_persistent (ps : List Loc) (s : List EtcdKv) :
    Persistent (kvsHold (GF := GF) ps s) := by
  unfold kvsHold; infer_instance

/-- `kvsHold`'s introduction: the lengths agree and each `*KeyValue` holds its key-value. -/
theorem kvsHold_intro (ps : List Loc) (s : List EtcdKv) :
    ⌜ps.length = s.length⌝ ∗
      □ (∀ (i : Nat) (p : Loc) (v : EtcdKv), ⌜ps[i]? = some p⌝ -∗ ⌜s[i]? = some v⌝ -∗
        kvValAt p v) ⊢ kvsHold (GF := GF) ps s := by
  unfold kvsHold
  iintro H
  iexact H

end defs

end etcd_cache
end EtcdGrove
end Perennial
