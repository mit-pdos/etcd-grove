/- Lean-first (no Rocq counterpart). `hasKey(kvs, key)` (`examples/etcd/dist/client/watch.go`): copy of
the cache example's `hasKey` (`Spec/github_com/mit_pdos/etcd_grove/examples/etcd/cache/hasKey.lean`),
at the dist package's copy in `watch.go`: the same triple, the function and package initializer the
dist package's. `kvsHold` is the cache example's (`etcd_cache.kvsHold`), redeclared here with the same
body so that this spec imports no other spec.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.CacheBase
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- **The answer's key-values, read-only**: the pointers `ps` hold `s`, index by index (the cache
example's `etcd_cache.kvsHold`). -/
def kvsHold (ps : List Loc) (s : List EtcdKv) : IProp GF :=
  iprop(⌜ps.length = s.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (v : EtcdKv), ⌜ps[i]? = some p⌝ -∗ ⌜s[i]? = some v⌝ -∗ kvValAt p v)

instance kvsHold_persistent (ps : List Loc) (s : List EtcdKv) :
    Persistent (kvsHold (GF := GF) ps s) := by
  unfold kvsHold; infer_instance

omit package_sem in
/-- `kvsHold`'s introduction: the lengths agree and each `*KeyValue` holds its key-value. -/
theorem kvsHold_intro (ps : List Loc) (s : List EtcdKv) :
    ⌜ps.length = s.length⌝ ∗
      □ (∀ (i : Nat) (p : Loc) (v : EtcdKv), ⌜ps[i]? = some p⌝ -∗ ⌜s[i]? = some v⌝ -∗
        kvValAt p v) ⊢ kvsHold (GF := GF) ps s := by
  unfold kvsHold
  iintro H
  iexact H

/-- See the file header. -/
abbrev hasKey.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (s : List EtcdKv) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client ∗
      sl ↦*□ ps ∗ kvsHold ps s }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.hasKey)) (Val #sl))
      (Val #key))
  {{ (b : Bool), RET #b; ⌜b = true ↔ ∃ v ∈ s, v.key = key⌝ }}

end spec

end etcd_dist_client
end EtcdGrove
end Perennial
