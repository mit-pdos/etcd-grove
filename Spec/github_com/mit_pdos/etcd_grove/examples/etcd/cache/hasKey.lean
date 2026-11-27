/- Lean-first (no Rocq counterpart).

`hasKey(kvs, key)` (etcd_cache.go; the cache's `Get` check, 2026-11-02): whether one of the key-values
`kvs` (pointers `ps` holding etcd's key-values `s`, index by index, read-only: `kvsHold`, in
`dist/client/CacheBase.lean`) has the key `key`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.cache.Defs
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_cache

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.etcd.cache go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.cache.Assumptions]

/-- See the file header. -/
abbrev hasKey.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (s : List EtcdKv) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.etcd.cache ∗
      sl ↦*□ ps ∗ kvsHold ps s }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.etcd.cache.hasKey)) (Val #sl))
      (Val #key))
  {{ (b : Bool), RET #b; ⌜b = true ↔ ∃ v ∈ s, v.key = key⌝ }}

end spec

end etcd_cache
end EtcdGrove
end Perennial
