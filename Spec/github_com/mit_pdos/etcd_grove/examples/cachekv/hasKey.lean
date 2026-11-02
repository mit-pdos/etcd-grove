/- Lean-first (no Rocq counterpart).

`hasKey(kvs, key)` (cachekv.go; the cache's `Get` check, 2026-11-02): whether one of the key-values
`kvs` (pointers `ps` holding etcd's key-values `s`, index by index, read-only) has the key `key`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.cachekv.Defs
public import Proof.go_etcd_io.etcd.cache.v3.InvEtcd

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace cachekv

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.cachekv go_etcd_io.etcd.cache.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.cachekv.Assumptions]

/-- **The answer's key-values, read-only**: the pointers `ps` hold `s`, index by index. -/
def kvsHold (ps : List Loc) (s : List EtcdKv) : IProp GF :=
  iprop(⌜ps.length = s.length⌝ ∗
    □ ∀ (i : Nat) (p : Loc) (v : EtcdKv), ⌜ps[i]? = some p⌝ -∗ ⌜s[i]? = some v⌝ -∗ kvValAt p v)

instance kvsHold_persistent (ps : List Loc) (s : List EtcdKv) :
    Persistent (kvsHold (GF := GF) ps s) := by
  unfold kvsHold; infer_instance

/-- See the file header. -/
abbrev hasKey.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (s : List EtcdKv) (key : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.cachekv ∗
      sl ↦*□ ps ∗ kvsHold ps s }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.cachekv.hasKey)) (Val #sl))
      (Val #key))
  {{ (b : Bool), RET #b; ⌜b = true ↔ ∃ v ∈ s, v.key = key⌝ }}

end spec

end cachekv
end EtcdGrove
end Perennial
