/- Lean-first (no Rocq counterpart). kvreconf's spec (the same Go text), ported.

`getMap(b)` (kv.go, 2026-10-22, the snapshot-liveness fix): what `putMap` wrote at the start of
`b` (`encMap kvs`, well formed), read back: the map of the bindings `kvs` (no repeated key, so
each key's value is its binding's), the rest of `b` (a slice of it, which gives it back), and
`ok`. Stated of bytes `putMap` wrote (a snapshot's data, by its certificate), so `ok` is `true`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Base
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.Codec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]

/-- See the file header. -/
abbrev getMap.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (kvs : List (GoString × GoString)) (r : List w8),
  KVsWf kvs →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvdurable ∗
      b ↦*{dq} (encMap kvs ++ r) }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvdurable.getMap)) (Val #b))
  {{ (mK : Loc) (rest : GoSlice), RET (PairV (PairV #mK #rest) #true);
      rest ↦*{dq} r ∗ (rest ↦*{dq} r -∗ b ↦*{dq} (encMap kvs ++ r)) ∗
      ∃ K : GMap GoString GoString, mK ↦$ K ∗ ⌜∀ k, K !! k = kvs.lookup k⌝ }}

end spec

end kvdurable
end EtcdGrove
end Perennial
