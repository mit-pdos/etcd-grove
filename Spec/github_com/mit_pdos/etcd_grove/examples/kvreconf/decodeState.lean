/- Lean-first (no Rocq counterpart).

`decodeState(b)` (kv.go, D22 S-r): what `encodeState` wrote (`encState kvs ops`, both well
formed), read back: the map of the bindings `kvs` and the table of the bindings `ops` (no
repeated key, so each key's value is its binding's), and `ok`. Stated of bytes `encodeState`
wrote (a snapshot's data, by its certificate), so `ok` is `true`. (2026-10-22, the
snapshot-liveness fix: the table maps each operation applied to its answer; both maps are read
by `getMap`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]

/-- See the file header. -/
abbrev decodeState.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (kvs ops : List (GoString × GoString)),
  KVsWf kvs → KVsWf ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kvreconf ∗
      b ↦*{dq} encState kvs ops }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kvreconf.decodeState)) (Val #b))
  {{ (mK mA : Loc), RET (PairV (PairV #mK #mA) #true); b ↦*{dq} encState kvs ops ∗
      ∃ (K A : GMap GoString GoString), mK ↦$ K ∗ mA ↦$ A ∗
        ⌜(∀ k, K !! k = kvs.lookup k) ∧ (∀ o, A !! o = ops.lookup o)⌝ }}

end spec

end kvreconf
end EtcdGrove
end Perennial
