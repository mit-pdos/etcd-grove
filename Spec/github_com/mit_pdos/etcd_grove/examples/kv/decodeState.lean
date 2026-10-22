/- Lean-first (no Rocq counterpart).

`decodeState(b)` (kv.go, D22 S-r): what `encodeState` wrote (`encState kvs ops`, well formed),
read back: the map of the bindings `kvs` (no repeated key, so each key's value is its binding's)
and the table of the operations `ops`, each `true`, and `ok`. Stated of bytes `encodeState`
wrote (a snapshot's data, by its certificate), so `ok` is `true`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI go_etcd_io.raft.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

/-- See the file header. -/
abbrev decodeState.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (kvs : List (GoString × GoString)) (ops : List GoString),
  KVsWf kvs → OpsWf ops →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      b ↦*{dq} encState kvs ops }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.decodeState)) (Val #b))
  {{ (mK mA : Loc), RET (PairV (PairV #mK #mA) #true); b ↦*{dq} encState kvs ops ∗
      ∃ (K : GMap GoString GoString) (A : GMap GoString Bool), mK ↦$ K ∗ mA ↦$ A ∗
        ⌜(∀ k, K !! k = kvs.lookup k) ∧ (∀ o, A !! o = if o ∈ ops then some true else none)⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
