/- Lean-first (no Rocq counterpart).

`kvsFrom(kvs)` (linkvtxn.go): a new slice of the `KV`s of a reply's key-values (`txn.kvsIs`),
in order: each key and its `VR` (`kvVR`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Calls

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.linkvtxn

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- See the file header. -/
abbrev kvsFrom.spec : Prop :=
  ∀ (sl : GoSlice) (ps : List Loc) (kvs : List EtcdKv),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.linkvtxn ∗
      sl ↦*□ ps ∗ txn.kvsIs ps kvs }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.linkvtxn.kvsFrom)) (Val #sl))
  {{ (out : GoSlice), RET #out; out ↦* (kvs.map fun kv => (⟨kv.key, kvVR kv⟩ : KV)) ∗
      ownSliceCap KV out (DFrac.own 1) }}

end spec

end linkvtxn
end EtcdGrove
end Perennial
