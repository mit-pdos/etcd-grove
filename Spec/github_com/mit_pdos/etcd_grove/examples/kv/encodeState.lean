/- Lean-first (no Rocq counterpart).

`encodeState(kv, applied)` (kv.go, D22 S-r): the store's map and applied table as a snapshot's
data (`encState`), of some list of its bindings and some list of its operations (in Go, in
increasing order; see `less.spec`).
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

/-- The bindings `kvs` are the map `K`'s, and well formed for `decodeState` (`KVsWf`). -/
def KVsOf (K : GMap GoString GoString) (kvs : List (GoString × GoString)) : Prop :=
  KVsWf kvs ∧ ∀ k, kvs.lookup k = K !! k

/-- The operations `ops` are the table `A`'s keys, and well formed (`OpsWf`). -/
def OpsOf (A : GMap GoString Bool) (ops : List GoString) : Prop :=
  OpsWf ops ∧ ∀ o, o ∈ ops ↔ (A !! o).isSome

/-- See the file header. -/
abbrev encodeState.spec : Prop :=
  ∀ (mK mA : Loc) (K : GMap GoString GoString) (A : GMap GoString Bool) (dq1 dq2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.kv ∗
      mK ↦${dq1} K ∗ mA ↦${dq2} A }}
    (App (App (Val (@! github_com.mit_pdos.etcd_grove.examples.kv.encodeState)) (Val #mK)) (Val #mA))
  {{ (s : GoSlice), RET #s; mK ↦${dq1} K ∗ mA ↦${dq2} A ∗
      ∃ (kvs : List (GoString × GoString)) (ops : List GoString),
        s ↦* encState kvs ops ∗ ⌜KVsOf K kvs ∧ OpsOf A ops⌝ }}

end spec

end kv
end EtcdGrove
end Perennial
