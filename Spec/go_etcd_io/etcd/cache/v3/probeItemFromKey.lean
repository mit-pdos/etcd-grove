/-
`probeItemFromKey` (`cache/*.go`), an internal helper.
Users: `snapshot.Range` (the tree's search probes).
Proof sketch: allocates `&kvItem{key: string(key)}`.
Changes: restated over the opaque vocabulary of `Internal.lean` (the old internal handles, ghost names and certificate parameters replaced by predicates over W0's model); the spec mirrors the code.
Margin: none known.
-/
module

public import Spec.go_etcd_io.etcd.cache.v3.Internal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace Cache

open Iris Iris.BI EtcdModel EtcdWire ClientV3
open Classical

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `probeItemFromKey(key)`: a fresh item with key `key` and no key-value. -/
def probeItemFromKey.spec : Prop :=
  ∀ (sl : GoSlice) (key : GoString) (dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*{dq} key }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.probeItemFromKey)) (Val #sl))
  {{ (p : Loc), RET #p; sl ↦*{dq} key ∗ kvItemAt p key null }}

end spec

end Cache
end EtcdGrove
end Perennial
