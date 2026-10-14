/-
`FromKey` (`cache/predicate.go`). Lean-first (no Rocq counterpart); see `InvCache.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvCache

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `FromKey(start)`: a closure implementing `fromKeyPred start` (`bytes.Compare(k, start) >=
0`). It keeps `start`, so `start`'s slice must stay read-only. -/
abbrev FromKey.spec : Prop :=
  ∀ (sl : GoSlice) (start : GoString),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ sl ↦*□ start }}
    (App (Val (@! go_etcd_io.etcd.cache.v3.FromKey)) (Val #sl))
  {{ (f : GoFunc), RET #f; ⌜f ≠ func.nil⌝ ∗ keyPredSpec f (fromKeyPred start) }}

end spec

end EtcdGrove
end Perennial
