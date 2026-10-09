/-
`newKVItem(kv)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
-/
module

public import Proof.go_etcd_io.etcd.cache.v3.InvStore

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.cache.v3 go_etcd_io.etcd.api.v3

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.cache.v3.Assumptions]

/-- `newKVItem(kv)`: a new read-only `kvItem` with key `string(kv.Key)`. -/
abbrev newKVItem.spec : Prop :=
  ∀ (e : KvEntry),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗ kvAt e }}
    (App (Val (@! newKVItem)) (Val #e.2))
  {{ (p : Loc), RET #p; kvItemIs p e }}

end spec

end EtcdGrove
end Perennial
