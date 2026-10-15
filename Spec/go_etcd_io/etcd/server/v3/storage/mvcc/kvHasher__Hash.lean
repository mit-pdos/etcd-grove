/-
`kvHasher.Hash` (`hash.go`): the trust boundary.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `h.Hash()` returns some `KeyValueHash`. -/
abbrev mvcc.kvHasher.Hash.spec : Prop :=
  ∀ (hp : Loc) (h : kvHasher),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ hp ↦ h }}
    (App (Val (hp @!! go.GoType.PointerType kvHasher.ty @!! go!"Hash")) (Val #()))
  {{ (r : KeyValueHash), RET #r; hp ↦ h }}

end spec

end EtcdGrove
end Perennial
