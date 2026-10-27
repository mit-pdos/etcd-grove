/-
`kvHasher.Hash` (`hash.go`): the trust boundary.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.InvCompact
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.HashDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-- `h.Hash()` of a hasher `newKVHasher` made (`kvHasherOk`: a zero one's nil `hash` panics;
audit B4b, 2026-10-18) returns some `KeyValueHash`. -/
abbrev mvcc.kvHasher.Hash.spec : Prop :=
  ∀ (hp : Loc) (h : kvHasher),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗ hp ↦ h ∗
      ⌜mvcc.kvHasherOk h⌝ }}
    (App (Val (hp @!! go.GoType.PointerType kvHasher.ty @!! go!"Hash")) (Val #()))
  {{ (r : KeyValueHash), RET #r; hp ↦ h }}

end spec

end EtcdGrove
end Perennial
