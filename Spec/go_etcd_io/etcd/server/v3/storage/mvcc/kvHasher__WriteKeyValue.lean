/-
`kvHasher.WriteKeyValue` (`hash.go`): the trust boundary.
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

/-- `h.WriteKeyValue(k, v)` on a hasher (its points-to) whose `keep` map is read (at a fraction,
given back): the hasher changes (opaque), the key and value are read. -/
abbrev mvcc.kvHasher.WriteKeyValue.spec : Prop :=
  ∀ (hp : Loc) (h : kvHasher) (keep : GoMap) (dq : DFrac) (K : GMap Revision Unit)
    (key val : GoSlice) (k v : GoString) (dk dv : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      hp ↦ h ∗ ownMap keep dq K ∗ key ↦*{dk} k ∗ val ↦*{dv} v }}
    (App (App (Val (hp @!! go.GoType.PointerType kvHasher.ty @!! go!"WriteKeyValue")) (Val #key))
      (Val #val))
  {{ RET #(); (∃ h' : kvHasher, hp ↦ h') ∗ ownMap keep dq K ∗ key ↦*{dk} k ∗ val ↦*{dv} v }}

end spec

end EtcdGrove
end Perennial
