/-
`snapshot.Range(startKey, endKey)`. Lean-first (no Rocq counterpart); see `InvStore.lean`.
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

/-- `p.Range(startKey, endKey)` on a snapshot of map `h.2`: the key-values in
`kvRange startKey endKey h.2`, in key order, as an owned slice of read-only `*KeyValue`s. -/
abbrev snapshot.Range.spec : Prop :=
  ∀ (p : Loc) (h : w64 × KvMap) (startSl endSl : GoSlice) (startKey endKey : GoString)
    (d1 d2 : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.cache.v3 ∗
      snapIs p h ∗ startSl ↦*{d1} startKey ∗ endSl ↦*{d2} endKey }}
    (App (App (Val (p @!! go.GoType.PointerType snapshot.ty @!! go!"Range")) (Val #startSl)) (Val #endSl))
  {{ (out : GoSlice), RET #out; startSl ↦*{d1} startKey ∗ endSl ↦*{d2} endKey ∗
      out ↦* ((kvRange startKey endKey h.2).map Prod.snd) ∗ ownSliceCap Loc out (DFrac.own 1) ∗
      kvsAt (kvRange startKey endKey h.2) }}

end spec

end EtcdGrove
end Perennial
