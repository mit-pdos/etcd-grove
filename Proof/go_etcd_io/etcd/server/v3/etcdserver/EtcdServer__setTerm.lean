/-
Proof of `Spec/EtcdServer__setTerm.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setTerm

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.setTerm.wp_proof :
    EtcdServer.setTerm.spec (GF := GF) (hG := hG) := by
  intro s v
  wp_start as #Hat
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold srvAtomics at Hat
  icases Hat with ⟨#Hai, #Ht⟩
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Store (srvTermAddr s) v $$ [] [HΦ]
  · iexact Hatomic
  iinv Ht with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, Hv⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  imod Hclose $$ [Hv] with -
  · inext; iexists v; iexact Hv
  imodintro
  wp_auto
  iapply HΦ
  itrivial

end proof

end EtcdGrove
end Perennial
