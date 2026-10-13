/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__setLead.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setLead

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.setLead.wp_proof :
    EtcdServer.setLead.spec (GF := GF) (hG := hG) := by
  intro s v
  wp_start as #Hl
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold srvLeadInv at Hl
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Store (srvLeadAddr s) v $$ [] [HΦ]
  · iexact Hatomic
  iinv Hl with Hi Hclose
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
