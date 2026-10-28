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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- In either auth mode (E3p): only the term's invariant is used. -/
theorem EtcdServer.setTerm.wp_proofM (on : Bool) :
    EtcdServer.setTerm.specM (GF := GF) (hG := hG) on := by
  intro s E γr v
  wp_start as #Hat
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold srvAtomicsM at Hat
  icases Hat with ⟨#Hai, #Ht, -⟩
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

theorem EtcdServer.setTerm.wp_proof :
    EtcdServer.setTerm.spec (GF := GF) (hG := hG) :=
  EtcdServer.setTerm.wp_proofM false

end proof

end EtcdGrove
end Perennial
