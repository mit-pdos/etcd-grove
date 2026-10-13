/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/EtcdServer__getCommittedIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__getCommittedIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

theorem EtcdServer.getCommittedIndex.wp_proof : EtcdServer.getCommittedIndex.spec (GF := GF) (hG := hG) := by
  intro s γr
  wp_start as #Hl
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  iunfold srvCommittedInv at Hl
  wp_auto
  wp_apply_core sync.atomic.Uint64.wp_Load (structFieldRef EtcdServer go!"committedIndex" s)
    (DFrac.own 1) $$ [] [HΦ]
  · iexact Hatomic
  iinv Hl with Hi Hclose
  iapply fupd_mask_intro (Std.LawfulSet.empty_subset)
  iintro Hmask
  inext
  icases Hi with ⟨%v0, Hv, Hauth⟩
  iexists v0
  iframe Hv
  iintro Hv
  imod Hmask with -
  ihave #Hlb := monoNatLbOwn_get γr.committed _ _ $$ Hauth
  imod Hclose $$ [Hv Hauth] with -
  · inext; iexists v0; iframe Hv Hauth
  imodintro
  wp_auto
  iapply HΦ
  iunfold committedAtLeast
  iexact Hlb

end proof

end EtcdGrove
end Perennial
