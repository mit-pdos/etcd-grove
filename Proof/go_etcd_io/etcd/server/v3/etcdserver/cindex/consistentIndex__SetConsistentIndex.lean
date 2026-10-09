/-
Proof of `Spec/consistentIndex__SetConsistentIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

theorem consistentIndex.SetConsistentIndex.wp_proof :
    consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG) := by
  intro ci γ v term
  wp_start as #Hci
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  unfold isCI
  icases Hci with ⟨#Hinv, -⟩
  wp_auto
  -- the index: the linearization point
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ ci term]
  · iPkgInit
  iinv Hinv with Hi Hclose
  imod HΦ with ⟨%k, Hk, HΦ⟩
  imodintro
  inext
  unfold ciInv
  icases Hi with ⟨%k0, %t0, Hidx, Hg, Hterm⟩
  iexists k0
  iframe Hidx
  iintro Hidx
  unfold ciIdx
  imod ghostVar_update_halves v $$ Hk Hg with ⟨Hk, Hg⟩
  imod HΦ $$ Hk with HΦ
  imod Hclose $$ [Hidx Hg Hterm] with -
  · inext; iexists v, t0; iframe
  imodintro
  wp_auto
  -- the term
  wp_apply_core sync.atomic.wp_StoreUint64 $$ [] [HΦ]
  · iPkgInit
  iinv Hinv with Hi Hclose
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  icases Hi with ⟨%k1, %t1, Hidx, Hg, Hterm⟩
  iexists t1
  iframe Hterm
  iintro Hterm
  imod Hmask with -
  imod Hclose $$ [Hidx Hg Hterm] with -
  · inext; iexists k1, term; iframe
  imodintro
  wp_auto
  iexact HΦ

end proof

end EtcdGrove
end Perennial
