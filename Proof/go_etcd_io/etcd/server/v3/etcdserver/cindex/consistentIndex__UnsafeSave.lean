/-
Proof of `Spec/consistentIndex__UnsafeSave.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__UnsafeSave
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeUpdateConsistentIndex

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

theorem consistentIndex.UnsafeSave.wp_proof
    (hu : schema.UnsafeUpdateConsistentIndex.spec (GF := GF) (hG := hG)) :
    consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG) := by
  intro ci γ tx TM PTi PTt m
  wp_start as ⟨#Hci, #Hw, HTM, HPi, HPt⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  unfold isCI
  icases Hci with ⟨#Hinv, -⟩
  wp_auto
  -- the index: the linearization point
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ HTM HPi HPt ci tx]
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
  icombine Hk Hg gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  imod HΦ $$ Hk with ⟨%Hmono, HΦ⟩
  imod Hclose $$ [Hidx Hg Hterm] with -
  · inext; iexists k, t0; iframe
  imodintro
  wp_auto
  -- the term
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ HTM HPi HPt tx index]
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
  · inext; iexists k1, t1; iframe
  imodintro
  wp_auto
  wp_bind (App (App (App (Val (@! schema.UnsafeUpdateConsistentIndex)) (Val #(GoInterface.ok tx)))
      (Val #k)) (Val #t1))
  iapply (hu tx TM PTi PTt m k t1) $$ [HTM HPi HPt]
  · iframe Hsch Hw HTM HPi HPt
    ipureintro; exact Hmono
  inext
  iintro HTM
  wp_auto
  iapply HΦ $$ HTM

end proof

end EtcdGrove
end Perennial
