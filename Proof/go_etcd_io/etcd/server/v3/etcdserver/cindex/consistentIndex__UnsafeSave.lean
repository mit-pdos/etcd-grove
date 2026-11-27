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
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

theorem consistentIndex.UnsafeSave.wp_proof
    (hu : schema.UnsafeUpdateConsistentIndex.spec (GF := GF) (hG := hG)) :
    consistentIndex.UnsafeSave.spec (GF := GF) (hG := hG) := by
  intro ci γ P tx TM PTi PTt m
  wp_start as ⟨#Hci, #Hw, HTM, HPi, HPt⟩
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  unfold isCI
  icases Hci with ⟨#Hinv, -, #Hpmu⟩
  (try wp_auto)
  -- (keepfix-d) the pair mutex: the term field, the index's second mirror and the predicate
  wp_apply sync.Mutex.wp_Lock $$ [$Hpmu] as ⟨Hlocked, HL⟩
  iunfold ciPairInv at HL
  icases HL with ⟨%kl, %tl, Hpk, Hterm, #HP⟩
  (try wp_auto)
  -- the index: the linearization point; under the pair mutex it is the mutex's `kl`
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ HTM HPi HPt Hpk Hterm Hlocked ci tx]
  · iPkgInit
  iinv Hinv with Hi Hclose
  imod HΦ with ⟨%k, Hk, HΦ⟩
  imodintro
  inext
  unfold ciInv
  icases Hi with ⟨%k0, Hidx, Hg, Hpk0⟩
  iexists k0
  iframe Hidx
  iintro Hidx
  unfold ciIdx
  icombine Hk Hg gives %Heq
  obtain ⟨_, rfl⟩ := Heq
  icombine Hpk0 Hpk gives %Heq'
  obtain ⟨_, rfl⟩ := Heq'
  imod HΦ $$ Hk with ⟨%Hmono, HΦ⟩
  imod Hclose $$ [Hidx Hg Hpk0] with -
  · inext; iexists k; iframe
  imodintro
  (try wp_auto)
  -- the term: owned under the pair mutex
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ HTM HPi HPt Hpk Hterm Hlocked ci tx index]
  · iPkgInit
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hmask
  inext
  iexists tl
  iframe Hterm
  iintro Hterm
  imod Hmask with -
  imodintro
  (try wp_auto)
  wp_apply sync.Mutex.wp_Unlock $$ [$Hpmu $Hlocked Hpk Hterm]
  · inext; iunfold ciPairInv; iexists k, tl; iframe Hpk Hterm HP
  (try wp_auto)
  wp_bind (App (App (App (Val (@! schema.UnsafeUpdateConsistentIndex)) (Val #(GoInterface.ok tx)))
      (Val #k)) (Val #tl))
  iapply (hu tx TM PTi PTt m k tl) $$ [HTM HPi HPt]
  · iframe Hsch Hw HTM HPi HPt
    ipureintro; exact Hmono
  inext
  iintro HTM
  (try wp_auto)
  iapply HΦ $$ %tl HP HTM

end proof

end EtcdGrove
end Perennial
