/-
Proof of `Spec/consistentIndex__UnsafeConsistentIndex.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__UnsafeConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.schema.UnsafeReadConsistentIndex

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
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.cindex.Assumptions]

theorem consistentIndex.UnsafeConsistentIndex.wp_proof
    (hS : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hR : schema.UnsafeReadConsistentIndex.spec (GF := GF) (hG := hG)) :
    consistentIndex.UnsafeConsistentIndex.spec (GF := GF) (hG := hG) := by
  intro ci γ b E View
  wp_start as ⟨#Hci, Hown, #Hbe⟩
  ihave #Hatomic : isPkgInit (PROP := IProp GF) pkg_id.sync.atomic $$ []
  · iPkgInit
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  iunfold isCI at Hci
  icases Hci with ⟨#Hinv, #Hmu⟩
  (try wp_auto)
  -- the fast read: the first linearization point
  wp_apply_core sync.atomic.wp_LoadUint64 $$ [] [HΦ Hown ci]
  · iPkgInit
  iinv Hinv with Hi Hclose
  imod HΦ with ⟨%k, Hk, HΦ⟩
  imodintro
  inext
  iunfold ciInv at Hi
  icases Hi with ⟨%k0, %t0, Hidx, Hg, Hterm⟩
  iexists k0
  iframe Hidx
  iintro Hidx
  ihave %Heq := ciIdx_agree $$ Hk Hg
  subst Heq
  imod HΦ $$ Hk with HΦ
  imod Hclose $$ [Hidx Hg Hterm] with -
  · inext; iunfold ciInv; iexists k, t0; iframe
  imodintro
  (try wp_auto)
  wp_if_destruct
  · -- k ≠ 0: return it
    have hk : k ≠ W64 0 := by intro h; subst h; simp at Hif
    simp only [hk, ↓reduceIte]
    (try wp_auto)
    iapply HΦ $$ Hown
  -- k = 0: load the index from the backend, reading `be` with the owner's half
  have hk : k = W64 0 := by word
  subst hk
  simp only [↓reduceIte]
  iunfold ciOwner at Hown
  (try wp_auto)
  iunfold isMetaBackend at Hbe
  icases Hbe with ⟨%bi, %Hbi, #HReadTx⟩
  subst Hbi
  dsimp only
  wp_apply HReadTx as %rt #Hrt
  iunfold metaReadTx at Hrt
  icases Hrt with ⟨-, -, #Hrd⟩
  (try wp_auto)
  wp_apply_core (hR rt E View) $$ [] [HΦ Hown ci]
  · iframe Hsch Hrd
  iapply readCIAU_wand $$ HΦ
  iintro %m Hm
  (try wp_auto)
  -- the store: the second linearization point
  wp_apply_core (hS ci γ m.1 m.2) $$ [] [Hm Hown v]
  · iframe Hpkg; iunfold isCI; iframe Hinv Hmu
  imod Hm with ⟨%k', Hk', Hm⟩
  imodintro
  iexists k'
  iframe Hk'
  iintro Hk'
  imod Hm $$ Hk' with Hm
  imodintro
  (try wp_auto)
  iapply Hm
  iunfold ciOwner
  iexact Hown

end proof

end EtcdGrove
end Perennial
