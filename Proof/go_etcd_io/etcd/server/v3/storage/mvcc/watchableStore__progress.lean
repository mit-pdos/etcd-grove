/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progress
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressIfSync

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchableStore.progress.wp_proof
    (hPIS : mvcc.watchableStore.progressIfSync.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.progress.spec (GF := GF) (hG := hG) := by
  intro s st γ w
  wp_start as ⟨#Hws, #Hiw, HR⟩
  ihave #Hiw' := Hiw
  simp only [mvcc.storeWatchParams]
  icases Hiw' with ⟨%γw, %r, %fcs, #Hmeta, #Hfix, %Hsr⟩
  ihave #Hfix' := Hfix
  iunfold mvcc.watcherFixed at Hfix'
  icases Hfix' with ⟨%Hnn, %ks, %es, -, -, -, -, -, #Hid, -⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %mp Hmp
  wp_apply wp_mapInsert WatchID.ty mp ∅ r.id w $$ [$Hmp] as Hmp
  (try wp_auto)
  wp_apply (hPIS s st γ mp (DFrac.own 1) (<[r.id := w]> ∅) r.id) $$ [$Hws $Hmp $HR] as %b ⟨-, HR⟩
  · imodintro
    iintro %id %w' %Hl
    by_cases h : id = r.id
    · subst h; rw [GMap.lookup_insert] at Hl; cases Hl
      simp only [mvcc.storeWatchParams]
      iexists γw, r, fcs
      iframe #
      ipureintro; exact Hsr
    · rw [GMap.lookup_insert_ne _ _ (Ne.symm h), GMap.lookup_empty] at Hl; cases Hl
  (try wp_auto)
  iapply HΦ
  iframe HR

end proof

end EtcdGrove
end Perennial
