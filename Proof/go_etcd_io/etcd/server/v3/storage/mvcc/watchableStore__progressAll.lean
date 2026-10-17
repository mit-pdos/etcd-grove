/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressAll
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

theorem mvcc.watchableStore.progressAll.wp_proof
    (hPIS : mvcc.watchableStore.progressIfSync.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.progressAll.spec (GF := GF) (hG := hG) := by
  intro s st γ m dq M γc o ch L
  wp_start as ⟨#Hws, Hm, #HM, #Hpf, HPC, HR⟩
  wp_auto
  -- the stream's registered watchers (K1b): each of the map, or cancelled for its reason
  ihave #Hcw : mvcc.complWS γ γc M (mvcc.progCompl (mvcc.storeWatchParams s st γ) γc M o ch L) $$ []
  · iunfold mvcc.complWS
    iintro !> %L0 %u %γw %ql %hex #Hmu HPC Hregl Hlv
    iunfold mvcc.progCompl at HPC
    cases o
    · simp only [Bool.false_eq_true, ↓reduceIte]
      icases HPC with #Hcan
      obtain ⟨id0, hid0⟩ := hex
      icases Hcan $$ %id0 %u %hid0 with Hcn0
      simp only [mvcc.storeWatchParams]
      icases Hcn0 with ⟨%γw', #Hm', #Hcn⟩
      ihave %Hag := mvcc.watcherMeta_agree γ u γw γw' $$ Hmu Hm'
      subst Hag
      iunfold mvcc.cancelled at Hcn
      ihave %Hb := dghostVar_agree $$ Hlv Hcn
      cases Hb
    · simp only [↓reduceIte]
      icases HPC with ⟨HCR, #Hc⟩
      simp only [mvcc.storeWatchParams] at *
      icases HCR with ⟨#Hisch, #Hinv, Hg⟩
      ihave %HL := ghostVar_agree $$ Hregl Hg
      subst HL
      iframe Hregl Hlv
      isplitl [Hg]
      · iunfold mvcc.progCompl
        simp only [↓reduceIte, mvcc.storeWatchParams]
        iframe Hisch Hinv Hg Hc
      iintro !> %w0 %hw0
      icases Hc $$ %w0 %hw0 with (Hin | Hcf)
      · ileft; iexact Hin
      iright
      iunfold mvcc.cancelledFor at Hcf
      icases Hcf with ⟨-, %r0, %fcs0, %lo0, #Hwi, #Hrs⟩
      simp only [mvcc.storeWatchParams]
      iunfold mvcc.watcherIs at Hwi
      icases Hwi with ⟨%γw0, %C0, -, #Hf0, -⟩
      iunfold mvcc.rsnW
      iexists r0, fcs0
      iframe Hf0 Hrs
  wp_apply (hPIS s st γ m dq M _ γc (mvcc.progCompl (mvcc.storeWatchParams s st γ) γc M o ch L))
    $$ [$Hws $Hm $HR $HPC] as %b ⟨Hm, HPC, HR⟩
  · isplitr
    · iintro !> %id %w %hw
      icases HM $$ %id %w %hw with ⟨#HIW, #HOC⟩
      iframe HIW
      simp only [mvcc.storeWatchParams] at *
      icases HOC with ⟨%γw, #Hm, %Hwc⟩
      icases HIW with ⟨%γw', %r, %fcs, -, #Hf, -⟩
      iexists γw, r, fcs
      iframe Hm Hf
      isplitr
      · ipureintro; exact Hwc
      iright
      rw [Hwc]
      iexact Hpf
    iright; iexact Hcw
  (try wp_auto)
  iapply HΦ
  iframe Hm HPC HR

end proof

end EtcdGrove
end Perennial
