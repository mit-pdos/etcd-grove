/-
Proof of the spec of the same name: `WatchStream.Rev.contract` at `*watchStream` (stage 2 of the
mvcc API, 2026-11-05). Lean-first (no Rocq counterpart).

The store's reader slot is borrowed from the handle's pool with the reader token; the update fires
at the store's read, under `s.revMu` (`rev_readCb`, the store's read callback).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchStream__Rev
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.StreamHandle

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.watchStream.Rev.wp_proof : mvcc.watchStream.Rev.spec (GF := GF) (hG := hG) := by
  intro w γ ι Q
  wp_start as ⟨Hws, Hrt, Hau⟩
  icases mvcc.api.isMvccWatchStream_open w γ ι $$ Hws with
    ⟨%γw, %γc, %s, %st, %γo, %hι, #Hinv, #Hws, #Htp, #Hrp, #Hpf⟩
  obtain ⟨hι, hγ⟩ := hι
  iunfold mvcc.isWatchStreamAt at Hws
  iNamed Hws
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  ihave Hcb := mvcc.api.rev_readCb γ Q $$ Hau
  wp_auto_lc 1
  iapply fupd_wp
  ihave Hrt : ownToks (GF := GF) γw.st.api.rdk 1 $$ [Hrt]
  · iunfold mvcc.api.mvccReaders at Hrt; (try rw [hγ]); iexact Hrt
  imod mvcc.watchReader_lend s st γw $$ [$Hlc1 $Hrp $Hrt] with ⟨HPR, Hloan⟩
  imodintro
  wp_apply wp_with_defer as %defer defer
  wp_apply sync.Mutex.wp_Lock $$ [$Hmu] as ⟨Hlocked, HR⟩
  iunfold mvcc.isWatchable at Hwable
  icases Hwable with ⟨%wi, %hwa, #Hwatch, #Hprog, #HprogAll, #Hrev⟩
  have hwi : wi = ⟨go.GoType.PointerType watchableStore.ty, #s⟩ := by
    simp only [interface.mkOk, GoInterface.ok.injEq] at hwa; exact hwa.symm
  subst hwi
  ihave HPR : (mvcc.storeWatchParams s st γw).R $$ [HPR]
  · simp only [mvcc.storeWatchParams]; iexact HPR
  ihave Hcb : (mvcc.storeWatchParams s st γw).RevCb
      (fun L => iprop(∃ σ : mvcc.api.MvccState, Q σ ∗ ⌜σ.log = L⌝)) $$ [Hcb]
  · simp only [mvcc.storeWatchParams]; rw [hγ]; iexact Hcb
  wp_apply Hrev $$ [$HPR $Hcb] as %r ⟨HPR, %L, ⟨%σ, HQ, %hσ⟩, %HL⟩
  iapply wp_fupd
  wp_apply sync.Mutex.wp_Unlock $$ [$Hmu $Hlocked $HR]
  simp only [mvcc.storeWatchParams]
  imod Hloan $$ HPR with Hrt
  ihave Hrt : mvcc.api.mvccReaders (GF := GF) γ 1 $$ [Hrt]
  · iunfold mvcc.api.mvccReaders; (try rw [← hγ]); iexact Hrt
  imodintro
  wp_auto
  iapply HΦ
  iframe Hrt
  iexists σ
  iframe HQ
  ipureintro
  rw [HL.2, mvcc.api.MvccState.rev, hσ]
  have : 1 ≤ L.length := List.length_pos_iff.2 HL.1
  congr 1
  omega

end proof

end EtcdGrove
end Perennial
