/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__NewWatchStream
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__watch
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progress
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__progressAll
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.watchableStore__rev
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.WatchClose
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NewWatchableLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReaderSpecs

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

/-- The watchable store is the stream's `watchable` (`isWatchable`, for `storeWatchParams`): its
`watch`, `progress`, `progressAll` and `rev` methods. -/
theorem mvcc.isWatchable_store
    (hWatch : mvcc.watchableStore.watch.spec (GF := GF) (hG := hG))
    (hProg : mvcc.watchableStore.progress.spec (GF := GF) (hG := hG))
    (hProgAll : mvcc.watchableStore.progressAll.spec (GF := GF) (hG := hG))
    (hRev : mvcc.watchableStore.rev.spec (GF := GF) (hG := hG)) (s st : Loc) (γ : mvcc.WsNames) :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc ∗
      mvcc.isWatchableStore s st γ ⊢
    mvcc.isWatchable (interface.mkOk (go.GoType.PointerType watchableStore.ty) #s)
      (mvcc.storeWatchParams s st γ) := by
  have hRev := mvcc.watchableStore.rev.spec_R hRev
  iintro ⟨#Hpkg, #Hws⟩
  iunfold mvcc.isWatchable
  iexists ⟨go.GoType.PointerType watchableStore.ty, #s⟩
  isplitr
  · ipureintro; rfl
  isplitr
  · iintro !> %key %endk %fcs %k %e %fs %startRev %id %ch %γc %L %Back !> %Φ
      ⟨#Hk, #He, #Hf, #Hfs, #HC, HCR, HR, HT, %Hsr, Hcb⟩ HΦ
    iapply (hWatch s st γ key endk fcs k e fs startRev id ch γc L Back) $$ [HCR HR HT Hcb] HΦ
    iframe Hpkg Hws Hk He Hf Hfs HC HCR HR HT Hcb
    ipureintro; exact Hsr
  isplitr
  · iintro !> %w !> %Φ ⟨#HIW, HR⟩ HΦ
    have hR : (mvcc.storeWatchParams (GF := GF) s st γ).R = mvcc.watchReader (GF := GF) s st γ := rfl
    rw [hR]
    iapply (hProg s st γ w) $$ [HR] [HΦ]
    · iframe Hpkg Hws HIW HR
    inext; iintro HR; iapply HΦ; iexact HR
  isplitr
  · iintro !> %m %dq %M %γc %o %ch %L !> %Φ ⟨Hm, #HIW, #Hpf, HPC, HR⟩ HΦ
    have hR : (mvcc.storeWatchParams (GF := GF) s st γ).R = mvcc.watchReader (GF := GF) s st γ := rfl
    rw [hR]
    iapply (hProgAll s st γ m dq M γc o ch L) $$ [Hm HPC HR] [HΦ]
    · iframe Hpkg Hws HIW Hpf Hm HPC HR
    inext; iintro %b ⟨Hm, HPC, HR⟩; iapply HΦ; iframe Hm HPC; iexact HR
  · iintro !> !> %Φ HR HΦ
    simp only [mvcc.storeWatchParams]
    iunfold mvcc.watchReader at HR
    icases HR with ⟨Hsr, Hmur⟩
    iapply (hRev s st γ none) $$ [Hsr] [Hmur HΦ]
    · iframe Hpkg Hws Hsr
      unfold mvcc.logLent; itrivial
    inext
    iintro %r ⟨Hsr, -, -⟩
    iapply HΦ
    iunfold mvcc.watchReader
    iframe Hsr Hmur

theorem mvcc.watchableStore.NewWatchStream.wp_proof
    (hWatch : mvcc.watchableStore.watch.spec (GF := GF) (hG := hG))
    (hProg : mvcc.watchableStore.progress.spec (GF := GF) (hG := hG))
    (hProgAll : mvcc.watchableStore.progressAll.spec (GF := GF) (hG := hG))
    (hRev : mvcc.watchableStore.rev.spec (GF := GF) (hG := hG)) :
    mvcc.watchableStore.NewWatchStream.spec (GF := GF) (hG := hG) := by
  intro s st γ Q Ψ
  wp_start as #Hws
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨%g, #Hg, #HgS⟩, -, -, -, -, #Hcbl, -⟩
  iunfold gaugeSpec at HgS
  icases HgS with ⟨#HgI, -, -⟩
  wp_auto
  wp_apply HgI
  wp_apply chan.wp_make2 (V := WatchResponse) $$ [] as %ch %γch ⟨#Hch, %Hcap, Hown⟩
  · ipureintro; decide
  wp_apply (wp_map_make1 (K := w64) (V := GoFunc)) as %cm Hcm
  wp_apply (wp_map_make1 (K := w64) (V := Loc)) as %wm Hwm
  wp_alloc wsl as Hs
  iStructNamed Hs
  ihave #Hwable := mvcc.isWatchable_store hWatch hProg hProgAll hRev s st γ $$ [$Hpkg $Hws]
  -- the channel's ghost state and invariant
  imod ghostVar_alloc (GF := GF) ([] : List mvcc.RespM) with ⟨%γrecv, Hrecv⟩
  icases ghostVar_halves γrecv _ $$ Hrecv with ⟨Hrecv1, Hrecv2⟩
  imod ghostVar_alloc (GF := GF) ([] : List Loc) with ⟨%γregl, Hregl⟩
  icases ghostVar_halves γregl _ $$ Hregl with ⟨Hregl1, Hregl2⟩
  imod ghost_map_alloc_empty (K := Loc) (V := Unit) (GF := GF) with ⟨%γreg, Hreg⟩
  -- the stream's id map (the channel's) and the progress fact `Q`
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Loc) with ⟨%γi, Hids⟩
  imod (saved_prop_alloc (GF := GF) Q DFrac.discard DFrac.valid_discard) with ⟨%γp, #Hsp⟩
  imod mono_list_own_alloc (GF := GF) ([] : List mvcc.RespM) with ⟨%γsl, Hsl, -⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Loc) (V := Nat) with ⟨%γri, Hri⟩
  imod (saved_pred_alloc (GF := GF) Ψ DFrac.discard DFrac.valid_discard) with ⟨%γrs, #Hrs⟩
  let γc : mvcc.WatchChanNames := ⟨γch, γrecv, γregl, γreg, γi, γp, γsl, γri, γrs⟩
  imod inv_alloc mvcc.watchN ⊤ (mvcc.watchChanInv γ ch γc) $$ [Hown Hrecv1 Hregl1 Hreg Hsl Hri] with #Hinv
  · inext
    iunfold mvcc.watchChanInv
    iexists ChanState.Buffered [], [], [], [], []
    simp only [named, EtcdGrove.chanIsClosed, Bool.false_eq_true, ↓reduceIte]
    iframe Hown Hrecv1 Hregl1
    isplitr
    · ipureintro; exact List.prefix_refl _
    isplitr
    · ipureintro; rfl
    isplitr
    · iunfold mvcc.respsIs
      isplitr
      · ipureintro; rfl
      iintro !> %i %v %r %hv
      simp at hv
    isplitr
    · iintro !>; iapply BigSepL.bigSepL_nil.2; itrivial
    isplitr
    · itrivial
    isplitl [Hreg]
    · have hrm : mvcc.regMap ([] : List Loc) = ∅ := rfl
      rw [hrm]; iexact Hreg
    isplitr
    · ipureintro; exact ⟨List.nodup_nil, by simp⟩
    isplitr
    · iintro !>; iapply BigSepL.bigSepL_nil.2; itrivial
    isplitr
    · iintro !>; iapply BigSepL.bigSepL_nil.2; itrivial
    isplitl [Hsl Hri]
    · iunfold mvcc.sentAuth
      iframe Hsl
      iexists ∅
      iframe Hri
      isplitr
      · ipureintro
        exact ⟨fun w h => by simp [GMap.lookup_empty] at h, fun w n h => by simp [GMap.lookup_empty] at h,
          fun w n k x h => by simp [GMap.lookup_empty] at h, fun k x h => by simp at h⟩
      iintro !>; iapply BigSepL.bigSepL_nil.2; itrivial
    iapply BigSepL.bigSepL_nil.2; itrivial
  -- the stream's lock
  imod token_alloc (GF := GF) with ⟨%γt, Htok⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Loc) with ⟨%γf, Hidf⟩
  let γo : mvcc.WsStreamNames := ⟨γt, γi, γf, γp, γsl, γrs, γri⟩
  imod sync.init_Mutex (mvcc.watchStreamInv wsl (mvcc.storeWatchParams s st γ) ch γc γo) ⊤
    (wsl.[watchStream, go!"mu"]) $$ mu [nextID closed cancels watchers Hcm Hwm Hregl2 Hids Hidf]
    with #Hmu
  · inext
    iunfold mvcc.watchStreamInv
    iexists _, false, cm, wm, ∅, ∅
    simp only [named, Bool.false_eq_true, ↓reduceIte]
    iframe nextID closed cancels watchers Hcm Hwm
    isplitr
    · ipureintro; intro id; rfl
    isplitr
    · ipureintro; intro id w h; simp [GMap.lookup_empty] at h
    isplitr
    · iintro !> %id %w %h; simp [GMap.lookup_empty] at h
    isplitr
    · iintro !> %id %c %w %h; simp [GMap.lookup_empty] at h
    isplitl [Hids Hidf]
    · iunfold mvcc.idsInv
      iexists ∅
      iframe Hids Hidf
      ipureintro
      refine ⟨by first | decide | rfl | (show (0 : Int) ≤ 0; omega) | word, fun i hi => ?_⟩
      simp [GMap.lookup_empty] at hi
    iexists []
    isplitl [Hregl2]
    · simp only [mvcc.storeWatchParams]
      iframe Hch Hinv Hregl2
    isplitr
    · iintro !> %w %h; simp at h
    ipureintro
    have h0 : ∀ n, mvcc.aboveCnt n (∅ : GMap w64 Loc) = 0 := fun n => by
      unfold mvcc.aboveCnt; rw [GMap.map_filter_empty, GMap.map_size_empty]
    refine ⟨?_, by simp⟩
    rw [h0]
    first | decide | (simp) | word
  ipersist watchable
  ipersist ch
  (try wp_auto)
  iapply HΦ
  iexists γo, ch, γc
  iunfold mvcc.watchStreamOpen
  iunfold mvcc.watchConsumer
  iframe Htok Hrecv2 Hch Hinv ch Hsp Hrs
  isplitr
  rotate_left
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl, by rw [Hcap]; decide⟩
  iunfold mvcc.isWatchStream
  iexists ch, γc
  simp only [named]
  iframe watchable ch Hwable Hmu
  isplitr
  · ipureintro; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  isplitr
  · simp only [mvcc.storeWatchParams]; itrivial
  iintro !> %L !> %Φ' H HΦ'
  iapply (mvcc.wp_watch_close s st γ ch γc L) $$ H HΦ'


end proof

end EtcdGrove
end Perennial
