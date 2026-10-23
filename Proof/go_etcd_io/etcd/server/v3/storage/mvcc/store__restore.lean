/-
Proof of `Spec/.../mvcc/store__restore.lean` (the restore plan's R4, option 1: the empty bucket
`NewStore` restores). Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__restore
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__setupMetricsReporter
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewRevBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeReadScheduledCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.restoreIntoIndex
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Logger__Info
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.NoCmpRead

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

theorem mvcc.store.restore.wp_proof
    (hSetup : mvcc.store.setupMetricsReporter.spec (GF := GF) (hG := hG))
    (hNRB : mvcc.NewRevBytes.spec (GF := GF) (hG := hG))
    (hR2B : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (hFin : mvcc.UnsafeReadFinishedCompact.spec (GF := GF) (hG := hG))
    (hSch : mvcc.UnsafeReadScheduledCompact.spec (GF := GF) (hG := hG))
    (hRII : mvcc.restoreIntoIndex.spec (GF := GF) (hG := hG))
    (hZI64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG)) :
    mvcc.store.restore.spec (GF := GF) (hG := hG) := by
  intro s γ b le ti lg q P HF RT WT W Wi Dep Cmp PutOk dqb dqi
  wp_start as ⟨Hb, #Hbk, Hrt, Hncmp, Hbv, Hkvi, Hix, Hig, Hiw, #Hle, #Hlg, %Hlgnn, Hcur, Hcmp,
    HrevMu⟩
  wp_auto
  wp_apply (hSetup s b dqb) $$ [$Hb] as Hb
  (try wp_auto)
  -- `min, max := NewRevBytes(), NewRevBytes()`, then their revisions' bytes
  wp_apply hNRB as %mn0 ⟨Hmn0, Hmn0c, %Hmn0cap⟩
  wp_apply hNRB as %mx0 ⟨Hmx0, Hmx0c, %Hmx0cap⟩
  (try wp_auto)
  wp_apply (hR2B _ mn0 _ (Or.inl (by simp))) $$ [$Hmn0 $Hmn0c] as %mn ⟨Hmn, Hmnc⟩
  (try wp_auto)
  wp_apply (hR2B _ mx0 _ (Or.inl (by simp))) $$ [$Hmx0 $Hmx0c] as %mx ⟨Hmx, Hmxc⟩
  (try wp_auto)
  -- `keyToLease := make(map[string]lease.LeaseID)`
  wp_apply (wp_map_make1 (K := GoString) (V := w64) go.string
    go_etcd_io.etcd.server.v3.lease.LeaseID.ty) as %ktl Hktl
  (try wp_auto)
  -- `tx := s.b.ReadTx()`; `tx.RLock()`
  iunfold mvcc.isKeyBackendG at Hbk
  icases Hbk with ⟨%bi, %Hbi, -, #HRTx, -, -, -⟩
  subst Hbi
  (try wp_auto)
  wp_apply HRTx $$ %q %(∅ : mvcc.Bucket) [$Hbv $Hrt] as %rt ⟨Hbv, %L, HL, #Hsnap⟩
  ihave #Hmeta := mvcc.kbNoCmp_metaNone γ RT (mvcc.delKey γ) rt ∅ L $$ Hncmp Hsnap
  iunfold mvcc.keyReadSnap at Hsnap
  (try wp_auto)
  wp_apply Hsnap $$ %q [$HL $Hbv] as ⟨Hbv, %m', %Rd, %Tok, Htok, #Hlk, #Hthin⟩
  (try wp_auto)
  -- the compaction keys: neither is there
  wp_apply (hFin rt true) $$ [] as %xf %found %Hf
  · iframe #
  obtain ⟨-, Hf0, Hfnf⟩ := Hf
  have Hfound : found = false := Hfnf rfl
  subst Hfound
  have Hxf := Hf0 rfl
  subst Hxf
  (try wp_auto)
  wp_apply (hSch rt true) $$ [] as %xs %sfound %Hs
  · iframe #
  obtain ⟨-, Hs0, Hsnf⟩ := Hs
  have Hsfound : sfound = false := Hsnf rfl
  subst Hsfound
  have Hxs := Hs0 rfl
  subst Hxs
  (try wp_auto)
  -- `keysGauge.Set(0)`
  ihave Hinit : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨⟨%e0, #Herr⟩, -, -, ⟨%gg, #Hgauge, -, #Hgset⟩, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, #HrCK, -⟩
  iunfold gaugeSetSpec at Hgset
  (try wp_auto)
  wp_apply Hgset $$ %(W64 0)
  (try wp_auto)
  -- `rkvc, revc := restoreIntoIndex(s.lg, s.kvindex)`: no entry to send (the bucket is empty);
  -- the goroutine reads nothing (`Rd` false)
  ihave #Hrc0 : mvcc.rdCap (GF := GF) (fun _ _ => iprop(False)) iprop(True) $$ []
  · iunfold mvcc.rdCap
    iintro !> %s0 %b0 HF -
    iexfalso; iexact HF
  wp_apply (hRII lg ti [] (fun _ _ => iprop(False)) iprop(True) e0) $$ [$Hix]
    as %rkvc %revc ⟨%γk, %γr, #Hsk, Hprod, #Hsr, Hcons⟩
  · iframe #
    isplitr
    · ipureintro; exact Hlgnn
    ipureintro
    exact ⟨List.Pairwise.nil, fun e h => by cases h⟩
  (try wp_auto)
  -- the chunk loop: the first range read finds nothing (the bucket is empty), so it ends
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
  ihave #Hlim := mvcc.keyReadLocked_rangeLim _ _ _ _ _ $$ Hlk
  iunfold mvcc.keyRangeLimSpec at Hlim
  -- the snapshot read is the empty bucket's (a thinning of it)
  iunfold mvcc.snapThin at Hthin
  icases Hthin with ⟨%Hthin', -⟩
  have Hm' : m' = ∅ := by
    apply (GMap.lookup_empty_iff m').1
    intro k
    cases h : m'.lookup k with
    | none => rfl
    | some v => have := Hthin' k v h; simp at this
  subst Hm'
  have Hbr : ∀ klo khi, mvcc.bucketRange (∅ : mvcc.Bucket) klo khi = [] := by
    intro klo khi; simp [mvcc.bucketRange]
  wp_for
  wp_apply Hlim $$ %bK %mn %mx %_ %_ %(DFrac.own 1) %(DFrac.own 1) %(W64 10000)
      [$HKeyG $Htok $Hmn $Hmx] as %ks %vs ⟨Htok, Hmn, Hmx, %res, #Hpv, %Hres⟩
  · ipureintro; simp [mvcc.revBytes]
  rw [Hbr] at Hres
  have Hres0 : res = [] := List.sublist_nil.1 Hres.1
  subst Hres0
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, -⟩
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  have Hk0 : ks.len = W64 0 := by
    have h1 := Hkl.1; have h2 := Hlens.1
    simp only [List.length_nil] at h2
    rw [h2] at h1; unfold sint.nat at h1; word
  (try wp_auto)
  rw [decide_eq_true Hk0]
  (try wp_auto)
  wp_for_post
  -- `close(rkvc)`: every entry (none) sent
  wp_apply (wp_spsc_close γk rkvc (mvcc.rkvProt (fun _ _ => iprop(False)) [])
    (fun sent => iprop(⌜sent.length = ([] : List mvcc.KvEnt).length⌝)) []) $$ [$Hsk $Hprod]
  · ipureintro; rfl
  (try wp_auto)
  -- `s.revMu.Lock()` on private memory; `s.currentRev = <-revc`
  wp_apply (plain.wp_Lock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
  (try wp_auto)
  wp_apply (wp_spsc_receive γr revc (mvcc.revProt ti iprop(True) []) (fun _ => iprop(False)) [])
    $$ [$Hsr $Hcons] as %v %okr Hr
  cases okr
  · simp only [Bool.false_eq_true, ↓reduceIte]
    icases Hr with ⟨⟨⟩, -⟩
  simp only [↓reduceIte]
  icases Hr with ⟨Hr, -⟩
  iunfold mvcc.revProt at Hr
  icases Hr with ⟨%Hv, -, -, %L, Hix, %HL⟩
  obtain ⟨-, Hv⟩ := Hv
  subst Hv
  have HL0 : L = [] := by
    have : mvcc.idxOfEntries L = [] := HL
    unfold mvcc.idxOfEntries at this
    exact List.map_eq_nil_iff.1 this
  subst HL0
  (try wp_auto)
  wp_apply (plain.wp_Unlock sync.atomic.Int32.wp_Add _) $$ [$HrevMu] as HrevMu
  (try wp_auto)
  -- `for key, lid := range keyToLease`: the map is empty
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply wp_map_for_range (fun (_ : List GoString) (_ : Int) => iprop(True)) $$ Hktl
  iintro %keys -
  isplitr
  · ipureintro; trivial
  isplitr
  · imodintro
    iintro %i %key %v ⟨-, %Hkv⟩
    simp at Hkv
  iintro - Hktl
  (try wp_auto)
  -- `tx.RUnlock()`
  iunfold mvcc.keyReadLocked at Hlk
  icases Hlk with ⟨#Hru, -⟩
  wp_bind (App (Val #(methods rt.ty go!"RUnlock" rt.v)) (Val #()))
  iapply Hru $$ [Htok]
  · iexact Htok
  inext
  iintro Hrt
  (try wp_auto)
  -- `s.lg.Info("kvstore restored", zap.Int64("current-rev", s.currentRev))`
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  wp_apply hZI64 _ _ as %f1 -
  (try wp_auto)
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f1]
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)
  -- the index's lock, from the rebuilt (empty) index
  have Hrep : mvcc.IdxCRep (-1) (mvcc.evsOf ([[], []] ++ [[]])) (mvcc.idxOfEntries []) :=
    mvcc.IdxCRep.nil (by decide)
  have Hpub := mvcc.idx_publish (GF := GF) ti γ.idx [] [[], []] Hrep
  have Hc : (mvcc.evsOf ([[], []] ++ [[]])).length = 0 := rfl
  rw [Hc] at Hpub
  imod Hpub $$ Hix Hig Hiw with ⟨#Hti, Hrd, Hiw⟩
  wp_apply (hInfo lg) $$ []
  · iframe #; ipureintro; exact Hlgnn
  (try wp_auto)
  iapply HΦ
  iframe
  iexact Hti

end proof

end EtcdGrove
end Perennial
