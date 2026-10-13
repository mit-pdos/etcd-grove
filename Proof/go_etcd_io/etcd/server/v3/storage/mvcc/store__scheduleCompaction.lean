/-
Proof of the spec of the same name (the mvcc store's compaction job, unit 5c).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__scheduleCompaction
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Compact
public import Spec.time.Since
public import Spec.encoding.binary.bigEndian__PutUint64
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.newKVHasher
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.BytesToRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__WriteKeyValue
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.kvHasher__Hash
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.Duration
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Uint32
public import Spec.go_uber_org.zap.String
public import Spec.github_com.dustin.go_humanize.Bytes
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.RevToBytes
public import Spec.time.Time__Unix
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Errorf

@[expose] public section

set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

/-! Pure facts of the job's batches: the keys a batch reads below `u64Be (rev + 1)` are revision
keys with a main at most `rev`, and one not kept is one compaction may delete (`KeyDel`). -/

theorem mvcc.sc_not_lt_prefix : ∀ (p x : List w8), ¬ go.GoStringLt (p ++ x) p
  | [], x => by intro h; unfold go.GoStringLt at h; cases h
  | a :: p, x => by
    intro h
    unfold go.GoStringLt at h
    cases h with
    | cons h' => exact mvcc.sc_not_lt_prefix p x h'
    | rel hr => exact absurd hr (Int.lt_irrefl _)

theorem mvcc.sc_u64Be_lt_inv (a b : w64) (x : List w8)
    (h : go.GoStringLt (u64Be a ++ x) (u64Be b)) : uint.Z a < uint.Z b := by
  rcases Int.lt_trichotomy (uint.Z a) (uint.Z b) with hlt | heq | hlt
  · exact hlt
  · have hab : a = b := by word
    subst hab
    exact absurd h (mvcc.sc_not_lt_prefix _ _)
  · have h2 := mvcc.RevOrder.u64Be_lt b a hlt [] x
    rw [List.append_nil] at h2
    exact absurd h (adt.strLt_asymm h2)

theorem mvcc.sc_entry {ilog : mvcc.Log} (hcs : ∀ cs ∈ ilog, cs.length < 2 ^ 63)
    (hlen : ilog.length < 2 ^ 63) {m' : mvcc.Bucket}
    (hsub : ∀ k v, m'.lookup k = some v → (mvcc.bucketMap ilog).lookup k = some v)
    (klo : GoString) (rev : w64) (hrev0 : 0 ≤ sint.Z rev) (hrev1 : sint.Z rev < 2 ^ 63 - 1) (n : Nat)
    {p : GoString × GoString}
    (hp : p ∈ (mvcc.bucketRange m' klo (u64Be (rev + W64 1))).take n) :
    ∃ (r : mvcc.Rev) (t : Bool), p.1 = mvcc.revBytes r t ∧ 0 ≤ sint.Z r.main ∧
      0 ≤ sint.Z r.sub ∧ sint.Z r.main ≤ sint.Z rev := by
  have hp' := List.mem_of_mem_take hp
  have hmem := (((mvcc.bucketRange_eq_iff m' klo _ _).1 rfl).2 p.1 p.2).1 (by simpa using hp')
  obtain ⟨hl, -, hlt⟩ := hmem
  obtain ⟨r, i, t, hr, hi, hk⟩ := mvcc.RevOrder.bucketMap_key ilog hcs (hsub _ _ hl)
  refine ⟨⟨W64 r, W64 i⟩, t, hk, ?_, ?_, ?_⟩
  · simp only; word
  · simp only; word
  · rw [hk] at hlt
    unfold mvcc.revBytes at hlt
    rw [List.append_assoc, List.append_assoc] at hlt
    have := mvcc.sc_u64Be_lt_inv _ _ _ hlt
    simp only
    word

theorem mvcc.sc_keyDel (log : mvcc.Log) (rev : w64) (A : GMap Revision Unit)
    (hA : mvcc.keepSetIs A log (sint.Z rev)) (hrl : sint.Z rev < log.length) (r : mvcc.Rev)
    (t : Bool) (key : GoString) (hk : key = mvcc.revBytes r t) (h0 : 0 ≤ sint.Z r.main)
    (h1 : sint.Z r.main ≤ sint.Z rev) (hnot : (A.lookup (mvcc.revVal r)).isSome = false) :
    mvcc.KeyDel log (sint.Z rev) key :=
  ⟨hrl, r, t, hk, h0, h1, fun hk' => by have := (hA r).2 hk'; rw [hnot] at this; cases this⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mvcc.store.scheduleCompaction.wp_proof
    (h0 : mvcc.treeIndex.Compact.spec (GF := GF) (hG := hG))
    (h1 : time.Since.spec (GF := GF) (hG := hG))
    (h2 : binary.bigEndian.PutUint64.spec (GF := GF) (hG := hG))
    (h3 : mvcc.newKVHasher.spec (GF := GF) (hG := hG))
    (h4 : mvcc.BytesToRev.spec (GF := GF) (hG := hG))
    (h5 : mvcc.kvHasher.WriteKeyValue.spec (GF := GF) (hG := hG))
    (h6 : mvcc.UnsafeSetFinishedCompact.spec (GF := GF) (hG := hG))
    (h7 : mvcc.kvHasher.Hash.spec (GF := GF) (hG := hG))
    (h8 : zap.Int64.spec (GF := GF) (hG := hG))
    (h9 : zap.Duration.spec (GF := GF) (hG := hG))
    (h10 : zap.Int'.spec (GF := GF) (hG := hG))
    (h11 : zap.Uint32.spec (GF := GF) (hG := hG))
    (h12 : zap.String.spec (GF := GF) (hG := hG))
    (h13 : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (h14 : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (h15 : mvcc.RevToBytes.spec (GF := GF) (hG := hG))
    (h16 : time.Time.Unix.spec (GF := GF) (hG := hG)) :
    mvcc.store.scheduleCompaction.spec (GF := GF) (hG := hG) := by
  intro s γ rev prev
  wp_start as ⟨#Hjob, Htok⟩
  iunfold mvcc.compactJobPre at Hjob
  icases Hjob with ⟨#Hs, #Hstop, %Hcmp, #Hlb, %log, #Hcert, %Hrev'⟩
  have Hrev : 0 ≤ sint.Z rev ∧ sint.Z rev < log.length := ⟨Hrev'.1, Hrev'.2.1⟩
  have Hnd : mvcc.NoDelPutAt log (sint.Z rev) := Hrev'.2.2
  ihave #Hs0 := Hs
  iunfold mvcc.isStore at Hs0
  iNamed Hs0
  ihave #Hbk' := mvcc.isKeyBackendG_cmp _ s γ _ _ _ Hcmp $$ Hbk
  iunfold mvcc.isKeyBackendG at Hbk'
  icases Hbk' with ⟨%bi, %Hbi, -, -, #HBT, #HForce, #HSize, #HSizeU, #HCmp⟩
  icases HCmp $$ [] with ⟨#HLSR, #HUSR, -⟩
  · ipureintro; trivial
  subst Hbi
  ihave Hmi : (mvccInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hmi with ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    ⟨%hIdx, #HIdxG, #HIdx⟩, ⟨%hPause, #HPauseG, #HPause⟩, ⟨%hTot, #HTotG, #HTot⟩,
    ⟨%cKeys, #HKeysG, #HKeys⟩, ⟨%gLast, #HLastG, #HLast⟩⟩
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  iunfold mvcc.compactTok at Htok
  icases Htok with ⟨%c', %hc', Htok⟩
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply HLSR
  (try wp_auto)
  wp_apply time.wp_Now as %t0 -
  (try wp_auto)
  wp_apply h0 ti γ.idx rev log c' $$ [$Htok] as %keep ⟨Htok, %A, Hkeep, %HA⟩
  · iframe #; ipureintro; exact ⟨hc', Hrev.1, Hrev.2⟩
  (try wp_auto)
  iunfold histSpec at HIdx HPause HTot
  iunfold counterSpec at HKeys
  icases HKeys with ⟨-, #HKeysAdd⟩
  iunfold gaugeSetSpec at HLast
  wp_apply h1 as %d1 -
  (try wp_auto)
  wp_apply HIdx
  (try wp_auto)
  wp_apply time.wp_Now as %t1 -
  (try wp_auto)
  wp_apply wp_slice_make2 (V := w8) (W64 8) as %endS ⟨HendS, -⟩
  · ipureintro; decide
  (try wp_auto)
  wp_apply (wp_bePutUint64 h2 endS _ (rev + W64 1) (by simp)) $$ [$HendS] as HendS
  (try wp_auto)
  ihave #HcfgS := Hcfg
  iStructNamedSuffix HcfgS "C"
  (try wp_auto)
  wp_apply h3 as %hv -
  (try wp_auto)
  wp_apply wp_slice_make2 (V := w8) (W64 17) as %lastS ⟨HlastS, HlastC⟩
  · ipureintro; decide
  (try wp_auto)
  -- the schema's `Key` bucket
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩⟩
  ihave #Hc2 := Hcert
  iunfold mvcc.idxCert at Hc2
  icases Hc2 with ⟨-, -, %Hlwf, -⟩
  have Hrz : sint.Z rev < 2 ^ 63 - 1 := by have := Hrev.2; have := Hlwf.2.1; omega
  irename «end» => endP
  -- the batches
  ihave HI : iprop(∃ (lst : GoSlice) (bs : List w8) (kc : w64) (hv' : kvHasher),
      "last" ∷ last_ptr ↦ lst ∗ "HlastS" ∷ lst ↦* bs ∗ "HlastC" ∷ ownSliceCap w8 lst (DFrac.own 1) ∗
      "%Hbs" ∷ ⌜bs.length = 17⌝ ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗ "h" ∷ h_ptr ↦ hv')
    $$ [last HlastS HlastC keyCompactions h]
  · iexists lastS, _, W64 0, hv
    simp only [named]
    iframe
    ipureintro; simp
  wp_for HI
  wp_apply time.wp_Now as %tst -
  (try wp_auto)
  wp_apply HBT as %bt #Hbt
  (try wp_auto)
  iunfold mvcc.isBatchTxG at Hbt
  icases Hbt with ⟨%Locked, %LockedO, #HbtS, -⟩
  ihave #HbtS0 := HbtS
  iunfold mvcc.batchTxSpecG at HbtS0
  icases HbtS0 with ⟨-, -, #HUnl0, -, -, #HLockOut, #HDel, #HRng, -⟩
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HLockOut $$ [] 
  · iframe #
  inext
  iintro ⟨Hlocked, HW, HP, -⟩
  (try wp_auto)
  iunfold mvcc.writerRes at HW
  icases HW with ⟨%ilog, %ntok, HW⟩
  iNamedSuffix HW "W"
  ihave #HcW' := HcertW
  iunfold mvcc.idxCert at HcW'
  icases HcW' with ⟨-, -, %HilWf, -⟩
  ispecialize HRng $$ []
  · ipureintro; trivial
  wp_bind (App (App (App (App (Val #(methods bt.ty _ bt.v)) (Val #bK)) (Val #lst)) (Val #endS)) (Val #_))
  iapply HRng $$ %([] : mvcc.Puts) %(1 : Qp).half %(mvcc.bucketMap ilog) %bK %lst %endS %bs %(u64Be (rev + W64 1))
    %scfg.CompactionBatchLimit' %(DFrac.own 1) %(DFrac.own 1) [] [Hlocked HbvW HlastS HendS]
  · ipureintro
    refine ⟨Hcfgl, ?_⟩
    intro hn
    have := congrArg List.length hn
    simp [u64Be_length] at this
  · iframe; iframe #
  inext
  iintro %ks %vs ⟨Hlocked, HbvW, HlastS, HendS, %m', #Hthin, #Hpv⟩
  (try wp_auto)
  rename_i igo
  irename : (igo ↦ zero_val w64 : IProp GF) => Higo
  iunfold mvcc.snapThin at Hthin
  icases Hthin with ⟨%Hsub, -⟩
  simp only [List.foldl_nil] at Hsub
  generalize hL : (mvcc.bucketRange m' bs (u64Be (rev + W64 1))).take
    (sint.Z scfg.CompactionBatchLimit').toNat = L
  have HLent : ∀ p ∈ L, ∃ (r : mvcc.Rev) (t : Bool), p.1 = mvcc.revBytes r t ∧ 0 ≤ sint.Z r.main ∧
      0 ≤ sint.Z r.sub ∧ sint.Z r.main ≤ sint.Z rev := by
    intro p hp
    rw [← hL] at hp
    exact mvcc.sc_entry HilWf.2.2 HilWf.2.1 Hsub bs rev Hrev.1 Hrz _ hp
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, #Hel⟩
  ihave %Hvl := ownSlice_len _ _ _ $$ Hvs
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave IH : iprop(∃ (n k kc : w64) (hv : kvHasher) (rv : Revision),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "h" ∷ h_ptr ↦ hv ∗ "rev" ∷ rev_ptr ↦ rv ∗ "Hlocked" ∷ Locked [] ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ L.length⌝) $$ [i Higo keyCompactions h rev Hlocked]
  · iexists W64 0, _, _, _, _
    simp only [named]
    iframe
    ipureintro; exact ⟨by decide, by simp⟩
  wp_for IH
  wp_if_destruct
  · have hlen1 : kss.length = L.length := by simpa using Hlens.1
    have hlen2 : vss.length = L.length := by simpa using Hlens.2
    have Hlt : sint.nat n < L.length := by rw [← hlen1, Hkl.1]; word
    have Hbnd2 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z ks.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd2, and_self, ↓reduceIte]
    obtain ⟨e, He⟩ : ∃ e, L[sint.nat n]? = some e := ⟨_, List.getElem?_eq_getElem Hlt⟩
    icases (BigSepL.bigSepL_lookup_acc He).1 $$ Hel with ⟨⟨%ksl, %vsl, %Hkv, #Hksl, #Hvsl⟩, -⟩
    obtain ⟨r, t, Hk, Hr0, Hs0, Hrm⟩ := HLent e (List.mem_of_getElem? He)
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    (try wp_auto)
    simp only [Hbnd2, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    have Hkb : e.1 = mvcc.revBytes r false ++ (if t then [W8 116] else []) := by
      rw [Hk]; cases t <;> simp [mvcc.revBytes]
    wp_apply (h4 ksl r (if t then [W8 116] else []) DFrac.discard (by cases t <;> simp) Hr0 Hs0)
      $$ [] as -
    · rw [← Hkb]; iexact Hksl
    (try wp_auto)
    wp_apply (wp_map_lookup2 Revision.ty (go.GoType.StructType []) keep A (mvcc.revVal r) (DFrac.own 1))
      $$ [$Hkeep] as Hkeep
    (try wp_auto)
    ihave #HDel1 := HDel $$ []
    · ipureintro; trivial
    wp_join iprop(∃ kc' : w64, keyCompactions_ptr ↦ kc' ∗ Locked [] ∗ keys_ptr ↦ ks ∗ igo ↦ n ∗
        tx_ptr ↦ GoInterface.ok bt)
      with [keyCompactions Hlocked keys Higo tx] as ⟨%kc', keyCompactions, Hlocked, keys, Higo, tx⟩
    · (try wp_auto)
      simp only [Hbnd2, and_self, ↓reduceIte]
      wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
      · ipureintro; exact Hkv.1
      ihave #Hdk : mvcc.delKey γ e.1 $$ []
      · iunfold mvcc.delKey
        iexists (sint.Z rev), log
        iframe Hlb Hcert
        ipureintro
        refine ⟨by omega, mvcc.sc_keyDel log rev A HA Hrev.2 r t e.1 Hk Hr0 Hrm ?_, Hnd⟩
        revert Hif; cases (A !! mvcc.revVal r).isSome <;> simp
      (try wp_auto)
      wp_bind (App (App (Val #(methods bt.ty _ bt.v)) (Val #bK)) (Val #ksl))
      iapply HDel1 $$ [Hlocked]
      · iframe Hlocked; iframe #
      inext
      iintro ⟨Hlocked, -⟩
      (try wp_auto)
      wp_join_done
    (try wp_auto)
    simp only [Hbnd2, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index ks (sint.Z n) kss DFrac.discard ksl Hn.1 $$ [$Hks] as -
    · ipureintro; exact Hkv.1
    (try wp_auto)
    have Hbnd3 : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z vs.len := by
      refine ⟨Hn.1, ?_⟩; have := Hvl.1; rw [hlen2] at this; word
    simp only [Hbnd3, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index vs (sint.Z n) vss DFrac.discard vsl Hn.1 $$ [$Hvs] as -
    · ipureintro; exact Hkv.2
    (try wp_auto)
    wp_apply (h5 h_ptr hv keep (DFrac.own 1) A ksl vsl e.1 e.2 DFrac.discard DFrac.discard)
      $$ [$h $Hkeep] as ⟨⟨%hv2, h⟩, Hkeep, -, -⟩
    · iframe #
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, n, kc', hv2, mvcc.revVal r
    simp only [named]
    iframe
    ipureintro
    constructor <;> word
  -- the batch read: short (the last), or full
  wp_if_destruct
  · -- the last batch: `finishedCompactRev = rev`, the compaction finished
    (try wp_auto)
    wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact))
      (Val #(GoInterface.ok bt))) (Val #rev))
    iapply (h6 bt (mvcc.bucketView γ) (mvcc.delKey γ) (mvcc.writerRes s γ) Dep Locked Ph fh [] rev
      Hrev.1) $$ [Hlocked]
    · iframe Hlocked; iframe #
      iunfold mvcc.batchTxSpec; iexact HbtS
    inext
    iintro Hlocked
    (try wp_auto)
    iunfold mvcc.compactRes at HcresW
    icases HcresW with ⟨%sched, %fin, %nf, Hmeta, Hfin, %Hnf⟩
    iunfold mvcc.metaCompact at Hmeta
    imod ghostVar_update (sched, some rev) γ.cmeta _ $$ Hmeta with Hmeta
    imod mono_nat_own_update (max nf (mvcc.crevN (sint.Z rev))) (Nat.le_max_left _ _) $$ Hfin
      with ⟨Hfin, #Hflb⟩
    ihave #Hdone : mvcc.compactedAt γ (sint.Z rev) $$ []
    · iunfold mvcc.compactedAt
      iapply monoNatLbOwn_le _ (Nat.le_max_right _ _) $$ Hflb
    wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
    iapply HUnl0 $$ [Hlocked HtoksW HwW HclogW HcurW HbvW Hmeta Hfin HP]
    · iframe Hlocked HP
      iunfold mvcc.writerRes
      iexists ilog, ntok
      simp only [named]
      iframe
      iframe #
      isplitr
      · ipureintro; exact HbudgetW
      isplitr
      · ipureintro; exact HneW
      iunfold mvcc.compactRes
      iexists sched, some rev, _
      iunfold mvcc.metaCompact
      iframe
      ipureintro
      exact Nat.le_max_right _ _
    inext
    iintro -
    (try wp_auto)
    wp_apply h1 as %d2 -
    (try wp_auto)
    wp_apply HPause
    (try wp_auto)
    wp_apply h7 h_ptr hv $$ [$h] as %hash h
    (try wp_auto)
    wp_apply HSize as %sz -
    wp_apply HSizeU as %szu -
    (try wp_auto)
    wp_apply h8 as %f0 -
    (try wp_auto)
    wp_apply h1 as %d3 -
    (try wp_auto)
    wp_apply h9 as %f1 -
    (try wp_auto)
    wp_apply h10 as %f2 -
    (try wp_auto)
    wp_apply h11 as %f3 -
    (try wp_auto)
    wp_apply h8 as %f4 -
    (try wp_auto)
    wp_apply h13 as %str5 -
    (try wp_auto)
    wp_apply h12 as %f5 -
    (try wp_auto)
    wp_apply h8 as %f6 -
    (try wp_auto)
    wp_apply h13 as %str7 -
    (try wp_auto)
    wp_apply h12 as %f7 -
    (try wp_auto)
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [f0, f1, f2, f3, f4, f5, f6, f7]
    isplitr
    · ipureintro; rfl
    iintro %fsl ⟨-, -⟩
    (try wp_auto)
    wp_apply h14 lg _ _ $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    wp_for_post
    wp_apply time.wp_Now as %tn -
    (try wp_auto)
    wp_apply h16 as %un -
    (try wp_auto)
    wp_apply HLast
    (try wp_auto)
    wp_apply HKeysAdd
    (try wp_auto)
    wp_apply h1 as %d4 -
    (try wp_auto)
    wp_apply HTot
    (try wp_auto)
    wp_apply HUSR
    (try wp_auto)
    iapply HΦ
    iframe Htok
    ileft
    iframe Hdone
    ipureintro; rfl
  -- a full batch: committed, then the next one after the sleep, unless the store stops
  wp_bind (App (Val #(methods bt.ty _ bt.v)) (Val #()))
  iapply HUnl0 $$ [Hlocked HtoksW HwW HclogW HcurW HbvW HcresW HP]
  · iframe Hlocked HP
    iunfold mvcc.writerRes
    iexists ilog, ntok
    simp only [named]
    iframe
    iframe #
    ipureintro; exact ⟨HbudgetW, HneW⟩
  inext
  iintro -
  (try wp_auto)
  wp_apply (h15 _ lst bs (Or.inl Hbs)) $$ [$HlastS $HlastC] as %lst2 ⟨HlastS, HlastC⟩
  (try wp_auto)
  wp_apply HForce $$ []
  · isplitl [] <;> itrivial
  (try wp_auto)
  wp_apply h1 as %d5 -
  (try wp_auto)
  wp_apply HPause
  (try wp_auto)
  wp_apply +noauto time.wp_After as %tch %γt #Hbag
  wp_auto_lc 2
  ihave #Hstop0 := Hstop
  iunfold mvcc.storeStop at Hstop0
  icases Hstop0 with ⟨%stc, #Hstc, #Hstcc⟩
  iunfold mvcc.isStopChan at Hstcc
  icases Hstcc with ⟨%γs, #Hstcc⟩
  icombine Hstopc Hstc gives %Hsteq
  subst Hsteq
  ihave #Hfmt : isPkgInit (PROP := IProp GF) pkg_id.fmt $$ []
  · iPkgInit
  wp_apply_core chan.wp_select_blocking
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists time.Time, inferInstance, inferInstance, inferInstance, inferInstance, tch, γt
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply is_bag_is_chan $$ Hbag
    iapply bag_recv_au $$ [$Hlc1 $Hlc2] Hbag
    inext
    iintro %tm' -
    wp_auto
    wp_for_post
    iframe
    iexists lst2, _, kc, hv
    simp only [named]
    iframe
    ipureintro
    rw [List.length_append, mvcc.revBytes_length]
    simp [Hbs]
  iapply BigAndL.bigAndL_cons.2
  isplit
  · simp only [chan.blockingClausePre]
    iexists Unit, inferInstance, inferInstance, inferInstance, inferInstance, sstop, γs
    isplitr
    · ipureintro; rfl
    isplitr
    · iapply ownBroadcastChan_is_chan $$ Hstcc
    iapply broadcast_chan_receive _ _ _ _ _ $$ Hstcc
    iintro ⟨-, #Hdone⟩
    wp_auto
    wp_apply mvcc.wp_Errorf_errorfIs $$ [] as %err #Herr
    · iframe #; iapply ownSlice_nil
    (try wp_auto)
    wp_for_post
    wp_apply time.wp_Now as %tn -
    (try wp_auto)
    wp_apply h16 as %un -
    (try wp_auto)
    wp_apply HLast
    (try wp_auto)
    wp_apply HKeysAdd
    (try wp_auto)
    wp_apply h1 as %d4 -
    (try wp_auto)
    wp_apply HTot
    (try wp_auto)
    wp_apply HUSR
    (try wp_auto)
    iapply HΦ
    iframe Htok
    iright
    iframe Herr
    iunfold mvcc.storeStopped
    iexists sstop, γs
    iframe Hstc Hdone
  iapply BigAndL.bigAndL_nil.2
  itrivial

end proof

end EtcdGrove
end Perennial

