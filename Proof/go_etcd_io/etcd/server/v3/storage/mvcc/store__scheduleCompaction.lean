/-
Proof of the spec of the same name (the mvcc store's compaction job, unit 5c).
The hypotheses are the callees' specs, in the order of `etc/link-lean-first-mvcc.txt`.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__scheduleCompaction
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Compact
public import Perennial.Proof.time
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
    exact absurd h (go.goStringLt_asymm h2)

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

/-! Counting the keys the job deletes (item 8, 2026-10-17): distinct revision keys of the job's
log up to `rev` (`sc_space`), so no more than its changes, fewer than `2 ^ 62` (`CompactSmall`,
from the certificate's time receipts: `CompactSmall_of_cert`):
`keyCompactions` (an `int`) stays non-negative, as `dbCompactionKeysCounter.Add` needs. -/

/-- `k` is the bucket key of a change of `log` at a revision at most `c`. -/
def mvcc.sc_space (log : mvcc.Log) (c : Int) (k : GoString) : Prop :=
  ∃ (r i : Nat) (ch : mvcc.Change), (r : Int) ≤ c ∧ (log.getD r [])[i]? = some ch ∧
    k = mvcc.revBytes ⟨W64 r, W64 i⟩ ch.isDel

theorem mvcc.sc_sum_range (log : mvcc.Log) : ∀ n : Nat,
    ((List.range n).map fun r => (log.getD r []).length).sum = ((log.take n).map List.length).sum
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, mvcc.sc_sum_range log n,
      List.take_add_one, List.map_append, List.sum_append]
    congr 1
    cases h : log[n]? <;> simp [List.getD_eq_getElem?_getD, h]

theorem mvcc.sc_count (log : mvcc.Log) (c : Int) (D : List GoString) (hnd : D.Nodup)
    (hD : ∀ k ∈ D, mvcc.sc_space log c k) :
    D.length ≤ ((log.take (c.toNat + 1)).map List.length).sum := by
  let U : List GoString := (List.range (c.toNat + 1)).flatMap fun r =>
    (log.getD r []).zipIdx.map fun p => mvcc.revBytes ⟨W64 r, W64 p.2⟩ p.1.isDel
  have hsub : D ⊆ U := by
    intro k hk
    obtain ⟨r, i, ch, hr, hi, rfl⟩ := hD k hk
    simp only [U, List.mem_flatMap, List.mem_range, List.mem_map]
    exact ⟨r, by omega, (ch, i), List.mem_zipIdx_iff_getElem?.2 hi, rfl⟩
  have hlen : U.length = ((log.take (c.toNat + 1)).map List.length).sum := by
    simp only [U, List.length_flatMap, List.length_map, List.length_zipIdx]
    exact mvcc.sc_sum_range log _
  calc D.length ≤ U.length := (List.subperm_of_subset hnd hsub).length_le
    _ = _ := hlen

theorem mvcc.sc_mem_bucketOfRev {r : Nat} {before : List EtcdKv} {cs : List mvcc.Change}
    {p : GoString × GoString} (h : p ∈ mvcc.bucketOfRev r before cs) :
    ∃ (i : Nat) (ch : mvcc.Change), cs[i]? = some ch ∧ p.1 = mvcc.revBytes ⟨W64 r, W64 i⟩ ch.isDel := by
  unfold mvcc.bucketOfRev at h
  rw [List.mem_filterMap] at h
  obtain ⟨⟨c, i⟩, hi, hp⟩ := h
  rw [List.mem_zipIdx_iff_getElem?] at hi
  cases hk : mvcc.changeKv (W64 r) before cs i with
  | none => rw [hk] at hp; simp at hp
  | some kv =>
    rw [hk] at hp
    simp only [Option.map_some, Option.some.injEq] at hp
    exact ⟨i, c, hi, by rw [← hp]⟩

theorem mvcc.sc_bucketMap_key (log : mvcc.Log) {k v : GoString}
    (h : (mvcc.bucketMap log).lookup k = some v) :
    ∃ (r i : Nat) (ch : mvcc.Change), r < log.length ∧ (log.getD r [])[i]? = some ch ∧
      k = mvcc.revBytes ⟨W64 r, W64 i⟩ ch.isDel := by
  unfold mvcc.bucketMap at h
  rw [mvcc.lookup_foldl_insert] at h
  cases hf : (mvcc.bucketOf log).reverse.find? (fun p => decide (p.1 = k)) with
  | none =>
    rw [hf] at h
    have h0 : (GMap.empty : GMap GoString GoString) !! k = none := rfl
    rw [h0] at h; cases h
  | some p =>
    have hp := List.mem_reverse.1 (List.mem_of_find?_eq_some hf)
    have hk : p.1 = k := by simpa using List.find?_some hf
    unfold mvcc.bucketOf at hp
    rw [List.mem_flatten] at hp
    obtain ⟨l, hl, hp⟩ := hp
    rw [List.mem_map] at hl
    obtain ⟨⟨cs, r⟩, hz, rfl⟩ := hl
    rw [List.mem_zipIdx_iff_getElem?] at hz
    simp only at hz
    have hr : r < log.length := (List.getElem?_eq_some_iff.1 hz).1
    obtain ⟨i, ch, hi, hpi⟩ := mvcc.sc_mem_bucketOfRev hp
    refine ⟨r, i, ch, hr, ?_, by rw [← hk, hpi]⟩
    rw [List.getD_eq_getElem?_getD, hz]; exact hi

/-- A key a batch reads (`sc_entry`'s), of a revision at most `rev`, is in the job's space. -/
theorem mvcc.sc_mem (log ilog : mvcc.Log) (rev : w64) (hrev : sint.Z rev < log.length)
    (hilen : ilog.length < 2 ^ 63) (hpre : log <+: ilog ∨ ilog <+: log) {m' : mvcc.Bucket}
    (hsub : ∀ k v, m'.lookup k = some v → (mvcc.bucketMap ilog).lookup k = some v)
    {k v : GoString} (hkv : m'.lookup k = some v) (r : mvcc.Rev) (t : Bool)
    (hk : k = mvcc.revBytes r t) (hm : sint.Z r.main ≤ sint.Z rev) :
    mvcc.sc_space log (sint.Z rev) k := by
  obtain ⟨r', i, ch, hr', hi, hk'⟩ := mvcc.sc_bucketMap_key ilog (hsub _ _ hkv)
  rw [hk] at hk'
  obtain ⟨-, hrr⟩ := mvcc.revBytes_inj _ _ _ _ hk'
  have hmain : r.main = W64 r' := by rw [hrr]
  have hrz : (r' : Int) ≤ sint.Z rev := by
    rw [hmain] at hm
    have : sint.Z (W64 (r' : Int)) = r' := by word
    omega
  have hget : log.getD r' [] = ilog.getD r' [] := by
    have h1 : r' < log.length := by omega
    rcases hpre with ⟨t', rfl⟩ | ⟨t', rfl⟩
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hr']
  exact ⟨r', i, ch, hrz, by rw [hget]; exact hi, by rw [hk, ← hk']⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem mvcc.store.scheduleCompaction.wp_proof
    (h0 : mvcc.treeIndex.Compact.spec (GF := GF) (hG := hG))
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
  icases Hjob with ⟨#Hs, #Hstop, -, %Hcmp, #Hlb, %log, #Hcert, #Hnevc, %Hrev'⟩
  have Hrev : 0 ≤ sint.Z rev ∧ sint.Z rev < log.length := ⟨Hrev'.1, Hrev'.2.1⟩
  have Hnd : mvcc.NoDelPutAt log (sint.Z rev) := Hrev'.2.2
  ihave %Hsmall : ⌜mvcc.CompactSmall log (sint.Z rev)⌝ $$ []
  · iapply mvcc.CompactSmall_of_cert s γ log (sint.Z rev) $$ [Hs Hcert]
    iframe Hs Hcert
  ihave #Hs0 := Hs
  iunfold mvcc.isStore at Hs0
  iNamed Hs0
  icases mvcc.storeStop_fields s γ _ _ _ _ $$ [Hpin Hstop] with ⟨#Hb, #Hidx, #Hsched, #Hstopc, #Hstopch, #Hrstd⟩
  · iframe Hpin Hstop
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
    ⟨%cKeys, #HKeysG, #HKeys⟩, ⟨%gLast, #HLastG, #HLast⟩, -⟩
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
  icases HKeys with ⟨-, -, #HKeysAdd⟩
  iunfold gaugeSetSpec at HLast
  wp_apply time.wp_Since as %d1 -
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
  wp_apply h3 as %hv %Hhv
  (try wp_auto)
  wp_apply wp_slice_make2 (V := w8) (W64 17) as %lastS ⟨HlastS, HlastC⟩
  · ipureintro; decide
  (try wp_auto)
  -- the schema's `Key` bucket
  ihave #Hsch : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.schema $$ []
  · iPkgInit
  ihave Hsi : (go_etcd_io.etcd.server.v3.storage.schema.schemaInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hsch
  icases Hsi with ⟨-, -, -, ⟨%bK, #HKeyG, -⟩, -⟩
  ihave #Hc2 := Hcert
  iunfold mvcc.idxCert at Hc2
  icases Hc2 with ⟨-, %Hlwf, -⟩
  have Hrz : sint.Z rev < 2 ^ 63 - 1 := by have := Hrev.2; have := Hlwf.2.1; omega
  irename «end» => endP
  -- the batches
  -- `D`: the keys deleted so far (item 8): distinct keys of the job's space, below the cursor
  ihave HI : iprop(∃ (lst : GoSlice) (bs : List w8) (kc : w64) (hv' : kvHasher) (D : List GoString),
      "last" ∷ last_ptr ↦ lst ∗ "HlastS" ∷ lst ↦* bs ∗ "HlastC" ∷ ownSliceCap w8 lst (DFrac.own 1) ∗
      "%Hbs" ∷ ⌜bs.length = 17⌝ ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "h" ∷ (h_ptr ↦ hv' ∗ ⌜mvcc.kvHasherOk hv'⌝) ∗
      "%HD" ∷ ⌜sint.Z kc = D.length ∧ D.Nodup ∧
        ∀ k ∈ D, mvcc.sc_space log (sint.Z rev) k ∧ go.GoStringLt k bs⌝)
    $$ [last HlastS HlastC keyCompactions h]
  · iexists lastS, _, W64 0, hv, []
    simp only [named]
    iframe
    ipureintro; simp [Hhv]
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
  icases HW with ⟨%ilog, HW⟩
  iNamedSuffix HW "W"
  ihave #HcW' := HcertW
  ihave %Hpre : ⌜log <+: ilog ∨ ilog <+: log⌝ $$ []
  · iapply mvcc.idxCert_prefix $$ [Hcert HcertW]
    iframe Hcert HcertW
  iunfold mvcc.idxCert at HcW'
  icases HcW' with ⟨-, %HilWf, -⟩
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
  have HLsrt : (L.map Prod.fst).Pairwise go.GoStringLt := by
    rw [← hL]
    exact (((mvcc.bucketRange_eq_iff _ _ _ _).1 rfl).1).sublist
      (List.Sublist.map _ (List.take_sublist _ _))
  have HLmem : ∀ p ∈ L, m'.lookup p.1 = some p.2 ∧ go.GoStringLe bs p.1 := by
    intro p hp
    rw [← hL] at hp
    have := (((mvcc.bucketRange_eq_iff m' bs _ _).1 rfl).2 p.1 p.2).1
      (by simpa using List.mem_of_mem_take hp)
    exact ⟨this.1, this.2.1⟩
  have Hlt_le : ∀ {a b c : GoString}, go.GoStringLt a b → go.GoStringLe b c → go.GoStringLt a c := by
    intro a b c h1 h2
    rcases h2 with rfl | h2
    · exact h1
    · exact go.goStringLt_trans h1 h2
  iunfold mvcc.pairVals at Hpv
  icases Hpv with ⟨%kss, %vss, #Hks, #Hvs, %Hlens, #Hel⟩
  ihave %Hvl := ownSlice_len _ _ _ $$ Hvs
  ihave %Hkl := ownSlice_len _ _ _ $$ Hks
  ihave IH : iprop(∃ (n k kc : w64) (hv : kvHasher) (rv : Revision) (D : List GoString),
      "i" ∷ i_ptr ↦ n ∗ "Higo" ∷ igo ↦ k ∗ "keyCompactions" ∷ keyCompactions_ptr ↦ kc ∗
      "h" ∷ (h_ptr ↦ hv ∗ ⌜mvcc.kvHasherOk hv⌝) ∗ "rev" ∷ rev_ptr ↦ rv ∗ "Hlocked" ∷ Locked [] ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ L.length⌝ ∗
      "%HD" ∷ ⌜sint.Z kc = D.length ∧ D.Nodup ∧ (∀ k ∈ D, mvcc.sc_space log (sint.Z rev) k) ∧
        (∀ k ∈ D, ∀ j (hj : j < L.length), sint.nat n ≤ j → go.GoStringLt k (L[j]).1) ∧
        (sint.Z n = 0 ∨ ∀ k ∈ D, go.GoStringLt k
          (mvcc.revBytes (mvcc.revOf ⟨rv.Main', rv.Sub' + W64 1⟩) false))⌝)
    $$ [i Higo keyCompactions h rev Hlocked]
  · iexists W64 0, _, _, _, _, D
    simp only [named]
    iframe
    ipureintro
    refine ⟨⟨by decide, by simp⟩, HD.1, HD.2.1, fun k hk => (HD.2.2 k hk).1, ?_, Or.inl (by decide)⟩
    intro k hk j hj _
    exact Hlt_le (HD.2.2 k hk).2 (HLmem _ (List.getElem_mem hj)).2
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
    obtain ⟨HnL, HeL⟩ := List.getElem?_eq_some_iff.1 He
    have Henotin : e.1 ∉ D := fun hm =>
      go.goStringLt_irrefl _ (by have := HD.2.2.2.1 e.1 hm (sint.nat n) HnL (Nat.le_refl _); rwa [HeL] at this)
    have Hesp : mvcc.sc_space log (sint.Z rev) e.1 :=
      mvcc.sc_mem log ilog rev Hrev.2 HilWf.2.1 Hpre Hsub (HLmem e (List.mem_of_getElem? He)).1 r t
        Hk Hrm
    wp_join iprop(∃ (kc' : w64) (D' : List GoString), keyCompactions_ptr ↦ kc' ∗ Locked [] ∗
        keys_ptr ↦ ks ∗ igo ↦ n ∗ tx_ptr ↦ GoInterface.ok bt ∗
        ⌜sint.Z kc' = D'.length ∧ D'.Nodup ∧ (∀ k ∈ D', mvcc.sc_space log (sint.Z rev) k) ∧
          ∀ k ∈ D', k = e.1 ∨ k ∈ D⌝)
      with [keyCompactions Hlocked keys Higo tx]
      as ⟨%kc', %D', keyCompactions, Hlocked, keys, Higo, tx, %HD'⟩
    · iexists kc, D
      iframe
      ipureintro
      exact ⟨HD.1, HD.2.1, HD.2.2.1, fun k hk => Or.inr hk⟩
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
      -- the key deleted: one more in `D`, still fewer than the job's changes
      have Hnd' : (e.1 :: D).Nodup := List.nodup_cons.2 ⟨Henotin, HD.2.1⟩
      have Hsp' : ∀ k ∈ e.1 :: D, mvcc.sc_space log (sint.Z rev) k := by
        intro k hk
        rcases List.mem_cons.1 hk with rfl | hk
        · exact Hesp
        · exact HD.2.2.1 k hk
      have Hcnt := mvcc.sc_count log (sint.Z rev) _ Hnd' Hsp'
      have Hsm : ((log.take ((sint.Z rev).toNat + 1)).map List.length).sum < 2 ^ 62 := Hsmall
      rw [List.length_cons] at Hcnt
      have HDk := HD.1
      iexists kc + W64 1, e.1 :: D
      iframe
      ipureintro
      refine ⟨?_, Hnd', Hsp', fun k hk => ?_⟩
      · rw [List.length_cons]; word
      · rcases List.mem_cons.1 hk with rfl | hk
        · exact Or.inl rfl
        · exact Or.inr hk
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
    icases h with ⟨h, %Hhv⟩
    wp_apply (h5 h_ptr hv keep (DFrac.own 1) A ksl vsl e.1 e.2 DFrac.discard DFrac.discard)
      $$ [$h $Hkeep] as ⟨⟨%hv2, h⟩, Hkeep, -, -⟩
    · iframe #
      ipureintro
      exact ⟨Hhv, r, _, Hkb, by cases t <;> simp, Hr0, Hs0⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists n + W64 1, n, kc', hv2, mvcc.revVal r, D'
    simp only [named]
    iframe
    ipureintro
    have Hn1 : sint.nat (n + W64 1) = sint.nat n + 1 := by word
    have Hsrt := List.pairwise_iff_getElem.1 HLsrt
    have Hnext : ∀ j (hj : j < L.length), sint.nat n < j → go.GoStringLt e.1 (L[j]).1 := by
      intro j hj hnj
      have := Hsrt (sint.nat n) j (by simpa using HnL) (by simpa using hj) hnj
      simpa [HeL] using this
    have Hsucc : go.GoStringLt e.1
        (mvcc.revBytes (mvcc.revOf ⟨(mvcc.revVal r).Main', (mvcc.revVal r).Sub' + W64 1⟩) false) := by
      rw [Hk]
      apply mvcc.RevOrder.revBytes_lt
      right
      simp only [mvcc.revOf, mvcc.revVal]
      refine ⟨?_, ?_⟩ <;> first | trivial | rfl | word
    refine ⟨⟨by word, by word⟩, HD'.1, HD'.2.1, HD'.2.2.1, ?_, Or.inr ?_⟩
    · intro k hk j hj hnj
      rcases HD'.2.2.2 k hk with rfl | hk
      · exact Hnext j hj (by omega)
      · exact HD.2.2.2.1 k hk j hj (by omega)
    · intro k hk
      rcases HD'.2.2.2 k hk with rfl | hk
      · exact Hsucc
      · exact go.goStringLt_trans
          (by have := HD.2.2.2.1 k hk (sint.nat n) HnL (Nat.le_refl _); rwa [HeL] at this) Hsucc
  -- the batch read: short (the last), or full
  wp_if_destruct
  · -- the last batch: `finishedCompactRev = rev`, the compaction finished
    (try wp_auto)
    wp_bind (App (App (Val (@! go_etcd_io.etcd.server.v3.storage.mvcc.UnsafeSetFinishedCompact))
      (Val #(GoInterface.ok bt))) (Val #rev))
    iapply (h6 bt (mvcc.bucketView γ) (mvcc.delKey γ) (mvcc.writerRes s γ) Dep Locked Ph (mvcc.hookFn γ) [] rev
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
    iapply HUnl0 $$ [Hlocked HwkW HwvW HbvW Hmeta Hfin HP]
    · iframe Hlocked HP
      iunfold mvcc.writerRes
      iexists ilog
      simp only [named]
      iframe
      iframe #
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
    wp_apply time.wp_Since as %d2 -
    (try wp_auto)
    wp_apply HPause
    (try wp_auto)
    icases h with ⟨h, %Hhv⟩
    wp_apply h7 h_ptr hv $$ [$h] as %hash h
    · ipureintro; exact Hhv
    (try wp_auto)
    wp_apply HSize as %sz -
    wp_apply HSizeU as %szu -
    (try wp_auto)
    wp_apply h8 as %f0 -
    (try wp_auto)
    wp_apply time.wp_Since as %d3 -
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
    have hkc0 : 0 ≤ sint.Z kc := by have := HD.1; omega
    ihave #HKA := HKeysAdd $$ %kc %hkc0
    wp_apply HKA
    (try wp_auto)
    wp_apply time.wp_Since as %d4 -
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
  iapply HUnl0 $$ [Hlocked HwkW HwvW HbvW HcresW HP]
  · iframe Hlocked HP
    iunfold mvcc.writerRes
    iexists ilog
    simp only [named]
    iframe
    iframe #
    ipureintro; exact HneW
  inext
  iintro -
  (try wp_auto)
  wp_apply (h15 _ lst bs (Or.inl Hbs)) $$ [$HlastS $HlastC] as %lst2 ⟨HlastS, HlastC⟩
  (try wp_auto)
  wp_apply HForce $$ []
  · isplitl [] <;> itrivial
  (try wp_auto)
  wp_apply time.wp_Since as %d5 -
  (try wp_auto)
  wp_apply HPause
  (try wp_auto)
  wp_apply +noauto time.wp_After as %tch %γt #Hbag
  wp_auto_lc 2
  ihave #Hstc := Hstopc
  ihave #Hstcc := Hstopch
  iunfold mvcc.isStopChan at Hstcc
  icases Hstcc with ⟨%γs, #Hstcc⟩
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
    have HDk := HD
    iexists lst2, _, kc, hv, D
    simp only [named]
    iframe
    ipureintro
    refine ⟨by rw [List.length_append, mvcc.revBytes_length]; simp [Hbs], HD.1, HD.2.1,
      fun k hk => ⟨HD.2.2.1 k hk, ?_⟩⟩
    rw [List.drop_eq_nil_of_le (by omega), List.append_nil]
    rcases HD.2.2.2.2 with h0 | hlt
    · exfalso
      clear HDk
      exact absurd h0 (by omega)
    · exact hlt k hk
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
    have hkc0 : 0 ≤ sint.Z kc := by have := HD.1; omega
    ihave #HKA := HKeysAdd $$ %kc %hkc0
    wp_apply HKA
    (try wp_auto)
    wp_apply time.wp_Since as %d4 -
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

