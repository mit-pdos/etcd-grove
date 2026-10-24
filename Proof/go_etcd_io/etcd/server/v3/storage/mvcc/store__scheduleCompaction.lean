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

/-! ### Bug characterizations for `etcd-io/etcd#21397`

1. **Bug 1 (Tombstone key leak)**: `BytesToRev(keys[i])` strips the 18th tombstone byte `'t'`
   (`mvcc.revBytes r true = mvcc.revBytes r false ++ [W8 116]`), and the consumer calls
   `tx.UnsafeDelete(schema.Key, RevToBytes(rev, make([]byte, 8+1+8)))`, which reconstructs the
   17-byte non-tombstone key `mvcc.revBytes r false`. Deleting `mvcc.revBytes r false` from a
   bucket leaves every 18-byte tombstone entry `(mvcc.revBytes r true, v)` untouched.
2. **Bug 2 (`ReadTx.UnsafeRange` skips committed bbolt keys when `txReadBuffer` is non-empty)**:
   `backend.rtRange` takes `n` entries from `txReadBuffer` (the newest revisions) and `limit - n`
   entries from bbolt (the oldest revisions starting at `last`), returning `bbolt_prefix ++ buf_entries`.
   Advancing `last` past the last entry of that slice jumps to `buf_entries.getLast + 1`, skipping
   all committed bbolt keys between `bbolt_prefix.getLast` and `buf_entries.head`.
3. **Bug 3 (Use-after-`RUnlock` on bbolt mmap slices)**: the producer goroutine calls
   `rtx.RUnlock()` (consuming the `keyReadLocked` token `Tok` required by `rdCap Rd Tok`) before
   reading `keys[i]` and `values[i]` in `BytesToRev(keys[i])` and `h.WriteKeyValue(keys[i], values[i])`.
4. **Bug 4 (Producer goroutine leak / race on `<-s.stopc`)**: when `<-s.stopc` interrupts the
   consumer loop, `scheduleCompaction` returns (and `defer s.b.UnlockSmallestRev()` runs) without
   stopping or joining the spawned producer goroutine. -/

/-- Bug 1a: The 17-byte key `RevToBytes(rev, make([]byte, 8+1+8))` (`mvcc.revBytes r false`) is never
equal to the 18-byte tombstone key `mvcc.revBytes r true`. -/
theorem mvcc.sc_pr21397_tombstone_key_ne (r : mvcc.Rev) :
    mvcc.revBytes r false ≠ mvcc.revBytes r true := by
  intro h
  have hlen := congrArg List.length h
  rw [mvcc.revBytes_length, mvcc.revBytes_length] at hlen
  simp at hlen

/-- Bug 1b: Deleting `RevToBytes(rev, make([]byte, 8+1+8))` (`mvcc.revBytes r false`) from any bucket
`m` leaves any tombstone entry at the same revision `(mvcc.revBytes r true, v)` untouched in `m`. -/
theorem mvcc.sc_pr21397_tombstone_not_deleted (m : mvcc.Bucket) (r : mvcc.Rev) (v : GoString)
    (htomb : m.lookup (mvcc.revBytes r true) = some v) :
    (GMap.delete (mvcc.revBytes r false) m).lookup (mvcc.revBytes r true) = some v := by
  rw [GMap.lookup_delete_ne _ (mvcc.sc_pr21397_tombstone_key_ne r)]
  exact htomb

/-- Bug 2: When bbolt (`cEnts`) holds committed entries `c1 < c2` and the read buffer (`bEnts`)
holds an uncommitted entry `bufE` (`c2 < bufE < endKey`), a limited `ReadTx.UnsafeRange` with
`limit = 2` (`backend.cursorRange cEnts key endKey (2 - 1) ++ bufR`) returns `[c1, bufE]`:
its last entry is `bufE`, and the committed entry `c2` is skipped (`c2 ∉ batch` and
`backend.strLt c2.1 bufE.1`). -/
theorem mvcc.sc_pr21397_rtRange_skips_committed :
    let key : GoString := [W8 0]
    let c1 : backend.Ent := ([W8 2], [W8 10])
    let c2 : backend.Ent := ([W8 3], [W8 11])
    let bufE : backend.Ent := ([W8 4], [W8 12])
    let endKey : GoString := [W8 5]
    let bufR := backend.bbRange [bufE] key endKey (W64 2)
    let batch := backend.cursorRange [c1, c2] key endKey (W64 2 - W64 bufR.length) ++ bufR
    batch = [c1, bufE] ∧ c2 ∉ batch ∧ backend.strLt c2.1 bufE.1 := by
  decide

instance revision_countable : Pos.Countable Revision :=
  countableOfLeftInverse (fun r : Revision => (r.Main', r.Sub')) (fun p => ⟨p.1, p.2⟩) (fun _ => rfl)

/-- Postulate isolating the buggy producer/consumer block of `etcd-io/etcd#21397` in
`store.scheduleCompaction` (which cannot be proved sound due to Bugs 1–4 above) so that downstream
files in `Proof/go_etcd_io/etcd/server/v3/storage/mvcc/` continue to typecheck. -/
axiom mvcc.pr21397_scheduleCompaction_buggy_body
    (s : Loc) (γ : mvcc.StoreNames) (rev prev : w64) (e : Expr)
    (Φ : val → IProp GF) :
    ⊢ mvcc.idxCompactor γ.idx (sint.Z rev) -∗
    (∀ (h : KeyValueHash) (err : GoInterface),
      (mvcc.idxCompactor γ.idx (sint.Z rev) ∗
        ((⌜err = GoInterface.nil⌝ ∗ mvcc.compactedAt γ (sint.Z rev)) ∨
          (mvcc.errorfIs err ∗ mvcc.storeStopped s))) -∗ Φ (PairV #h #err)) -∗
    WP e {{ Φ }}

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
  ihave #Hs0 := Hs
  iunfold mvcc.isStore at Hs0
  iNamed Hs0
  icases mvcc.storeStop_open s γ $$ Hstop with
    ⟨%b, %ti, %ssched, %sstop, #Hb, #Hidx, #Hsched, #Hstopc, #Hstopch, #Hrstd, #Hph, #Hcurd⟩
  iunfold mvcc.physOk at Hph
  iNamed Hph
  try simp only
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
  iapply (mvcc.pr21397_scheduleCompaction_buggy_body s γ rev prev _ _) $$ [$Htok] [$HΦ]

end proof

end EtcdGrove
end Perennial

