/- Lean-first (no Rocq counterpart). The proof of `db.commit(m, v)`'s crash-aware spec
(`DB.commit.specCrash`): `DB__commit.lean`'s, step by step, over the crash invariant of the file.
The writer holds its idle state `⟨m, bs, 8192, 4096 * hwm, .idle⟩` (`writerFileC`); each file
operation is its crash-aware spec, whose obligations are, for the states it may pass through:
- `Truncate`, its `Sync` and the data page's `WriteAt` and `Fdatasync`: `commitClean` (the meta
  pages and the current root page untouched, `commitClean_of_prefix`);
- the meta page's `WriteAt` and a failed `Fdatasync` of it: `commitMetaSt` (`commitMetaSt_of`
  after the data page's sync, which keeps the clean meta pages among the durable bytes known, and
  `commitMetaSt_wreach`), with `cacheOk` of the slot written (`cacheOk_wreach`);
- a successful `Fdatasync` of the meta page: `commitClean` at the new meta pages, whose root page
  is the data page (`bootOk` of it is the spec's premise).
Then `cs_freeze` freezes the data page (its `pageIs` and its cells' agreement come from its
discarded copy). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commitCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__commit
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__mmapCrash
public import Proof.os.CrashStSpec

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-! ### Lists -/

theorem take_drop_congr {α : Type} {l l' : List α} {N a n : Nat} (h : ∀ k < N, l'[k]? = l[k]?)
    (han : a + n ≤ N) : (l'.drop a).take n = (l.drop a).take n := by
  apply List.ext_getElem?; intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · exact h _ (by omega)
  · rfl

theorem take_congr' {α : Type} {l l' : List α} {N n : Nat} (h : ∀ k < N, l'[k]? = l[k]?)
    (hn : n ≤ N) : l'.take n = l.take n := by
  have := take_drop_congr (a := 0) h (by omega : 0 + n ≤ N); simpa using this

/-- A list in three segments, `[0, a)`, `[a, b)`, `[b, ...)`. -/
theorem split3_eq {α : Type} (l : List α) (a b : Nat) (hab : a ≤ b) :
    l.take a ++ ((l.drop a).take (b - a) ++ l.drop b) = l := by
  rw [show l.drop b = (l.drop a).drop (b - a) by rw [List.drop_drop]; congr 1; omega,
    List.take_append_drop, List.take_append_drop]

theorem split3_prefix {α : Type} (l X : List α) (a b k : Nat) (hab : a ≤ b) (hb : b ≤ l.length)
    (hk : k < b) : (l.take a ++ ((l.drop a).take (b - a) ++ X))[k]? = l[k]? := by
  have hl : (l.take a ++ (l.drop a).take (b - a)).length = b := by
    simp only [List.length_append, List.length_take, List.length_drop]; omega
  have e : l.take a ++ ((l.drop a).take (b - a) ++ X) =
      (l.take a ++ (l.drop a).take (b - a)) ++ X := by simp
  have e2 : l = (l.take a ++ (l.drop a).take (b - a)) ++ l.drop b := by
    rw [List.append_assoc, split3_eq l a b hab]
  generalize hA : l.take a ++ (l.drop a).take (b - a) = A at e e2 hl
  rw [e]
  conv => rhs; rw [e2]
  rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

theorem split3_length {α : Type} (l X : List α) (a b : Nat) (hab : a ≤ b) (hb : b ≤ l.length) :
    (l.take a ++ ((l.drop a).take (b - a) ++ X)).length = b + X.length := by
  simp only [List.length_append, List.length_take, List.length_drop]; omega

theorem syncedBytes_length (m : OsMeta) (xs : List (w8 × Bool)) :
    (syncedBytes m xs).length = xs.length := by
  unfold syncedBytes; split <;> simp

theorem durOverlay_of_some : ∀ {a b : List (Option w8)} {i : Nat} {d : w8},
    b[i]? = some (some d) → (durOverlay a b)[i]? = some (some d)
  | _, [], i, d, h => by simp at h
  | [], y :: b, i, d, h => by simpa [durOverlay] using h
  | x :: a, y :: b, 0, d, h => by
      simp only [durOverlay, List.getElem?_cons_zero, Option.some.injEq] at h ⊢
      subst h; rfl
  | x :: a, y :: b, i + 1, d, h => by
      simp only [durOverlay, List.getElem?_cons_succ] at h ⊢
      exact durOverlay_of_some h

/-- A sync keeping the bytes `H` from 0 knows them as durable. -/
theorem syncedKeep_dur (m : OsMeta) (lo : Nat) (xs H : List (w8 × Bool)) (k : Nat)
    (hk : k < H.length) : (m.syncedKeep lo xs 0 H).dur[k]? = some (some H[k].1) := by
  apply durOverlay_of_some
  simp [durOf, List.getElem?_eq_getElem hk]

/-! ### `commitClean` -/

/-- `commitClean` of a state whose bytes below the high water mark are the same. -/
theorem commitClean_of_prefix {m m' : OsMeta} {bs bs' : List (w8 × Bool)} (h : commitClean m bs)
    (hpre : ∀ k < 4096 * curPgid ((bs.map Prod.fst).take 8192), bs'[k]? = bs[k]?)
    (hhi : m'.hi ≤ 2 ^ 30) (hlo : 4 * 4096 ≤ m'.lo)
    (hpg : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m'.lo) : commitClean m' bs' := by
  have hok := h.ok
  obtain ⟨-, -, hr2, hrp, -⟩ := hok
  have hpre' : ∀ k < 4096 * curPgid ((bs.map Prod.fst).take 8192),
      (bs'.map Prod.fst)[k]? = (bs.map Prod.fst)[k]? := by
    intro k hk; rw [List.getElem?_map, List.getElem?_map, hpre k hk]
  have ht : (bs'.map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 :=
    take_congr' hpre' (by omega)
  refine ⟨hhi, hlo, by rw [ht]; exact h.ok, by rw [ht]; exact h.slot, by rw [ht]; exact hpg, ?_,
    fun k hk => by rw [hpre k (by omega)]; exact h.metas k hk, fun k hk => ?_⟩
  · rw [ht, take_drop_congr hpre' (by omega)]; exact h.boot
  · rw [ht, hpre _ (by omega)]; exact h.root k hk

theorem commitClean_hwm {m : OsMeta} {bs : List (w8 × Bool)} (h : commitClean m bs) :
    2 ≤ curRoot ((bs.map Prod.fst).take 8192) ∧
      curRoot ((bs.map Prod.fst).take 8192) < curPgid ((bs.map Prod.fst).take 8192) :=
  ⟨h.ok.2.2.1, h.ok.2.2.2.1⟩

/-- The states a growing `Truncate` reaches keep `commitClean`. -/
theorem treach_commitClean {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {sz : Nat}
    (h : commitClean m bs) (hl : bs.length = m.size) (hsz : sz ≤ 2 ^ 30) (hg : m.size ≤ sz)
    (hpg : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ bs.length)
    (hR : TReach m bs sz m' bs') : commitClean m' bs' ∧ bs'.length = m'.size := by
  have hhi := h.hi
  cases hR with
  | refl => exact ⟨h, hl⟩
  | ft =>
    exact ⟨commitClean_of_prefix h (fun _ _ => rfl) (by simp only [ftMeta]; omega) h.lo h.pg, hl⟩
  | grown =>
    refine ⟨commitClean_of_prefix h (fun k hk => List.getElem?_append_left (by omega))
      (by simp only [OsMeta.grown]; omega) h.lo h.pg, ?_⟩
    simp only [OsMeta.grown, List.length_append, List.length_replicate]
    omega

/-- **`Truncate`'s obligation** (`os.File.Truncate.specCrashS`). -/
theorem trunc_obl {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)} {sz : Nat}
    (h : commitClean m bs) (hl : bs.length = m.size) (hsz : sz ≤ 2 ^ 30) (hg : m.size ≤ sz)
    (hpg : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ bs.length) (fa fb : Nat) :
    ∀ m' bs', TReach m bs sz m' bs' →
      dbOk p (some ⟨m', bs', fa, fb, .idle⟩) ∧ ∀ t, dbOk p (some ⟨m', bs', fa, fb, .trunc t sz⟩) := by
  intro m' bs' hR
  obtain ⟨hc, hl'⟩ := treach_commitClean h hl hsz hg hpg hR
  exact ⟨commitClean_okS ⟨m', bs', fa, fb, .idle⟩ hl' rfl hc,
    fun t => commitClean_trunc_okS ⟨m', bs', fa, fb, .trunc t sz⟩ hl' rfl hc hsz⟩


/-- Bytes kept below `fb` (`H ++ F`), the rest replaced. -/
theorem keep_prefix {α : Type} (H F T X : List α) (k : Nat) (hk : k < H.length + F.length) :
    (H ++ (F ++ X))[k]? = (H ++ (F ++ T))[k]? := by
  rw [← List.append_assoc, ← List.append_assoc]
  generalize hA : H ++ F = A
  have : A.length = H.length + F.length := by rw [← hA, List.length_append]
  rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

/-- **A successful sync keeping the meta pages** (`csSynced false`, `H` the meta pages, `F` the
frozen pages, `T` the rest) keeps `commitClean`, with the size since the last sync the size. -/
theorem synced_commitClean {m : OsMeta} {H F T : List (w8 × Bool)} {hwm : Nat}
    (h : commitClean m (H ++ (F ++ T))) (hl : (H ++ (F ++ T)).length = m.size)
    (hpg : curPgid (((H ++ (F ++ T)).map Prod.fst).take 8192) = hwm)
    (hHF : H.length + F.length = 4096 * hwm) (h30 : m.size ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size) :
    commitClean (m.syncedKeep (4096 * hwm) T 0 H) (H ++ (F ++ syncedBytes m T)) ∧
      (H ++ (F ++ syncedBytes m T)).length = (m.syncedKeep (4096 * hwm) T 0 H).size := by
  have hl' : (H ++ (F ++ syncedBytes m T)).length = m.size := by
    rw [List.length_append, List.length_append, syncedBytes_length]
    rw [List.length_append, List.length_append] at hl; omega
  refine ⟨commitClean_of_prefix h (fun k hk => keep_prefix H F T _ k (by omega))
    (by show m.size ≤ _; exact h30) (by show _ ≤ m.size; exact h16)
    (by show _ ≤ m.size; rw [hpg]; simp only [List.length_append] at hl; omega), hl'⟩

/-- A window of a list unchanged. -/
theorem window_congr {α : Type} {l l' : List α} {a n : Nat}
    (h : ∀ k, a ≤ k → k < a + n → l'[k]? = l[k]?) : (l'.drop a).take n = (l.drop a).take n := by
  apply List.ext_getElem?; intro k
  simp only [List.getElem?_take, List.getElem?_drop]
  split
  · exact h _ (by omega) (by omega)
  · rfl

/-- The meta in slot `i` of `L`, whose slot holds the meta bytes of the page `D`. -/
theorem fileMeta_of_window {L D : List w8} {i : Nat}
    (h : ∀ k < 64, L[4096 * i + 16 + k]? = D[16 + k]?) : fileMeta L i = pageMeta D := by
  rw [fileMeta_slot]
  unfold pageMeta
  congr 1
  apply List.ext_getElem?; intro k
  by_cases hk : k < 64
  · rw [metaSlot_getElem? _ _ _ hk, h k hk, List.getElem?_take, if_pos hk, List.getElem?_drop]
  · rw [List.getElem?_eq_none (by rw [metaSlot_length]; omega), List.getElem?_take, if_neg hk]

/-- The page `D` written at page `i`: its slot is `D`'s meta. -/
theorem fileMeta_writeBytes (X D : List w8) (i : Nat) (hD : D.length = 4096) :
    fileMeta (writeBytes X (4096 * i) D) i = pageMeta D := by
  have hne : D ≠ [] := by intro h; simp [h] at hD
  refine fileMeta_of_window fun k hk => ?_
  rw [writeBytes_getElem? _ _ _ hne, if_neg (by omega), if_pos (by omega)]
  congr 1; omega

/-- The meta write, retried (at slot `1 - s`), keeps `commitMetaSt`. -/
theorem commitMetaSt_wreach {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {mp : List w8} {N : Meta}
    {s : Nat} {D : List w8} (h : commitMetaSt m bs mp N s) (hl : bs.length = m.size)
    (hD : D.length = 4096) (h8 : 8192 ≤ m.size)
    (hR : WReach m bs (4096 * (1 - s)) D m' bs') : commitMetaSt m' bs' mp N s := by
  have hN := hR.narrow hl
  obtain ⟨hdur, hdurHi⟩ := wreach_dur hR
  have hs2 := h.s2
  have hout : ∀ k, (k < 4096 * (1 - s) ∨ 4096 * (1 - s) + 4096 ≤ k) → bs'[k]? = bs[k]? := by
    rintro k (hk | hk)
    · exact hN.pre k (by unfold cfLo; omega)
    · exact hN.suf (by omega) k (by omega)
  have hpage : ∀ r, 2 ≤ r → ((bs'.map Prod.fst).drop (4096 * r)).take 4096 =
      ((bs.map Prod.fst).drop (4096 * r)).take 4096 := fun r hr =>
    window_congr fun k h1 _ => by
      rw [List.getElem?_map, List.getElem?_map, hout k (.inr (by omega))]
  have hR2 := h.ok.2.2.1
  have hNR := h.nRoot
  have hhi := h.hi
  have hhi' := hN.hi
  refine ⟨hs2, h.sTx, by omega, by rw [hN.lo]; exact h.lo, h.ok, h.slot, by rw [hN.lo]; exact h.pg,
    by rw [hpage _ hR2]; exact h.boot, fun k hk => by rw [hout _ (.inr (by omega))]; exact h.root k hk,
    fun k hk => by rw [hout _ (by omega)]; exact h.metaS k hk, h.nValid, h.nTx, h.nTxS, hNR,
    h.nRootPg, h.nPg, by rw [hN.lo]; exact h.nPgLo, by rw [hpage _ hNR]; exact h.nBoot,
    fun k hk => by rw [hout _ (.inr (by omega))]; exact h.nPage k hk, durOk_congr hdur hdurHi h.dur⟩

/-- `commitMetaSt` does not look at the mappings or `ok`. -/
theorem commitMetaSt_meta {m m' : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta}
    {s : Nat} (h : commitMetaSt m bs mp N s) (hhi : m'.hi = m.hi) (hlo : m'.lo = m.lo)
    (hdur : m'.dur = m.dur) (hdh : m'.durHi = m.durHi) : commitMetaSt m' bs mp N s :=
  ⟨h.s2, h.sTx, hhi ▸ h.hi, hlo ▸ h.lo, h.ok, h.slot, hlo ▸ h.pg, h.boot, h.root, h.metaS, h.nValid,
    h.nTx, h.nTxS, h.nRoot, h.nRootPg, h.nPg, hlo ▸ h.nPgLo, h.nBoot, h.nPage,
    durOk_congr hdur hdh h.dur⟩

/-- What the meta write (the page `D`, whose meta is `N`, at slot `1 - s`) reaches, from a state
whose meta pages are clean: `commitMetaSt`, and the page cache's slot `1 - s` the old or the new
meta. -/
theorem metaW_reach {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {mp : List w8} {N : Meta}
    {s : Nat} {D : List w8} (h : commitMetaSt m bs mp N s) (hl : bs.length = m.size)
    (hD : D.length = 4096) (h8 : 8192 ≤ m.size) (hcl : ∀ k < 8192, ∃ b, bs[k]? = some (b, true))
    (hw : pageMeta D = N) (hR : WReach m bs (4096 * (1 - s)) D m' bs') :
    commitMetaSt m' bs' mp N s ∧ cacheOk bs' (1 - s) (fun X => X = fileMeta mp (1 - s) ∨ X = N) ∧
      bs'.length = m'.size := by
  have hs2 := h.s2
  refine ⟨commitMetaSt_wreach h hl hD h8 hR, ?_, (hR.narrow hl).len⟩
  refine cacheOk_wreach hR hl (by omega) (by omega) (fun k hk x hx => ?_) (fun L hL _ => .inr ?_)
  · obtain ⟨b, hb⟩ := hcl (4096 * (1 - s) + 16 + k) (by omega)
    rw [hb] at hx; cases hx; rfl
  · rw [← hw]
    refine fileMeta_of_window fun k hk => ?_
    rw [hL k hk, List.getD_eq_getElem?_getD, show 4096 * (1 - s) + 16 + k - 4096 * (1 - s) = 16 + k by omega,
      List.getElem?_eq_getElem (by omega)]
    rfl

/-- **The meta write's obligation** (`os.File.WriteAt.specCrashS`). -/
theorem metaW_obl {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta}
    {s : Nat} {D : List w8} (h : commitMetaSt m bs mp N s) (hl : bs.length = m.size)
    (hD : D.length = 4096) (h8 : 8192 ≤ m.size) (hcl : ∀ k < 8192, ∃ b, bs[k]? = some (b, true))
    (hw : pageMeta D = N) (fa fb : Nat) :
    ∀ m' bs', WReach m bs (4096 * (1 - s)) D m' bs' →
      dbOk p (some ⟨m', bs', fa, fb, .idle⟩) ∧
      ∀ t, dbOk p (some ⟨m', bs', fa, fb, .write t (4096 * (1 - s)) D⟩) := by
  intro m' bs' hR
  obtain ⟨hM, hc, hl'⟩ := metaW_reach h hl hD h8 hcl hw hR
  have hs2 := h.s2
  refine ⟨commitMetaIdle_okS ⟨m', bs', fa, fb, .idle⟩ hl' rfl hM hc, fun t =>
    commitMetaW_okS ⟨m', bs', fa, fb, .write t (4096 * (1 - s)) D⟩ hl' rfl hM hD (by omega)
      h.ok.2.2.1 hc ?_⟩
  rw [fileMeta_writeBytes _ _ _ hD, hw]

end pure

section pure2
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-! ### `commitMetaSt` -/

/-- After the data page's sync: what the meta write needs (`commitMetaSt`), from `commitClean`,
the data page at the high water mark (clean), and the meta pages durable. -/
theorem commitMetaSt_of {m : OsMeta} {bs : List (w8 × Bool)} {v : w64} (h : commitClean m bs)
    (ht : (curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat + 1 < 2 ^ 64)
    (hb : (curPgid ((bs.map Prod.fst).take 8192) + 2) * 4096 ≤ 2 ^ 30)
    (hlo : 4096 * (curPgid ((bs.map Prod.fst).take 8192) + 1) ≤ m.lo)
    (hpage : ∀ k < 4096, bs[4096 * curPgid ((bs.map Prod.fst).take 8192) + k]? =
      (dataPage (curMeta ((bs.map Prod.fst).take 8192)).pgid' v)[k]?.map (·, true))
    (hboot : bootOk ((curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat + 1) (some v))
    (hdur : ∀ k < 8192, ∃ b, bs[k]? = some (b, true) ∧ m.dur[k]? = some (some b)) :
    commitMetaSt m bs ((bs.map Prod.fst).take 8192)
      (commitOf (curMeta ((bs.map Prod.fst).take 8192)))
      ((curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat % 2) := by
  have hhi := h.hi
  have hlo4 := h.lo
  have hok := h.ok
  have hslot := h.slot
  have hpg := h.pg
  have hboot0 := h.boot
  have hroot := h.root
  have hmpk : ∀ j < 8192, ((bs.map Prod.fst).take 8192)[j]? = (bs[j]?).map Prod.fst := by
    intro j hj; rw [List.getElem?_take, if_pos hj, List.getElem?_map]
  generalize hmp : (bs.map Prod.fst).take 8192 = mp at *
  obtain ⟨hl8, hv, hr2, hrp, hbd⟩ := hok
  have hcv := curMeta_valid mp hv
  have hpgv : (curMeta mp).pgid'.toNat = curPgid mp := rfl
  have hp64 : (curMeta mp).pgid'.toNat + 1 < 2 ^ 64 := by rw [hpgv]; omega
  obtain ⟨hN, htx, hnpg, hrt⟩ := commitOf_facts (curMeta mp) hcv ht hp64
  have hrtN : (commitOf (curMeta mp)).root'.root'.toNat = curPgid mp := by rw [hrt]; rfl
  have hdp := dataPage_length (curMeta mp).pgid' v
  have hpgB : ((bs.map Prod.fst).drop (4096 * curPgid mp)).take 4096 =
      dataPage (curMeta mp).pgid' v := by
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map]
    split
    · rw [hpage k ‹_›, Option.map_map]
      cases (dataPage (curMeta mp).pgid' v)[k]? <;> rfl
    · rw [List.getElem?_eq_none (by omega)]
  have hs2 : (curMeta mp).txid'.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
  have hnum : 2 ≤ (commitOf (curMeta mp)).root'.root'.toNat ∧
      (commitOf (curMeta mp)).root'.root'.toNat < (commitOf (curMeta mp)).pgid'.toNat ∧
      ((commitOf (curMeta mp)).pgid'.toNat + 1) * 4096 ≤ 2 ^ 30 ∧
      4096 * (commitOf (curMeta mp)).pgid'.toNat ≤ m.lo := by
    rw [hrtN, hnpg, hpgv]
    generalize curPgid mp = x at hb hlo hrp
    omega
  refine ⟨hs2, rfl, hhi, hlo4, ⟨hl8, hv, hr2, hrp, hbd⟩, hslot, hpg, hboot0, hroot, ?_, hN,
    ?_, htx, hnum.1, hnum.2.1, hnum.2.2.1, hnum.2.2.2,
    ?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨b, hb', -⟩ := hdur (4096 * ((curMeta mp).txid'.toNat % 2) + 16 + k) (by omega)
    exact ⟨b, by rw [hmpk _ (by omega), hb']; rfl, hb'⟩
  · show ((curMeta mp).txid'.toNat : Int) < ((commitOf (curMeta mp)).txid'.toNat : Int)
    rw [htx]; omega
  · rw [htx, hrtN, hpgB, dataPage_val]; exact hboot
  · intro k hk
    rw [hrtN, hpage k hk, List.getElem?_eq_getElem (by omega)]
    exact ⟨_, rfl⟩
  · refine .inr ⟨mp, fun k hk => ?_, fun _ => .inl rfl⟩
    obtain ⟨b, hb', hd⟩ := hdur (4096 * (1 - (curMeta mp).txid'.toNat % 2) + 16 + k) (by omega)
    exact ⟨b, by rw [hmpk _ (by omega), hb']; rfl, hd⟩

end pure2


end bboltfs
end EtcdGrove
end Perennial
