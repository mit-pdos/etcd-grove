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


/-- What the data page's write (at the high water mark or past it, inside the file) reaches:
`commitClean`. -/
theorem dataW_reach {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {off : Nat} {D : List w8}
    (h : commitClean m bs) (hl : bs.length = m.size)
    (hoff : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ off) (hoffs : off ≤ m.size)
    (hD : off + D.length ≤ 2 ^ 30) (hR : WReach m bs off D m' bs') :
    commitClean m' bs' ∧ Narrow m bs off D m' bs' := by
  have hN := hR.narrow hl
  have hhi := h.hi
  have hhi' := hN.hi
  refine ⟨commitClean_of_prefix h (fun k hk => hN.pre k (by unfold cfLo; omega)) (by omega)
    (by rw [hN.lo]; exact h.lo) (by rw [hN.lo]; exact h.pg), hN⟩

/-- **The data page's write's obligation** (`os.File.WriteAt.specCrashS`): it misses the meta
pages and the current root page. -/
theorem dataW_obl {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat} {D : List w8}
    (h : commitClean m bs) (hl : bs.length = m.size)
    (hoff : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ off) (hoffs : off ≤ m.size)
    (hD : off + D.length ≤ 2 ^ 30) (fa fb : Nat) :
    ∀ m' bs', WReach m bs off D m' bs' →
      dbOk p (some ⟨m', bs', fa, fb, .idle⟩) ∧ ∀ t, dbOk p (some ⟨m', bs', fa, fb, .write t off D⟩) := by
  intro m' bs' hR
  obtain ⟨hc, hN⟩ := dataW_reach h hl hoff hoffs hD hR
  have hpre' : ∀ k < 4096 * curPgid ((bs.map Prod.fst).take 8192),
      (bs'.map Prod.fst)[k]? = (bs.map Prod.fst)[k]? := by
    intro k hk; rw [List.getElem?_map, List.getElem?_map, hN.pre k (by unfold cfLo; omega)]
  have hw := commitClean_hwm h
  have ht : (bs'.map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 :=
    take_congr' hpre' (by omega)
  have hs := hN.size
  refine ⟨commitClean_okS ⟨m', bs', fa, fb, .idle⟩ hN.len rfl hc, fun t =>
    commitClean_write_okS ⟨m', bs', fa, fb, .write t off D⟩ hN.len rfl hc hD fun k hk => .inl ?_⟩
  show k < min off m'.size
  rw [ht] at hk
  omega

/-- **A successful sync of the meta pages** (`csSynced true`) after the meta write: `commitClean`
at the new meta pages `mp'`, whose root page `B` (clean) is `bootOk`. -/
theorem metaSynced_commitClean {m : OsMeta} {H F T : List (w8 × Bool)} {mp' B : List w8}
    (hok : m.ok = true) (hl : (H ++ (F ++ T)).length = m.size) (hH : H.length = 8192)
    (hmp : H.map Prod.fst = mp') (hmpok : metaPagesOk mp') (hslot : curInSlot mp')
    (hpg : 4096 * curPgid mp' ≤ m.size) (h30 : m.size ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size)
    (hB : B.length = 4096)
    (hpage : ∀ k < 4096, (H ++ (F ++ T))[4096 * curRoot mp' + k]? = B[k]?.map (·, true))
    (hboot : bootOk (curMeta mp').txid'.toNat (pageVal B)) :
    commitClean (m.synced 0 H) (syncedBytes m H ++ (F ++ T)) ∧
      (syncedBytes m H ++ (F ++ T)).length = (m.synced 0 H).size := by
  have hr2 := hmpok.2.2.1
  have hsH : syncedBytes m H = H.map (fun x => (x.1, true)) := by
    unfold syncedBytes; rw [if_pos hok]
  have hsl : (syncedBytes m H).length = 8192 := by rw [syncedBytes_length, hH]
  have hX : ((syncedBytes m H ++ (F ++ T)).map Prod.fst).take 8192 = mp' := by
    rw [List.map_append, List.take_append_of_le_length (by simp [hsl]),
      List.take_of_length_le (by simp [hsl]), hsH, List.map_map, ← hmp]; rfl
  have hhi : ∀ j, 8192 ≤ j → (syncedBytes m H ++ (F ++ T))[j]? = (H ++ (F ++ T))[j]? := by
    intro j hj
    rw [List.getElem?_append_right (l₁ := syncedBytes m H) (by omega),
      List.getElem?_append_right (l₁ := H) (by omega), hsl, hH]
  have hpB : (((syncedBytes m H ++ (F ++ T)).map Prod.fst).drop (4096 * curRoot mp')).take 4096 =
      B := by
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_take, List.getElem?_drop, List.getElem?_map]
    split
    · rw [hhi _ (by omega), hpage k ‹_›, Option.map_map]
      cases B[k]? <;> rfl
    · rw [List.getElem?_eq_none (by omega)]
  have hl' : (syncedBytes m H ++ (F ++ T)).length = m.size := by
    rw [List.length_append, hsl]; rw [List.length_append, hH] at hl; exact hl
  refine ⟨⟨by show m.size ≤ _; exact h30, by show _ ≤ m.size; exact h16, by rw [hX]; exact hmpok,
    by rw [hX]; exact hslot, by rw [hX]; exact hpg, by rw [hX, hpB]; exact hboot, fun k hk => ?_,
    fun k hk => ?_⟩, hl'⟩
  · rw [List.getElem?_append_left (by omega), hsH, List.getElem?_map,
      List.getElem?_eq_getElem (by omega)]
    exact ⟨_, rfl⟩
  · rw [hX, hhi _ (by omega), hpage k hk, List.getElem?_eq_getElem (by omega)]
    exact ⟨_, rfl⟩

/-- The meta pages of a state whose bytes below `N ≥ 8192` are the same. -/
theorem take8192_congr {l l' : List (w8 × Bool)} {N : Nat} (h : ∀ k < N, l'[k]? = l[k]?)
    (hN : 8192 ≤ N) : (l'.map Prod.fst).take 8192 = (l.map Prod.fst).take 8192 :=
  take_congr' (fun k hk => by rw [List.getElem?_map, List.getElem?_map, h k hk]) hN

/-- **A sync keeping the meta pages** (`csSynced false`) of a `commitClean` state: its premises
and the state it leaves. -/
theorem syncK_facts {m : OsMeta} {bs : List (w8 × Bool)} {hwm : Nat} (h : commitClean m bs)
    (hl : bs.length = m.size) (hpg : curPgid ((bs.map Prod.fst).take 8192) = hwm) (h2 : 2 ≤ hwm)
    (hsz : 4096 * hwm ≤ m.size) (h30 : m.size ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size) :
    (bs.take 8192).length = 8192 ∧
    8192 + ((bs.drop 8192).take (4096 * hwm - 8192)).length = 4096 * hwm ∧
    (∀ y ∈ bs.take 8192, y.2 = true) ∧
    commitClean (m.syncedKeep (4096 * hwm) (bs.drop (4096 * hwm)) 0 (bs.take 8192))
      (bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++
        syncedBytes m (bs.drop (4096 * hwm)))) ∧
    (bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++
        syncedBytes m (bs.drop (4096 * hwm)))).length = m.size ∧
    ((bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++
        syncedBytes m (bs.drop (4096 * hwm)))).map Prod.fst).take 8192 =
      (bs.map Prod.fst).take 8192 ∧
    (∀ k < 4096 * hwm, (bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++
        syncedBytes m (bs.drop (4096 * hwm))))[k]? = bs[k]?) := by
  have hH : (bs.take 8192).length = 8192 := by rw [List.length_take]; omega
  have hF : 8192 + ((bs.drop 8192).take (4096 * hwm - 8192)).length = 4096 * hwm := by
    rw [List.length_take, List.length_drop]; omega
  have e := split3_eq bs 8192 (4096 * hwm) (by omega)
  have hpre : ∀ k < 4096 * hwm, (bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++
      syncedBytes m (bs.drop (4096 * hwm))))[k]? = bs[k]? := fun k hk =>
    split3_prefix bs _ 8192 (4096 * hwm) k (by omega) (by omega) hk
  have hc' := h; rw [← e] at hc'
  have hl' := hl; rw [← e] at hl'
  obtain ⟨hcs, hls⟩ := synced_commitClean (m := m) (hwm := hwm) hc' hl' (by rw [e]; exact hpg)
    (by omega) h30 h16
  refine ⟨hH, hF, fun y hy => ?_, hcs, by rw [hls]; rfl, take8192_congr hpre (by omega), hpre⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  obtain ⟨b, hb⟩ := h.metas k (by omega)
  rw [List.getElem_take]
  rw [List.getElem?_eq_getElem (by omega), Option.some.injEq] at hb
  rw [hb]

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



section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

/-- The writer's idle state, its bytes in three segments: the meta pages, the frozen pages, the
rest (for `Sync`/`Fdatasync`). -/
theorem csOwn_split3 (p : GoString) (γc : GName) (m : OsMeta) (bs : List (w8 × Bool)) (hwm : Nat)
    (h2 : 2 ≤ hwm) :
    csOwn (GF := GF) p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩) ⊣⊢
      csOwn (GF := GF) p γc (some ⟨m, bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++
        bs.drop (4096 * hwm)), 8192, 4096 * hwm, .idle⟩) := by
  rw [split3_eq bs 8192 (4096 * hwm) (by omega)]
  exact .rfl

/-- `commit`'s error result, besides the error (see the spec). -/
def commitErrC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (t : Nat) :
    IProp GF :=
  iprop((∃ n', dbOwner (GF := GF) γ t n') ∗
    ∃ (mp' : List w8) (fl : Bool) (hwm : Nat) (st' : MapSt) (m' : OsMeta) (bs' : List (w8 × Bool)),
      writerStFC (GF := GF) γ γc db f fd p mp' fl hwm st' m' bs' ∗
      (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ)))

/-- `writerFileC` once failed asks less. -/
theorem writerFileC_fail (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)) :
    writerFileC (GF := GF) γc db f fd p mp fl hwm st m bs ⊢
      writerFileC (GF := GF) γc db f fd p mp true hwm st m bs := by
  unfold writerFileC
  iintro ⟨%fsz, Hfsz, Hdsz, Hf, Hfd, Hcs, %Hw⟩
  iexists fsz; iframe
  ipureintro; exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, fun h => by cases h⟩

/-- An error exit of `commit` while the handle is not yet failed. -/
theorem commitErrC_of (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString)
    (mp : List w8) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)) (t n : Nat) :
    dbOwner (GF := GF) γ t n ∗ writerStC (GF := GF) γ γc db f fd p mp false hwm st m bs ⊢
      commitErrC (GF := GF) γ γc db f fd p t := by
  iintro ⟨Hown, Hws⟩
  unfold commitErrC
  isplitl [Hown]
  · iexists n; iexact Hown
  iexists mp, false, hwm, st, m, bs
  isplitl
  · unfold writerStC writerStFC
    icases Hws with ⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, Hst⟩
    ihave Hw := writerFileC_fail γc db f fd p mp false hwm st m bs $$ Hw
    iframe
  · ileft; ipureintro; rfl

/-- The writer's cells, from its top part, the data page's and the rest. -/
theorem cells_rejoin (base : Loc) (hwm len : Nat) (hl : 4096 * hwm + 4096 ≤ len) :
    ((∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
        (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf)) ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ⊢
      writerCells (GF := GF) base hwm len := by
  iintro ⟨Hwc4, C1, C2⟩
  iapply (writerCells_top base hwm len).2
  iframe Hwc4
  obtain ⟨k, hk⟩ : ∃ k, len - 4096 * hwm - 4096 = k := ⟨_, rfl⟩
  rw [hk, show len - 4096 * hwm = 4096 + k by omega]
  iapply (cellsAny_append base (4096 * hwm) 4096 k)
  iframe C1 C2

/-- Failing the handle in `commit` (`meta_fail` with `metaRC`, no meta bytes). -/
theorem meta_failC (γ : DBNames) (db : Loc) (p : GoString) (base : Loc) (len : Nat) (γm : GName)
    (mp : List w8) (hwm : Nat) (mc : List w8) (hmc : mc.length = 128) (T : GMap Nat (Option w64))
    (x : Nat × Nat) (t n : Nat) (c : Bool) :
    mapInv (GF := GF) γ p base len γm ∗ ghostVar γm (1 : Qp).half () ∗
      ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗ ghostVar γ.cur (1 : Qp).half (mp, false, hwm) ∗
      ghostVar γ.out (1 : Qp).half.half true ∗ ghostVar γ.out (1 : Qp).half.half true ∗
      cellsB (GF := GF) base 16 (mc.take 64) ∗ cellsB (GF := GF) base 4112 (mc.drop 64) ∗
      db.[DB, go!"failed"] ↦ true ∗ monoNatAuthOwn γ.fail 1 0 ∗ ghostMapAuth γ.txs 1 T ∗
      ghostVar γ.own (1 : Qp).half x ∗ dbOwner (GF := GF) γ t n ∗ ghostVar γ.cls (1 : Qp).half c ⊢
      |={⊤}=> metaRC (GF := GF) γ db p ∗ dbFailed (GF := GF) γ ∗ dbOwner (GF := GF) γ t 0 ∗
        ghostVar γm (1 : Qp).half () ∗
        ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗ ghostVar γ.out (1 : Qp).half.half false := by
  iintro ⟨#Hinv, Htok, Hcur, Hcm, Ho1, Ho2, Hc0, Hc1, Hfl, Hfail, Hauth, Hown, Howner, Hcls⟩
  iunfold dbOwner at Howner
  imod ghostVar_update_halves (t, 0) γ.own _ _ $$ Howner Hown with ⟨Howner, Hown⟩
  imod fail_cur_inv γ p base len γm mp hwm $$ [Htok Hcur Hcm] with ⟨Htok, Hcur, Hcm⟩
  · iframe; iframe #
  imod metas_in γ p base len γm mp true hwm mc hmc (fun h => by cases h)
    $$ [Htok Hcur Ho1 Ho2 Hc0 Hc1] with ⟨Htok, Hcur, Ho1, Ho2⟩
  · iframe; iframe #
  imod mono_nat_own_update 1 (by omega) $$ Hfail with ⟨Hfail, Hlb⟩
  imodintro
  iframe Htok Hcur Ho1
  isplitr [Hlb Howner]
  · unfold metaRC
    iexists true, mp, hwm, c, T
    iframe
    dsimp only
    iframe Hfail
    iexists t; iexact Hown
  · unfold dbFailed dbOwner; iframe

/-- An error exit of `commit` once it failed the handle, with a mapping. -/
theorem dataErrTC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m : OsMeta) (bs : List (w8 × Bool))
    (fsz t n : Nat)
    (h : m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm + 4096 ≤ m.size ∧
      ∀ M : GMap Loc Nat, dbOk p (some ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩)) :
    dbOwner (GF := GF) γ t n ∗ dbFailed (GF := GF) γ ∗ ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ p base len γm ∗ hdrTail (GF := GF) base 0 ∗ hdrTail (GF := GF) base 1 ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
      csOwn (GF := GF) p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩) ⊢
      commitErrC (GF := GF) γ γc db f fd p t := by
  iintro ⟨Hown, #Hfailed, Hcur, Hmap, Hout, Hflds, Hcls, Htok, #Hinv, T0, T1, Hpc, Htop, Hfsz, Hdsz, Hf,
    Hfd, Hcs⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  ihave Hwc4 := (hdrTails base).2 $$ [T0 T1]
  · iframe T0 T1
  ihave Hwc := cells_rejoin base hwm len (by omega) $$ [Hwc4 Hpc Htop]
  · iframe Hwc4 Hpc Htop
  unfold commitErrC writerStFC writerFileC
  isplitl [Hown]
  · iexists n; iexact Hown
  iexists mp, true, hwm, some (base, len, γm), m, bs
  iframe Hcur Hmap Hout Hflds Hcls
  dsimp only [mapLen]
  isplitl [Hfsz Hdsz Hf Hfd Hcs Htok Hwc]
  · isplitl [Hfsz Hdsz Hf Hfd Hcs]
    · iexists fsz
      iframe
      ipureintro
      exact ⟨h5, by omega, h7, fun h => by cases h⟩
    · iframe; iframe #; ipureintro; exact ⟨h1, h2, h3, h4⟩
  · iright; iframe #; ipureintro; rfl

/-- `writerStC` with a mapping, from its parts. -/
theorem writerStC_mk (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString)
    (mp : List w8) (fl : Bool) (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m : OsMeta)
    (bs : List (w8 × Bool)) (fsz : Nat)
    (h : (2 ≤ hwm ∧ 4096 * hwm ≤ m.size ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩)) ∧
      (fl = false → (bs.map Prod.fst).take 8192 = mp ∧ commitClean m bs ∧ fsz = m.size ∧
        0 ≤ fd.toInt ∧ 4 * 4096 ≤ m.size ∧ m.size ≤ 2 ^ 30 ∧ len ≤ 2 ^ 30)) ∧
      (m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41)) :
    ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
      csOwn (GF := GF) p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ p base len γm ∗ writerCells (GF := GF) base hwm len ⊢
      writerStC (GF := GF) γ γc db f fd p mp fl hwm (some (base, len, γm)) m bs := by
  iintro ⟨Hcur, Hmap, Hout, Hflds, Hfsz, Hdsz, Hf, Hfd, Hcs, Hcls, Htok, #Hinv, Hwc⟩
  unfold writerStC writerFileC
  dsimp only [mapLen]
  iframe Hcur Hmap Hout Hflds Hcls
  isplitl [Hfsz Hdsz Hf Hfd Hcs]
  · iexists fsz
    iframe
    ipureintro; exact h.1
  · iframe; iframe #; ipureintro; exact h.2

/-- An error exit of `commit` while the handle is not yet failed, with a mapping (the state's
size since the file size field was set may differ: `writerFileC` once failed). -/
theorem commitErrC_mk (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString)
    (mp : List w8) (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m : OsMeta)
    (bs : List (w8 × Bool)) (fsz t n : Nat)
    (h : m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm ≤ m.size ∧
      ∀ M : GMap Loc Nat, dbOk p (some ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩)) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
      csOwn (GF := GF) p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ p base len γm ∗ writerCells (GF := GF) base hwm len ⊢
      commitErrC (GF := GF) γ γc db f fd p t := by
  iintro ⟨Hown, Hcur, Hmap, Hout, Hflds, Hfsz, Hdsz, Hf, Hfd, Hcs, Hcls, Htok, #Hinv, Hwc⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  unfold commitErrC writerStFC writerFileC
  isplitl [Hown]
  · iexists n; iexact Hown
  iexists mp, false, hwm, some (base, len, γm), m, bs
  iframe Hcur Hmap Hout Hflds Hcls
  dsimp only [mapLen]
  isplitl [Hfsz Hdsz Hf Hfd Hcs Htok Hwc]
  · isplitl [Hfsz Hdsz Hf Hfd Hcs]
    · iexists fsz
      iframe
      ipureintro
      exact ⟨h5, h6, h7, fun h => by cases h⟩
    · iframe; iframe #; ipureintro; exact ⟨h1, h2, h3, h4⟩
  · ileft; ipureintro; rfl

/-- An error exit of `commit` while writing the data page (not yet failed): its cells back with
the writer's. -/
theorem dataErrC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString)
    (mp : List w8) (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m : OsMeta)
    (bs : List (w8 × Bool)) (fsz t n : Nat)
    (h : m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm + 4096 ≤ m.size ∧
      ∀ M : GMap Loc Nat, dbOk p (some ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩)) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
      csOwn (GF := GF) p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ p base len γm ∗
      ((∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
        (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf)) ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ⊢
      commitErrC (GF := GF) γ γc db f fd p t := by
  iintro ⟨Hown, Hcur, Hmap, Hout, Hflds, Hfsz, Hdsz, Hf, Hfd, Hcs, Hcls, Htok, #Hinv, Hwc4, Hpc, Htop⟩
  ihave Hwc := cells_rejoin base hwm len (by omega) $$ [Hwc4 Hpc Htop]
  · iframe Hwc4 Hpc Htop
  iapply commitErrC_mk γ γc db f fd p mp hwm base len γm m bs fsz t n
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, by omega, h.2.2.2.2.2.2⟩
  iframe; iframe #

end lemmas


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 20000 in
theorem DB.commit.wp_proof_crash (wp_mmap : DB.mmap.specCrash (GF := GF) (hG := hG))
    (wp_Truncate : os.File.Truncate.specCrashS (GF := GF) (hG := hG))
    (wp_Sync : os.File.Sync.specCrashS (GF := GF) (hG := hG))
    (wp_pageAt : pageAt.spec (GF := GF) (hG := hG))
    (wp_WriteAt : os.File.WriteAt.specCrashS (GF := GF) (hG := hG))
    (wp_Fd : os.File.Fd.spec (GF := GF) (hG := hG))
    (wp_Fdatasync : syscall.Fdatasync.specCrashS (GF := GF) (hG := hG))
    (wp_pmeta : Page.«meta».spec (GF := GF) (hG := hG))
    (wp_write : Meta.write.spec (GF := GF) (hG := hG)) :
    DB.commit.specCrash (GF := GF) (hG := hG) := by
  intro γ γc db f fd p mp st m bs v Hok Ht Hb Hmok Hst Hvp Hboot
  generalize hmv : curMeta mp = mv at Ht Hvp Hboot ⊢
  generalize hhwm : curPgid mp = hwm at Hb ⊢
  have hpg : mv.pgid'.toNat = hwm := by rw [← hmv, ← hhwm]; rfl
  wp_start as ⟨#Hpkg, #Hos, #Hci, #Hfile, #Hmeta, #Hguard, Hws, Hown⟩
  unfold writerStC
  icases Hws with ⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, Hstr⟩
  rcases st with _ | ⟨base, len, γm⟩
  · exact absurd rfl Hst
  dsimp only
  icases Hstr with ⟨%Hstp, Htok, #Hinv, Hwc⟩
  iunfold writerFileC at Hw
  icases Hw with ⟨%fsz, Hfsz, Hdsz, Hf, Hfd, Hcs, %Hwf⟩
  obtain ⟨hmp, hcc, rfl, hfd, hsz⟩ := Hwf.2.2.2 rfl
  wp_alloc «$res0_ptr» as «$res0»
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_alloc_auto
  wp_pures
  wp_apply (Meta.wp_alloc_pos mv) as %m_ptr ⟨m, %Hmpos⟩
  (try wp_auto)
  dsimp only
  have hhwm2 : hwm + 2 ≤ 2 ^ 18 := by omega
  have hmZ : sint.Z ((mv.pgid' + W64 1 + W64 1) * W64 4096) = ((hwm + 2) * 4096 : Nat) := by
    have h1 : (mv.pgid' + W64 1 + W64 1).toNat = hwm + 2 := by
      simp only [BitVec.toNat_add]; rw [hpg]; show ((hwm + 1) % 2 ^ 64 + 1) % 2 ^ 64 = _; omega
    have h2 : ((mv.pgid' + W64 1 + W64 1) * W64 4096).toNat = (hwm + 2) * 4096 := by
      rw [BitVec.toNat_mul, h1]; show (hwm + 2) * 4096 % 2 ^ 64 = _; omega
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond, h2]; split <;> omega
  have hlenZ : sint.Z (W64 (len : Int)) = len := by
    have : len ≤ 2 ^ 41 := Hstp.2.2.2
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  simp only [mapLen, hlenZ, hmZ]
  generalize hminsz : (mv.pgid' + W64 1 + W64 1) * W64 4096 = minsz at hmZ ⊢
  -- remap if the next high water mark passes the mapping
  wp_join (Q := fun bv => iprop((⌜bv = executeVal⌝ ∗ ∃ (base' : Loc) (len' : Nat) (γm' : GName) (m' : OsMeta),
      writerStC (GF := GF) γ γc db f fd p mp false hwm (some (base', len', γm')) m' bs ∗
      ⌜m'.ok = true ∧ (hwm + 2) * 4096 ≤ len'⌝ ∗
      dbOwner (GF := GF) γ mv.txid'.toNat hwm ∗
      db_ptr ↦ db ∗ minsz_ptr ↦ minsz ∗ «$res0_ptr» ↦ GoInterface.nil ∗
      v_ptr ↦ v ∗ pg_ptr ↦ mv.pgid' ∗ m_ptr ↦ nextMeta mv) ∨
    (∃ e : GoInterface, ⌜bv = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ e ∗ commitErrC (GF := GF) γ γc db f fd p mv.txid'.toNat)))
    with [-HΦ]
  · -- remap
    wp_apply wp_mmap γ γc db f fd p minsz mp false hwm (some (base, len, γm)) m bs rfl (by omega)
        (by omega) $$ [Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Htok Hwc]
      as %err ⟨%st', %m', Hcur, Hmap, Hout, Hflds, Hw, %Hm', Hres⟩
    · iframe #
      unfold writerFileC mmapPre
      dsimp only
      iframe
      ipureintro
      exact ⟨⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, fun _ => ⟨hmp, hcc, rfl, hfd, hsz⟩⟩, Hstp⟩
    icases Hres with (⟨%Herr, %base', %len', %γm', %Hst', Htok, #Hinv', Hwc⟩ | ⟨%Herr, Hx⟩)
    · subst Herr
      obtain ⟨rfl, Hmaps', Hsz', Hmin', Hb', Hl41⟩ := Hst'
      (try wp_auto)
      ileft
      isplitr
      · ipureintro; rfl
      iexists base', len', γm', m'
      iframe
      unfold writerStC
      dsimp only
      iframe; iframe #
      ipureintro
      refine ⟨⟨Hmaps', by omega, Hb', Hl41⟩, by rw [Hm'.2.1]; exact Hmok, by omega⟩
    · obtain ⟨Herr, rfl⟩ := Herr
      cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      (try wp_auto)
      iright
      iexists (GoInterface.ok ie)
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Herr⟩
      iapply commitErrC_of γ γc db f fd p mp hwm none m' bs _ hwm
      isplitl [Hown]
      · iexact Hown
      unfold writerStC; dsimp only; iframe
  · -- no remap
    ileft
    isplitr
    · ipureintro; trivial
    iexists base, len, γm, m
    ihave Hws := writerStC_mk γ γc db f fd p mp false hwm base len γm m bs m.size
        ⟨⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, fun _ => ⟨hmp, hcc, rfl, hfd, hsz⟩⟩, Hstp⟩
      $$ [Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc]
    · iframe; iframe #
    iframe
    ipureintro; exact ⟨Hmok, by omega⟩
  iintro (⟨%Hbv, %base, %len, %γm, %m', Hws, %Hm', Hown, db, minsz, «$res0», v, pg, m⟩ |
    ⟨%e, %Hbv, db, «$res0», Herr⟩)
  rotate_left
  · obtain ⟨rfl, He⟩ := Hbv
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact He
    iunfold commitErrC at Herr
    iexact Herr
  subst Hbv
  clear hcc hmp Hwf hsz hfd Hstp
  iunfold writerStC at Hws
  icases Hws with ⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, %Hstp, Htok, #Hinv, Hwc⟩
  iunfold writerFileC at Hw
  icases Hw with ⟨%fsz, Hfsz, Hdsz, Hf, Hfd, Hcs, %Hwf⟩
  obtain ⟨hmp, hcc, rfl, hfd, hsz⟩ := Hwf.2.2.2 rfl
  obtain ⟨Hmaps, Hsz, Hbase, Hl41⟩ := Hstp
  obtain ⟨Hok', Hlen⟩ := Hm'
  icases csOwn_wf' _ _ _ $$ Hcs with ⟨Hcs, %Hcw⟩
  have hbl : bs.length = m'.size := Hcw.1
  have h2 := Hwf.1
  have hpgb : curPgid ((bs.map Prod.fst).take 8192) = hwm := by rw [hmp, hhwm]
  have hsZ : sint.Z (W64 (m'.size : Int)) = m'.size := by
    show BitVec.toInt _ = _
    rw [BitVec.toInt_eq_toNat_cond]; simp only [BitVec.toNat_ofInt]; split <;> omega
  have hlen64 : (W64 (len : Int)).toNat = len := by simp only [BitVec.toNat_ofInt]; omega
  have hlenI : 0 ≤ (W64 (len : Int)).toInt := by
    rw [BitVec.toInt_eq_toNat_cond, hlen64]; split <;> omega
  dsimp only [mapLen]
  (try wp_auto)
  simp only [hsZ, hmZ]
  -- grow: Truncate and Sync
  wp_join (Q := fun bv => iprop((⌜bv = executeVal⌝ ∗ ∃ (m2 : OsMeta) (bs2 : List (w8 × Bool)),
      writerStC (GF := GF) γ γc db f fd p mp false hwm (some (base, len, γm)) m2 bs2 ∗
      ⌜m2.ok = true ∧ (hwm + 2) * 4096 ≤ m2.size⌝ ∗
      db_ptr ↦ db ∗ «$res0_ptr» ↦ GoInterface.nil ∗
      v_ptr ↦ v ∗ pg_ptr ↦ mv.pgid' ∗ m_ptr ↦ nextMeta mv ∗
      dbOwner (GF := GF) γ mv.txid'.toNat hwm) ∨
    (∃ e : GoInterface, ⌜bv = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ e ∗ commitErrC (GF := GF) γ γc db f fd p mv.txid'.toNat)))
    with [-HΦ]
  · (try wp_auto)
    have hsz' : m'.size < (hwm + 2) * 4096 := by exact_mod_cast Hif
    icases (writerCells_top base hwm len).1 $$ Hwc with ⟨Hwc4, Htop⟩
    iunfold cellsAny at Htop
    icases Htop with ⟨%vf, Htop⟩
    rw [show len - 4096 * hwm = (m'.size - 4096 * hwm) + (len - m'.size) by omega]
    icases (cellsR_append _ _ _ _ _).1 $$ Htop with ⟨Hlow, Hhigh⟩
    rw [show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
    ihave Hmc := (mcellsAny_single (GF := GF) base len m'.size len Hsz (Nat.le_refl _)).2 $$ [Hhigh]
    · unfold cellsAny; iexists vf; iexact Hhigh
    have hobl := trunc_obl (p := p) hcc hbl (show len ≤ 2 ^ 30 from hsz.2.2) Hsz
      (by rw [hpgb, hbl]; exact Hwf.2.1) 8192 (4096 * hwm)
    rw [← hlen64] at hobl
    rw [← Hmaps]
    wp_apply wp_Truncate f fd p _ (W64 (len : Int)) _ ⟨p, true, true⟩ dbCrashN γc (dbOk p) m' bs
        8192 (4096 * hwm) len hfd rfl hlenI (by rw [hlen64]; exact Hsz)
        (fun b l h => by rw [Hmaps] at h; simp at h; omega) dbCrashN_disj hobl
        $$ [Hf Hfd Hcs Hmc] as %err ⟨Hf, Hfd, Hres⟩
    · iframe; iframe #
    simp only [hlen64]
    have h4 := Hwf.2.1
    -- the grown state
    obtain ⟨hccG, hblG⟩ := treach_commitClean (sz := len) hcc hbl hsz.2.2 Hsz
      (by rw [hpgb, hbl]; exact h4) .grown
    have hpreG : ∀ k < 4096 * hwm,
        (bs ++ List.replicate (len - m'.size) ((0 : w8), false))[k]? = bs[k]? :=
      fun k hk => List.getElem?_append_left (by omega)
    have hpgG : curPgid (((bs ++ List.replicate (len - m'.size) ((0 : w8), false)).map Prod.fst).take
        8192) = hwm := by rw [take8192_congr hpreG (by omega), hpgb]
    have hcells : ∀ (Hc : IProp GF), (Hc ⊢ cellsR (GF := GF) base m'.size (len - m'.size) (fun _ => byteCell 0)) →
        (∃ vf, cellsR (GF := GF) base 0 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 80 4016 vf) ∗
          (∃ vf, cellsR (GF := GF) base 4096 16 vf) ∗ (∃ vf, cellsR (GF := GF) base 4176 4016 vf) ∗
          cellsR (GF := GF) base (4096 * hwm) (m'.size - 4096 * hwm) vf ∗ Hc ⊢
        writerCells (GF := GF) base hwm len := by
      intro Hc hHc
      iintro ⟨H0, H1, H2, H3, Hlow, Hc⟩
      ihave Hc := hHc $$ Hc
      iapply (writerCells_top base hwm len).2
      iframe H0 H1 H2 H3
      rw [show len - 4096 * hwm = (m'.size - 4096 * hwm) + (len - m'.size) by omega]
      iapply cellsAny_append
      isplitl [Hlow]
      · unfold cellsAny; iexists vf; iexact Hlow
      rw [show 4096 * hwm + (m'.size - 4096 * hwm) = m'.size by omega]
      unfold cellsAny; iexists _; iexact Hc
    icases Hres with (⟨%Herr, Hg⟩ | ⟨%Herr, (Hg | ⟨Hcs, Hmc⟩)⟩)
    · subst Herr
      iunfold csGrownOwn at Hg
      icases Hg with ⟨Hcs, Hc, -⟩
      rw [Hmaps]
      ihave Hwc := hcells _ (mcells_single (GF := GF) base len m'.size len _ Hsz (Nat.le_refl _)).1
        $$ [Hwc4 Hlow Hc]
      · iframe
      (try wp_auto)
      obtain ⟨hH, hF, hHc, hccS, hblS, htkS, -⟩ := syncK_facts (m := m'.grown len) hccG hblG hpgG h2
        (by simp only [OsMeta.grown]; omega) (by simp only [OsMeta.grown]; exact hsz.2.2)
        (by simp only [OsMeta.grown]; omega)
      have hccF := commitClean_meta (m' := { m'.grown len with ok := false }) hccG rfl rfl
      ihave Hcs := (csOwn_split3 p γc (m'.grown len) _ hwm h2).1 $$ Hcs
      wp_apply wp_Sync f fd p _ _ ⟨p, true, true⟩ dbCrashN γc (dbOk p) (m'.grown len) _ _ _ 8192
          (4096 * hwm) false hH hF (fun _ => hHc) dbCrashN_disj
          (commitClean_okS _ hblS rfl hccS)
          (commitClean_okS ⟨{ m'.grown len with ok := false }, _, 8192, 4096 * hwm, .idle⟩
            (by rw [split3_eq _ _ _ (by omega)]; exact hblG) rfl
            (by rw [split3_eq _ _ _ (by omega)]; exact hccF))
        $$ [Hf Hfd Hcs] as %err2 ⟨Hf, Hfd, Hres2⟩
      · iframe; iframe #
      icases Hres2 with (⟨%Herr2, Hcs⟩ | ⟨%Herr2, Hcs⟩)
      · subst Herr2
        (try wp_auto)
        dsimp only [csSynced]
        ileft
        isplitr
        · ipureintro; trivial
        iexists _, _
        ihave Hws := writerStC_mk γ γc db f fd p mp false hwm base len γm _ _ len
            ⟨⟨h2, by simp only [OsMeta.syncedKeep, OsMeta.synced, OsMeta.grown]; omega,
              writer_okS _ _ hblS hccS, fun _ => ⟨by rw [htkS, take8192_congr hpreG (by omega), hmp],
                hccS, rfl, hfd, by simp only [OsMeta.syncedKeep, OsMeta.synced, OsMeta.grown]; omega,
                by simp only [OsMeta.syncedKeep, OsMeta.synced, OsMeta.grown]; exact hsz.2.2,
                hsz.2.2⟩⟩,
              by simp only [OsMeta.syncedKeep, OsMeta.synced, OsMeta.grown]; exact Hmaps,
              by simp only [OsMeta.syncedKeep, OsMeta.synced, OsMeta.grown]; omega, Hbase, Hl41⟩
          $$ [Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc]
        · iframe; iframe #
        iframe
        ipureintro
        exact ⟨Hok', by simp only [OsMeta.syncedKeep, OsMeta.synced, OsMeta.grown]; omega⟩
      · cases err2 with
        | nil => exact absurd rfl Herr2
        | ok ie =>
        (try wp_auto)
        iright
        iexists GoInterface.ok ie
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, Herr2⟩
        ihave Hcs := (csOwn_split3 p γc { m'.grown len with ok := false } _ hwm h2).2 $$ Hcs
        iapply commitErrC_mk γ γc db f fd p mp hwm base len γm { m'.grown len with ok := false } _
          m'.size _ hwm ⟨by simp only [OsMeta.grown]; exact Hmaps, by simp only [OsMeta.grown]; omega,
            Hbase, Hl41, h2, by simp only [OsMeta.grown]; omega, writer_okS _ _ hblG hccF⟩
        iframe; iframe #
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      iunfold csGrownOwn at Hg
      icases Hg with ⟨Hcs, Hc, -⟩
      rw [Hmaps]
      ihave Hwc := hcells _ (mcells_single (GF := GF) base len m'.size len _ Hsz (Nat.le_refl _)).1
        $$ [Hwc4 Hlow Hc]
      · iframe
      (try wp_auto)
      iright
      iexists GoInterface.ok ie
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Herr⟩
      iapply commitErrC_mk γ γc db f fd p mp hwm base len γm (m'.grown len) _
        m'.size _ hwm ⟨by simp only [OsMeta.grown]; exact Hmaps, by simp only [OsMeta.grown]; omega,
          Hbase, Hl41, h2, by simp only [OsMeta.grown]; omega, writer_okS _ _ hblG hccG⟩
      iframe; iframe #
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      ihave Htop := cells_back base m' len hwm vf Hmaps Hsz h4 $$ [Hmc Hlow]
      · iframe
      ihave Hwc := (writerCells_top base hwm len).2 $$ [Hwc4 Htop]
      · iframe
      (try wp_auto)
      iright
      iexists GoInterface.ok ie
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Herr⟩
      have hccT := (treach_commitClean (sz := len) hcc hbl hsz.2.2 Hsz
        (by rw [hpgb, hbl]; exact h4) .ft).1
      iapply commitErrC_mk γ γc db f fd p mp hwm base len γm (ftMeta m' len) bs
        m'.size _ hwm ⟨Hmaps, Hsz, Hbase, Hl41, h2, h4, writer_okS _ _ hbl hccT⟩
      iframe; iframe #
  · -- no growth
    ileft
    isplitr
    · ipureintro; trivial
    iexists m', bs
    ihave Hws := writerStC_mk γ γc db f fd p mp false hwm base len γm m' bs m'.size
        ⟨⟨Hwf.1, Hwf.2.1, Hwf.2.2.1, fun _ => ⟨hmp, hcc, rfl, hfd, hsz⟩⟩, Hmaps, Hsz, Hbase, Hl41⟩
      $$ [Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc]
    · iframe; iframe #
    iframe
    ipureintro; exact ⟨Hok', by omega⟩
  sorry

end proof

end bboltfs
end EtcdGrove
end Perennial
