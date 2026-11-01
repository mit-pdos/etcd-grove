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

-- the kernel's check of some `omega` proofs below recurses deeply
set_option maxRecDepth 20000

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.bboltfs

section pure
variable [GooseExts]

/-- An equation `omega` does not look into (`curPgid` of meta pages: `omega` unfolds it). -/
def HideEq (a b : Nat) : Prop := a = b

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
    fun k hk => by rw [hpre k (by omega)]; exact h.metas k hk, fun k hk => ?_, by rw [ht]; exact h.tx⟩
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
    fun k hk => by rw [hout _ (by omega)]; exact h.metaS k hk, h.tx, h.nValid, h.nTx, h.nTxS, hNR,
    h.nRootPg, h.nTxPg, h.nPg, by rw [hN.lo]; exact h.nPgLo, by rw [hpage _ hNR]; exact h.nBoot,
    fun k hk => by rw [hout _ (.inr (by omega))]; exact h.nPage k hk, durOk_congr hdur hdurHi h.dur⟩

/-- `commitMetaSt` does not look at the mappings or `ok`. -/
theorem commitMetaSt_meta {m m' : OsMeta} {bs : List (w8 × Bool)} {mp : List w8} {N : Meta}
    {s : Nat} (h : commitMetaSt m bs mp N s) (hhi : m'.hi = m.hi) (hlo : m'.lo = m.lo)
    (hdur : m'.dur = m.dur) (hdh : m'.durHi = m.durHi) : commitMetaSt m' bs mp N s :=
  ⟨h.s2, h.sTx, hhi ▸ h.hi, hlo ▸ h.lo, h.ok, h.slot, hlo ▸ h.pg, h.boot, h.root, h.metaS, h.tx,
    h.nValid, h.nTx, h.nTxS, h.nRoot, h.nRootPg, h.nTxPg, h.nPg, hlo ▸ h.nPgLo, h.nBoot, h.nPage,
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
    (hboot : bootOk (curMeta mp').txid'.toNat (pageVal B)) (htx : txOk mp') :
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
    fun k hk => ?_, by rw [hX]; exact htx⟩, hl'⟩
  · rw [List.getElem?_append_left (by omega), hsH, List.getElem?_map,
      List.getElem?_eq_getElem (by omega)]
    exact ⟨_, rfl⟩
  · rw [hX, hhi _ (by omega), hpage k hk, List.getElem?_eq_getElem (by omega)]
    exact ⟨_, rfl⟩

/-- The meta pages of a state whose bytes below `N ≥ 8192` are the same. -/
theorem csSynced_false_eq (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat) :
    csSynced false m H F T fa fb = ⟨m.syncedKeep fb T 0 H, H ++ (F ++ syncedBytes m T), fa, fb, .idle⟩ :=
  rfl

theorem csSynced_true_eq (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat) :
    csSynced true m H F T fa fb = ⟨m.synced 0 H, syncedBytes m H ++ (F ++ T), fa, fb, .idle⟩ :=
  rfl

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

/-- The grown state's sync (`Truncate` then `Sync` in `commit`): `syncK_facts` of it. -/
theorem grow_sync_facts {m : OsMeta} {bs : List (w8 × Bool)} {hwm len : Nat} (h : commitClean m bs)
    (hl : bs.length = m.size) (hpg : curPgid ((bs.map Prod.fst).take 8192) = hwm) (h2 : 2 ≤ hwm)
    (h4 : 4096 * hwm ≤ m.size) (hsz : m.size ≤ len) (h30 : len ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size) :
    commitClean (m.grown len) (bs ++ List.replicate (len - m.size) ((0 : w8), false)) ∧
    (bs ++ List.replicate (len - m.size) ((0 : w8), false)).length = (m.grown len).size ∧
    ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).take 8192).length = 8192 ∧
    8192 + (((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop 8192).take
      (4096 * hwm - 8192)).length = 4096 * hwm ∧
    (∀ y ∈ (bs ++ List.replicate (len - m.size) ((0 : w8), false)).take 8192, y.2 = true) ∧
    commitClean ((m.grown len).syncedKeep (4096 * hwm)
        ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop (4096 * hwm)) 0
        ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).take 8192))
      ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).take 8192 ++
        (((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop 8192).take (4096 * hwm - 8192) ++
        syncedBytes (m.grown len) ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop
          (4096 * hwm)))) ∧
    ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).take 8192 ++
        (((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop 8192).take (4096 * hwm - 8192) ++
        syncedBytes (m.grown len) ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop
          (4096 * hwm)))).length = len ∧
    (((bs ++ List.replicate (len - m.size) ((0 : w8), false)).take 8192 ++
        (((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop 8192).take (4096 * hwm - 8192) ++
        syncedBytes (m.grown len) ((bs ++ List.replicate (len - m.size) ((0 : w8), false)).drop
          (4096 * hwm)))).map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 := by
  obtain ⟨hccG, hblG⟩ := treach_commitClean (sz := len) h hl h30 hsz (by rw [hpg, hl]; exact h4)
    .grown
  have hpreG : ∀ k < 4096 * hwm,
      (bs ++ List.replicate (len - m.size) ((0 : w8), false))[k]? = bs[k]? :=
    fun k hk => List.getElem?_append_left (by omega)
  have htG := take8192_congr hpreG (by omega)
  have hsG : (m.grown len).size = len := rfl
  obtain ⟨hH, hF, hHc, hccS, hblS, htkS, -⟩ := syncK_facts (m := m.grown len) hccG hblG
    (by rw [htG, hpg]) h2 (by rw [hsG]; omega) (by rw [hsG]; exact h30) (by rw [hsG]; omega)
  exact ⟨hccG, hblG, hH, hF, hHc, hccS, hblS.trans hsG, by rw [htkS, htG]⟩

/-- `commit`'s growth (`Truncate` to `len`, then `Sync`), as obligations and the states it leaves,
named. -/
theorem grow_facts {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)} {hwm len : Nat}
    (h : commitClean m bs) (hl : bs.length = m.size)
    (hpg : curPgid ((bs.map Prod.fst).take 8192) = hwm) (h2 : 2 ≤ hwm)
    (h4 : 4096 * hwm ≤ m.size) (hsz : m.size ≤ len) (h30 : len ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size) :
    ∃ (M3 : OsMeta) (B3 H F T : List (w8 × Bool)),
      bs ++ List.replicate (len - m.size) ((0 : w8), false) = H ++ (F ++ T) ∧ H.length = 8192 ∧
      8192 + F.length = 4096 * hwm ∧ (∀ y ∈ H, y.2 = true) ∧
      csSynced false (m.grown len) H F T 8192 (4096 * hwm) = ⟨M3, B3, 8192, 4096 * hwm, .idle⟩ ∧
      commitClean M3 B3 ∧ M3.size = len ∧ M3.maps = m.maps ∧ M3.ok = m.ok ∧
      (B3.map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ M3 with maps := M }, B3, 8192, 4096 * hwm, .idle⟩)) ∧
      dbOk p (some ⟨M3, B3, 8192, 4096 * hwm, .idle⟩) ∧
      dbOk p (some ⟨{ m.grown len with ok := false }, H ++ (F ++ T), 8192, 4096 * hwm, .idle⟩) ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ { m.grown len with ok := false } with maps := M },
        H ++ (F ++ T), 8192, 4096 * hwm, .idle⟩)) ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ m.grown len with maps := M },
        bs ++ List.replicate (len - m.size) ((0 : w8), false), 8192, 4096 * hwm, .idle⟩)) ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ ftMeta m len with maps := M }, bs, 8192, 4096 * hwm,
        .idle⟩)) := by
  obtain ⟨hccG, hblG, hH, hF, hHc, hccS, hblS, htkS⟩ :=
    grow_sync_facts h hl hpg h2 h4 hsz h30 h16
  have hccT := (treach_commitClean (sz := len) h hl h30 hsz (by rw [hpg, hl]; exact h4) .ft).1
  have e := split3_eq (bs ++ List.replicate (len - m.size) ((0 : w8), false)) 8192 (4096 * hwm)
    (by omega)
  have hccF := commitClean_meta (m' := { m.grown len with ok := false }) hccG rfl rfl
  refine ⟨_, _, _, _, _, e.symm, hH, hF, hHc, rfl, hccS, rfl, rfl, rfl, htkS,
    writer_okS 8192 (4096 * hwm) (by rw [hblS]; rfl) hccS,
    commitClean_okS _ (by rw [hblS]; rfl) rfl hccS,
    commitClean_okS _ (by rw [e]; exact hblG) rfl (by rw [e]; exact hccF),
    fun M => writer_okS (m := { m.grown len with ok := false }) 8192 (4096 * hwm)
      (by rw [e]; exact hblG) (by rw [e]; exact hccF) M,
    writer_okS (m := m.grown len) 8192 (4096 * hwm) hblG hccG,
    writer_okS (m := ftMeta m len) 8192 (4096 * hwm) hl hccT⟩

theorem arith_hwm (hwm s : Nat) (h2 : 2 ≤ hwm) (hsz : (hwm + 2) * 4096 ≤ s) :
    4 * 4096 ≤ s ∧ 4096 * hwm ≤ s ∧ 4096 * (hwm + 1) ≤ s ∧ 8192 ≤ 4096 * hwm ∧
      4096 * hwm + 4096 ≤ s := by
  omega

theorem arith_sub4096 (a b : Nat) (h : a + 4096 ≤ b) : b - a = 4096 + (b - a - 4096) := by
  omega

/-- What the data page's write reaches, as the writer's state. -/
theorem dataW_after {p : GoString} {m2 m4 : OsMeta} {bs2 bs4 : List (w8 × Bool)} {hwm : Nat}
    {mp D : List w8} (hcc : commitClean m2 bs2) (hbl : bs2.length = m2.size)
    (hmp : (bs2.map Prod.fst).take 8192 = mp) (hpg : curPgid mp = hwm) (h2 : 2 ≤ hwm)
    (h4 : 4096 * hwm + 4096 ≤ m2.size) (hD : D.length = 4096) (h30 : m2.size ≤ 2 ^ 30)
    (hR : WReach m2 bs2 (4096 * hwm) D m4 bs4) :
    commitClean m4 bs4 ∧ bs4.length = m4.size ∧ (bs4.map Prod.fst).take 8192 = mp ∧
      m4.size = m2.size ∧ m4.maps = m2.maps ∧ m4.ok = m2.ok ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ m4 with maps := M }, bs4, 8192, 4096 * hwm, .idle⟩)) := by
  obtain ⟨hc, hN⟩ := dataW_reach hcc hbl (by rw [hmp, hpg]; exact Nat.le_refl _) (by omega)
    (by rw [hD]; omega) hR
  have hs1 := hN.size
  have hs2 := hN.szhi
  refine ⟨hc, hN.len, ?_, by rw [hD] at hs2; omega, hN.maps, hN.ok,
    writer_okS (m := m4) 8192 (4096 * hwm) hN.len hc⟩
  rw [← hmp]
  exact take8192_congr (N := 4096 * hwm) (fun k hk => hN.pre k (by unfold cfLo; omega)) (by omega)

/-- The slot the next commit writes. -/
theorem slot_next (t : w64) :
    ((t + W64 1) % W64 2).toNat = 1 - t.toNat % 2 := by
  rw [BitVec.toNat_umod, BitVec.toNat_add]
  show ((t.toNat + 1) % 2 ^ 64) % 2 = _
  omega

/-- What the meta write reaches, as the writer's state. -/
theorem metaW_after {p : GoString} {m m' : OsMeta} {bs bs' : List (w8 × Bool)} {mp : List w8}
    {N : Meta} {s hwm : Nat} {D : List w8} (h : commitMetaSt m bs mp N s) (hl : bs.length = m.size)
    (hD : D.length = 4096) (h8 : 8192 ≤ m.size) (hcl : ∀ k < 8192, ∃ b, bs[k]? = some (b, true))
    (hw : pageMeta D = N) (hR : WReach m bs (4096 * (1 - s)) D m' bs') :
    commitMetaSt m' bs' mp N s ∧
      cacheOk bs' (1 - s) (fun X => X = fileMeta mp (1 - s) ∨ X = N) ∧ bs'.length = m'.size ∧
      m'.maps = m.maps ∧ m'.size = m.size ∧ m'.ok = m.ok ∧
      (∀ k, (k < 4096 * (1 - s) ∨ 4096 * (1 - s) + 4096 ≤ k) → bs'[k]? = bs[k]?) ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ m' with maps := M }, bs', 8192, 4096 * hwm, .idle⟩)) ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ { m' with ok := false } with maps := M }, bs', 8192,
        4096 * hwm, .idle⟩)) ∧
      dbOk p (some ⟨{ m' with ok := false }, bs', 8192, 4096 * hwm, .idle⟩) := by
  obtain ⟨hM, hc, hl'⟩ := metaW_reach h hl hD h8 hcl hw hR
  have hN := hR.narrow hl
  have hs2 := h.s2
  have hs1 := hN.size
  have hs2' := hN.szhi
  refine ⟨hM, hc, hl', hN.maps, by rw [hD] at hs2'; omega, hN.ok, ?_,
    fun M => commitMetaIdle_okS ⟨{ m' with maps := M }, bs', 8192, 4096 * hwm, .idle⟩ hl' rfl
      (commitMetaSt_meta (m := m') hM rfl rfl rfl rfl) hc,
    fun M => commitMetaIdle_okS ⟨{ { m' with ok := false } with maps := M }, bs', 8192, 4096 * hwm,
      .idle⟩ hl' rfl (commitMetaSt_meta (m := m') hM rfl rfl rfl rfl) hc,
    commitMetaIdle_okS ⟨{ m' with ok := false }, bs', 8192, 4096 * hwm, .idle⟩ hl' rfl
      (commitMetaSt_meta (m := m') hM rfl rfl rfl rfl) hc⟩
  rintro k (hk | hk)
  · exact hN.pre k (by unfold cfLo; omega)
  · exact hN.suf (by omega) k (by omega)

theorem setPage_getElem? (xs PB : List w8) (i k : Nat) (hl : xs.length = 8192) (hi : i < 2)
    (hPB : PB.length = 4096) :
    (setPage xs i PB)[k]? =
      if 4096 * i ≤ k ∧ k < 4096 * i + 4096 then PB[k - 4096 * i]? else xs[k]? := by
  unfold setPage
  have h1 : (xs.take (4096 * i)).length = 4096 * i := by rw [List.length_take]; omega
  by_cases ha : k < 4096 * i
  · rw [List.append_assoc, List.getElem?_append_left (by omega), List.getElem?_take, if_pos ha,
      if_neg (by omega)]
  · rw [List.append_assoc, List.getElem?_append_right (l₁ := xs.take (4096 * i)) (by omega), h1]
    by_cases hb : k < 4096 * i + 4096
    · rw [List.getElem?_append_left (by omega), if_pos ⟨by omega, hb⟩]
    · rw [List.getElem?_append_right (by omega), hPB, List.getElem?_drop, if_neg (by omega),
        show 4096 * (i + 1) + (k - 4096 * i - 4096) = k by omega]

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
  have htx0 := h.tx
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
  have hnTxPg : (commitOf (curMeta mp)).txid'.toNat < (commitOf (curMeta mp)).pgid'.toNat := by
    have := htx0.2; unfold curPgid at this; rw [htx, hnpg]; omega
  refine ⟨hs2, rfl, hhi, hlo4, ⟨hl8, hv, hr2, hrp, hbd⟩, hslot, hpg, hboot0, hroot, ?_, htx0, hN,
    ?_, htx, hnum.1, hnum.2.1, hnTxPg, hnum.2.2.1, hnum.2.2.2,
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

/-- The data page's sync (`Fdatasync`, keeping the meta pages): obligations, and what the meta
write needs of the state it leaves. -/
theorem dataS_facts {p : GoString} {m4 : OsMeta} {bs4 : List (w8 × Bool)} {hwm : Nat} {mp : List w8}
    {mv : Meta} {v : w64} (hc : commitClean m4 bs4) (hl : bs4.length = m4.size)
    (hmp : (bs4.map Prod.fst).take 8192 = mp) (hmv : curMeta mp = mv) (hpg : curPgid mp = hwm)
    (h2 : 2 ≤ hwm) (hok : m4.ok = true) (hsz : (hwm + 2) * 4096 ≤ m4.size) (h30 : m4.size ≤ 2 ^ 30)
    (hd : ∀ i < 4096, (bs4[4096 * hwm + i]?).map Prod.fst = (dataPage mv.pgid' v)[i]?)
    (ht : mv.txid'.toNat + 1 < 2 ^ 64) (hb : (hwm + 2) * 4096 ≤ 2 ^ 30)
    (hboot : bootOk (mv.txid'.toNat + 1) (some v)) :
    ∃ (M5 : OsMeta) (B5 H F T : List (w8 × Bool)),
      bs4 = H ++ (F ++ T) ∧ H.length = 8192 ∧ 8192 + F.length = 4096 * hwm ∧ (∀ y ∈ H, y.2 = true) ∧
      csSynced false m4 H F T 8192 (4096 * hwm) = ⟨M5, B5, 8192, 4096 * hwm, .idle⟩ ∧
      dbOk p (some ⟨M5, B5, 8192, 4096 * hwm, .idle⟩) ∧
      dbOk p (some ⟨{ m4 with ok := false }, H ++ (F ++ T), 8192, 4096 * hwm, .idle⟩) ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ { m4 with ok := false } with maps := M }, H ++ (F ++ T),
        8192, 4096 * hwm, .idle⟩)) ∧
      commitMetaSt M5 B5 mp (commitOf mv) (mv.txid'.toNat % 2) ∧
      (∀ k < 8192, ∃ b, B5[k]? = some (b, true)) ∧ B5.length = M5.size ∧
      (∀ k < 4096, B5[4096 * hwm + k]? = (dataPage mv.pgid' v)[k]?.map (·, true)) ∧
      M5.maps = m4.maps ∧ M5.size = m4.size ∧ M5.ok = true ∧ (B5.map Prod.fst).take 8192 = mp := by
  obtain ⟨h16, h4, h5, h8, -⟩ := arith_hwm hwm m4.size h2 hsz
  obtain ⟨hH, hF, hHc, hccS, hblS, htkS, -⟩ :=
    syncK_facts hc hl (by rw [hmp, hpg]) h2 h4 h30 h16
  have e := split3_eq bs4 8192 (4096 * hwm) h8
  have hsk : ∀ k < 4096, (bs4.take 8192 ++ ((bs4.drop 8192).take (4096 * hwm - 8192) ++
      syncedBytes m4 (bs4.drop (4096 * hwm))))[4096 * hwm + k]? =
        (dataPage mv.pgid' v)[k]?.map (·, true) := by
    intro k hk
    have hl1 : (bs4.take 8192 ++ (bs4.drop 8192).take (4096 * hwm - 8192)).length = 4096 * hwm := by
      simp only [List.length_append, List.length_take, List.length_drop]; clear hpg ht hboot hd hb hmv; omega
    rw [← List.append_assoc, List.getElem?_append_right
      (l₁ := bs4.take 8192 ++ (bs4.drop 8192).take (4096 * hwm - 8192)) (by rw [hl1]; clear hpg ht hboot hd hb hmv; omega),
      hl1, show 4096 * hwm + k - 4096 * hwm = k by clear hpg ht hboot hd hb hmv; omega]
    unfold syncedBytes
    rw [if_pos hok, List.getElem?_map, List.getElem?_drop, ← hd k hk, Option.map_map]
    rfl
  have hdur : ∀ k < 8192, ∃ b, (bs4.take 8192 ++ ((bs4.drop 8192).take (4096 * hwm - 8192) ++
      syncedBytes m4 (bs4.drop (4096 * hwm))))[k]? = some (b, true) ∧
      (m4.syncedKeep (4096 * hwm) (bs4.drop (4096 * hwm)) 0 (bs4.take 8192)).dur[k]? =
        some (some b) := by
    intro k hk
    have hk' : k < (bs4.take 8192).length := by rw [hH]; exact hk
    obtain ⟨b, hb'⟩ := hc.metas k hk
    have hx : (bs4.take 8192)[k]? = some (b, true) := by rw [List.getElem?_take, if_pos hk, hb']
    refine ⟨b, by rw [List.getElem?_append_left hk', hx], ?_⟩
    rw [syncedKeep_dur _ _ _ _ k hk']
    rw [List.getElem?_eq_getElem hk', Option.some.injEq] at hx
    rw [hx]
  have hc5 := commitMetaSt_of (v := v) hccS (by rw [htkS, hmp, hmv]; exact ht)
    (by rw [htkS, hmp, hpg]; exact hb) (by rw [htkS, hmp, hpg]; exact h5)
    (by rw [htkS, hmp, hpg, hmv]; exact hsk) (by rw [htkS, hmp, hmv]; exact hboot) hdur
  rw [htkS, hmp, hmv] at hc5
  refine ⟨_, _, _, _, _, e.symm, hH, hF, hHc, rfl, commitClean_okS _ hblS rfl hccS,
    commitClean_okS _ (by rw [e]; exact hl) rfl
      (commitClean_meta (m := m4) (by rw [e]; exact hc) rfl rfl),
    fun M => writer_okS (m := { m4 with ok := false }) 8192 (4096 * hwm) (by rw [e]; exact hl)
      (commitClean_meta (m := m4) (by rw [e]; exact hc) rfl rfl) M,
    hc5, fun k hk => (hdur k hk).imp fun _ h => h.1, hblS, hsk, rfl, rfl, hok, by rw [htkS, hmp]⟩

/-- The meta write succeeded: the meta pages are the new ones `mp'`; its sync (`Fdatasync`,
`csSynced true`) leaves `commitClean` at `mp'`, whose root page is the data page. -/
theorem metaS_facts {p : GoString} {M5 m6 : OsMeta} {B5 bs6 : List (w8 × Bool)} {hwm i : Nat}
    {mp mp' : List w8} {mv : Meta} {v : w64}
    (hl6 : bs6.length = m6.size) (hs6 : m6.size = M5.size) (hok6 : m6.ok = true)
    (h2 : 2 ≤ hwm) (hsz : (hwm + 2) * 4096 ≤ M5.size) (h30 : M5.size ≤ 2 ^ 30)
    (hi : i = 1 - mv.txid'.toNat % 2)
    (hout : ∀ k, (k < 4096 * i ∨ 4096 * i + 4096 ≤ k) → bs6[k]? = B5[k]?)
    (hd : ∀ j < 4096, (bs6[4096 * i + j]?).map Prod.fst = (metaPageOf mv)[j]?)
    (ht5 : (B5.map Prod.fst).take 8192 = mp) (hml : mp.length = 8192)
    (hpg5 : ∀ k < 4096, B5[4096 * hwm + k]? = (dataPage mv.pgid' v)[k]?.map (·, true))
    (hmp' : mp' = setPage mp i (metaPageOf mv))
    (hok' : metaPagesOk mp') (hcur' : curMeta mp' = commitOf mv) (hcr' : curRoot mp' = hwm)
    (hcp' : curPgid mp' = hwm + 1) (hct' : (curMeta mp').txid'.toNat = mv.txid'.toNat + 1)
    (hboot : bootOk (mv.txid'.toNat + 1) (some v)) (htxm : mv.txid'.toNat < hwm) :
    ∃ (M7 : OsMeta) (B7 H F T : List (w8 × Bool)),
      bs6 = H ++ (F ++ T) ∧ H.length = 8192 ∧ 8192 + F.length = 4096 * hwm ∧
      csSynced true m6 H F T 8192 (4096 * hwm) = ⟨M7, B7, 8192, 4096 * hwm, .idle⟩ ∧
      dbOk p (some ⟨M7, B7, 8192, 4096 * hwm, .idle⟩) ∧
      commitClean M7 B7 ∧ B7.length = M7.size ∧ (B7.map Prod.fst).take 8192 = mp' ∧
      (B7.drop (4096 * hwm)).take (4096 * (hwm + 1) - 4096 * hwm) =
        (dataPage mv.pgid' v).map (·, true) ∧
      M7.maps = m6.maps ∧ M7.size = m6.size ∧ M7.ok = true ∧
      dbOk p (some ⟨M7, B7, 8192, 4096 * (hwm + 1), .idle⟩) ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ M7 with maps := M }, B7, 8192, 4096 * (hwm + 1), .idle⟩)) ∧
      (bs6.take 8192).map Prod.fst = mp' := by
  obtain ⟨h16, h4, h5, h8, h44⟩ := arith_hwm hwm M5.size h2 hsz
  have hi2 : i < 2 := by rw [hi]; omega
  have hD := metaPageOf_length mv
  have hdp := dataPage_length mv.pgid' v
  have hbl : 8192 ≤ bs6.length := by rw [hl6, hs6]; exact Nat.le_trans h8 h4
  have e := split3_eq bs6 8192 (4096 * hwm) h8
  have hH : (bs6.take 8192).length = 8192 := by rw [List.length_take]; omega
  have hF : 8192 + ((bs6.drop 8192).take (4096 * hwm - 8192)).length = 4096 * hwm := by
    rw [List.length_take, List.length_drop]; omega
  -- the meta pages
  have hX : (bs6.take 8192).map Prod.fst = mp' := by
    rw [hmp']
    apply List.ext_getElem?; intro k
    rw [setPage_getElem? _ _ _ _ hml hi2 hD, List.getElem?_map, List.getElem?_take]
    by_cases hk : k < 8192
    · rw [if_pos hk]
      by_cases hw : 4096 * i ≤ k ∧ k < 4096 * i + 4096
      · rw [if_pos hw, ← hd (k - 4096 * i) (by omega), show 4096 * i + (k - 4096 * i) = k by omega]
      · rw [if_neg hw, hout k (by omega), ← ht5, List.getElem?_take, if_pos hk, List.getElem?_map]
    · rw [if_neg hk, if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl
  -- the data page
  have hpg6 : ∀ k < 4096, (bs6.take 8192 ++ ((bs6.drop 8192).take (4096 * hwm - 8192) ++
      bs6.drop (4096 * hwm)))[4096 * hwm + k]? = (dataPage mv.pgid' v)[k]?.map (·, true) := by
    intro k hk
    rw [e, hout _ (.inr (by omega)), hpg5 k hk]
  obtain ⟨hcc7, hbl7⟩ := metaSynced_commitClean (m := m6) (B := dataPage mv.pgid' v) hok6
    (by rw [e, hl6]) hH hX hok' (by
      unfold curInSlot
      rw [hct', show (mv.txid'.toNat + 1) % 2 = i by omega, hcur', hmp',
        fileMeta_setPage_same mp i _ hml hi2 hD, metaPageOf_meta])
    (by rw [hcp', hs6]; exact h5) (by rw [hs6]; exact h30) (by rw [hs6]; exact h16) hdp
    (by rw [hcr']; exact hpg6) (by rw [hct', dataPage_val]; exact hboot)
    ⟨by rw [hct']; omega, by rw [hct', hcp']; omega⟩
  have hsH : syncedBytes m6 (bs6.take 8192) = (bs6.take 8192).map (fun x => (x.1, true)) := by
    unfold syncedBytes; rw [if_pos hok6]
  have hsl : (syncedBytes m6 (bs6.take 8192)).length = 8192 := by rw [syncedBytes_length, hH]
  have htk7 : ((syncedBytes m6 (bs6.take 8192) ++ ((bs6.drop 8192).take (4096 * hwm - 8192) ++
      bs6.drop (4096 * hwm))).map Prod.fst).take 8192 = mp' := by
    rw [List.map_append, List.take_append_of_le_length (by simp [hsl]),
      List.take_of_length_le (by simp [hsl]), hsH, List.map_map, ← hX]; rfl
  have hpg7 : ((syncedBytes m6 (bs6.take 8192) ++ ((bs6.drop 8192).take (4096 * hwm - 8192) ++
      bs6.drop (4096 * hwm))).drop (4096 * hwm)).take (4096 * (hwm + 1) - 4096 * hwm) =
        (dataPage mv.pgid' v).map (·, true) := by
    apply List.ext_getElem?; intro k
    rw [List.getElem?_take, List.getElem?_drop, List.getElem?_map]
    by_cases hk : k < 4096 * (hwm + 1) - 4096 * hwm
    · have hx := List.getElem?_append_right (l₁ := bs6.take 8192)
        (l₂ := (bs6.drop 8192).take (4096 * hwm - 8192) ++ bs6.drop (4096 * hwm))
        (i := 4096 * hwm + k) (by rw [hH]; omega)
      rw [hH] at hx
      rw [if_pos hk, List.getElem?_append_right (l₁ := syncedBytes m6 (bs6.take 8192)) (by omega),
        hsl, ← hx, hpg6 k (by omega)]
    · rw [if_neg hk, List.getElem?_eq_none (by rw [hdp]; omega)]; rfl
  have hl7 : (syncedBytes m6 (bs6.take 8192) ++ ((bs6.drop 8192).take (4096 * hwm - 8192) ++
      bs6.drop (4096 * hwm))).length = m6.size := hbl7
  have hfb : 4096 * (hwm + 1) ≤ m6.size := by rw [hs6]; exact h5
  refine ⟨_, _, _, _, _, e.symm, hH, hF, rfl, commitClean_okS _ hl7 rfl hcc7, hcc7, hbl7, htk7,
    hpg7, rfl, rfl, hok6, commitClean_okS _ hl7 rfl hcc7,
    writer_okS (m := m6.synced 0 (bs6.take 8192)) 8192 (4096 * (hwm + 1)) hl7 hcc7, hX⟩

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

/-- The data page out of the frozen pages up to the new high water mark. -/
theorem frozen_page (p : GoString) (B : List (w8 × Bool)) (hwm : Nat) (h2 : 2 ≤ hwm)
    (hl : 4096 * (hwm + 1) ≤ B.length) :
    osBytes (GF := GF) p 8192 DFrac.discard ((B.drop 8192).take (4096 * (hwm + 1) - 8192)) ⊢
      osBytes (GF := GF) p (4096 * hwm) DFrac.discard
        ((B.drop (4096 * hwm)).take (4096 * (hwm + 1) - 4096 * hwm)) := by
  have e : (B.drop 8192).take (4096 * (hwm + 1) - 8192) = (B.drop 8192).take (4096 * hwm - 8192) ++
      (B.drop (4096 * hwm)).take (4096 * (hwm + 1) - 4096 * hwm) := by
    rw [show 4096 * (hwm + 1) - 8192 = (4096 * hwm - 8192) + (4096 * (hwm + 1) - 4096 * hwm) by omega,
      List.take_add, List.drop_drop, show 8192 + (4096 * hwm - 8192) = 4096 * hwm by omega]
  rw [e]
  iintro H
  icases (osBytes_app p 8192 DFrac.discard _ _).1 $$ H with ⟨-, H2⟩
  rw [List.length_take, List.length_drop, show 8192 + min (4096 * hwm - 8192) (B.length - 8192) =
    4096 * hwm by omega]
  iexact H2

/-- `rwRC` from the writer's state with a mapping, not failed. -/
theorem rwRC_of (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m : OsMeta) (bs : List (w8 × Bool))
    (hok : m.ok = true) :
    writerStC (GF := GF) γ γc db f fd p mp false hwm (some (base, len, γm)) m bs ⊢
      rwRC (GF := GF) γ γc db f fd p := by
  unfold writerStC rwRC
  iintro ⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, Hst⟩
  ileft
  iexists mp, false, hwm, some (base, len, γm), m, bs
  iframe Hcur Hmap Hout Hflds Hw Hcls
  isplitr
  · ipureintro; exact fun _ => hok
  · dsimp only; iexact Hst

end lemmas


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.bboltfs.Assumptions]

set_option maxHeartbeats 1000000 in
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
  replace hhwm : HideEq (curPgid mp) hwm := hhwm
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
  have hpgb : HideEq (curPgid ((bs.map Prod.fst).take 8192)) hwm := by
    rw [hmp]; exact hhwm
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
      (by rw [show curPgid ((bs.map Prod.fst).take 8192) = hwm from hpgb, hbl]; exact Hwf.2.1)
      8192 (4096 * hwm)
    rw [← hlen64] at hobl
    rw [← Hmaps]
    wp_apply wp_Truncate f fd p _ (W64 (len : Int)) _ ⟨p, true, true⟩ dbCrashN γc (dbOk p) m' bs
        8192 (4096 * hwm) len hfd rfl hlenI (by rw [hlen64]; exact Hsz)
        (fun b l h => by rw [Hmaps] at h; simp at h; omega) dbCrashN_disj hobl
        $$ [Hf Hfd Hcs Hmc] as %err ⟨Hf, Hfd, Hres⟩
    · iframe; iframe #
    simp only [hlen64]
    have h4 := Hwf.2.1
    have h4len : 4096 * hwm ≤ len := by omega
    have h16len : 4 * 4096 ≤ len := Nat.le_trans hsz.1 Hsz
    have hl30 : len ≤ 2 ^ 30 := hsz.2.2
    obtain ⟨M3, B3, H, F, T, hsplit, hH, hF, hHc, hsyn, hcc3, hs3, hm3, ho3, ht3, hok3, hok3', hokF,
      hokF', hokG, hokT⟩ := grow_facts (p := p) hcc hbl hpgb h2 h4 Hsz hsz.2.2 hsz.1
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
    have hgs : (m'.grown len).size = len := rfl
    have hgm : (m'.grown len).maps = m'.maps := rfl
    icases Hres with (⟨%Herr, Hg⟩ | ⟨%Herr, (Hg | ⟨Hcs, Hmc⟩)⟩)
    · subst Herr
      iunfold csGrownOwn at Hg
      icases Hg with ⟨Hcs, Hc, -⟩
      rw [Hmaps]
      ihave Hwc := hcells _ (mcells_single (GF := GF) base len m'.size len _ Hsz (Nat.le_refl _)).1
        $$ [Hwc4 Hlow Hc]
      · iframe
      (try wp_auto)
      rw [hsplit]
      wp_apply wp_Sync f fd p _ _ ⟨p, true, true⟩ dbCrashN γc (dbOk p) (m'.grown len) H F T 8192
          (4096 * hwm) false hH hF (fun _ => hHc) dbCrashN_disj (by rw [hsyn]; exact hok3') hokF
        $$ [Hf Hfd Hcs] as %err2 ⟨Hf, Hfd, Hres2⟩
      · iframe; iframe #
      icases Hres2 with (⟨%Herr2, Hcs⟩ | ⟨%Herr2, Hcs⟩)
      · subst Herr2
        (try wp_auto)
        rw [hsyn]
        ileft
        isplitr
        · ipureintro; rfl
        iexists M3, B3
        have hA : 4096 * hwm ≤ M3.size := by rw [hs3]; exact h4len
        have hB : 4 * 4096 ≤ M3.size := by rw [hs3]; exact h16len
        have hC : M3.size ≤ 2 ^ 30 := by rw [hs3]; exact hl30
        have hD : (B3.map Prod.fst).take 8192 = mp := by rw [ht3, hmp]
        have hE : M3.maps = {[base := len]} := by rw [hm3]; exact Hmaps
        have hF' : M3.size ≤ len := by rw [hs3]; exact Nat.le_refl _
        have hG : M3.ok = true := by rw [ho3]; exact Hok'
        have hH' : (hwm + 2) * 4096 ≤ M3.size := by rw [hs3]; exact Hlen
        ihave Hws := writerStC_mk γ γc db f fd p mp false hwm base len γm M3 B3 len
            ⟨⟨h2, hA, hok3, fun _ => ⟨hD, hcc3, hs3.symm, hfd, hB, hC, hl30⟩⟩, hE, hF', Hbase, Hl41⟩
          $$ [Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc]
        · iframe Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc; iframe #
        iframe
        ipureintro
        exact ⟨hG, hH'⟩
      · cases err2 with
        | nil => exact absurd rfl Herr2
        | ok ie =>
        (try wp_auto)
        iright
        iexists GoInterface.ok ie
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, Herr2⟩
        iapply commitErrC_mk γ γc db f fd p mp hwm base len γm { m'.grown len with ok := false }
          (H ++ (F ++ T)) m'.size _ hwm ⟨by rw [← Hmaps]; rfl, Nat.le_refl len,
            Hbase, Hl41, h2, h4len, hokF'⟩
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
      iapply commitErrC_mk γ γc db f fd p mp hwm base len γm (m'.grown len)
        (bs ++ List.replicate (len - m'.size) ((0 : w8), false)) m'.size _ hwm
        ⟨by rw [hgm]; exact Hmaps, Nat.le_refl len, Hbase, Hl41, h2, h4len, hokG⟩
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
      iapply commitErrC_mk γ γc db f fd p mp hwm base len γm (ftMeta m' len) bs
        m'.size _ hwm ⟨Hmaps, Hsz, Hbase, Hl41, h2, h4, hokT⟩
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
  iintro (⟨%Hbv, %m2, %bs2, Hws, %Hm2, db, «$res0», v, pg, m, Hown⟩ |
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
  clear hcc hmp Hwf hsz Hmaps Hsz Hok' Hlen Hcw hbl hpgb hsZ
  iunfold writerStC at Hws
  icases Hws with ⟨Hcur, Hmap, Hout, Hflds, Hw, Hcls, %Hstp, Htok, #Hinv, Hwc⟩
  iunfold writerFileC at Hw
  icases Hw with ⟨%fsz, Hfsz, Hdsz, Hf, Hfd, Hcs, %Hwf⟩
  obtain ⟨hmp, hcc, rfl, -, h16, h30, hl30⟩ := Hwf.2.2.2 rfl
  obtain ⟨Hmaps, Hsz, -, -⟩ := Hstp
  obtain ⟨Hok2, Hgrow⟩ := Hm2
  icases csOwn_wf' _ _ _ $$ Hcs with ⟨Hcs, %Hcw⟩
  have hbl : bs2.length = m2.size := Hcw.1
  have h2 := Hwf.1
  obtain ⟨-, h4', -, h8, hin⟩ := arith_hwm hwm m2.size h2 Hgrow
  dsimp only [mapLen]
  (try wp_auto)
  -- the data page
  wp_apply (wp_slice_make2 (V := w8) (W64 4096)) as %buf ⟨Hbuf, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hblen := ownSlice_len $$ Hbuf
  ihave %Hpos := ownSlice_ptr_pos buf _ _ (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hbuf
  have hbl' : sint.Z buf.len = 4096 := by
    have h1 := Hblen.1; have h2 := Hblen.2; simp only [List.length_replicate] at h1
    have : sint.nat buf.len = (sint.Z buf.len).toNat := rfl
    omega
  wp_apply wp_pageAt
  · ipureintro; rw [hbl']; exact ⟨Hpos, by decide, by decide⟩
  rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0]
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) buf _ _ Hpos $$ Hbuf
    with ⟨Hb, Hclose⟩
  simp only [flatMap_encode_w8, show zero_val w8 = (0 : w8) from rfl]
  rw [zeroPage_val]
  icases (valPage_view _ _ _ _ _ Hpos).1 $$ Hb with ⟨Hh, Hv, Hr⟩
  (try wp_auto)
  rw [ite_eq_left (by rw [hbl']; decide), show sliceIndexRef w8 (sint.Z (W64 16)) buf = buf.ptr +ₗ 16 from
    sliceIndexRef_byte_W64 buf 16 Hpos (by decide)]
  (try wp_auto)
  ihave Hh : buf.ptr ↦ dataHdr mv.pgid' $$ [Hh]
  · simp only [dataHdr, pageHdr]; iexact Hh
  ihave Hb := (valPage_view buf.ptr _ _ v _ Hpos).2 $$ [Hh Hv Hr]
  · iframe
  ihave Hbuf := Hclose $$ %(dataPage mv.pgid' v) [] [Hb]
  · ipureintro; rw [dataPage_length, ← zeroPage_val, List.length_replicate]
  · simp only [dataPage]; iexact Hb
  -- its write, at the high water mark (inside the file)
  have hoff : (mv.pgid' * W64 4096).toNat = 4096 * hwm := by
    rw [BitVec.toNat_mul, hpg]; show hwm * 4096 % 2 ^ 64 = _; omega
  have hoffI : 0 ≤ (mv.pgid' * W64 4096).toInt := by
    rw [BitVec.toInt_eq_toNat_cond, hoff]; split <;> omega
  have hdl := dataPage_length mv.pgid' v
  icases (writerCells_top base hwm len).1 $$ Hwc with ⟨Hwc4, Htop⟩
  rw [arith_sub4096 (4096 * hwm) len (Nat.le_trans hin Hsz)]
  icases cellsAny_split _ _ _ _ $$ Htop with ⟨Hpc, Htop⟩
  ihave Hpc := (mcellsAny_single (GF := GF) base len (4096 * hwm) (4096 * hwm + 4096)
    (Nat.le_add_right _ _) (Nat.le_trans hin Hsz)).2 $$ [Hpc]
  · rw [Nat.add_sub_cancel_left]; iexact Hpc
  rw [← Hmaps]
  have hobl := fun fb => dataW_obl (p := p) (D := dataPage mv.pgid' v) hcc hbl
    (by rw [hmp, show curPgid mp = hwm from hhwm]; exact Nat.le_refl _) h4'
    (by rw [hdl]; exact Nat.le_trans hin h30) 8192 fb
  rw [← hoff] at hobl
  wp_apply wp_WriteAt f fd p (DFrac.own (1 : Qp).half) buf (dataPage mv.pgid' v) (DFrac.own 1)
      (mv.pgid' * W64 4096) (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ dbCrashN γc (dbOk p) m2 bs2
      8192 (4096 * hwm) rfl hoffI (by rw [hdl]; decide) (by rw [hdl]; decide) dbCrashN_disj
      (.inr (by rw [hoff]; exact Nat.le_refl _)) (hobl _) $$ [Hf Hbuf Hfd Hcs Hpc]
    as %n %err ⟨Hf, Hbuf, Hfd, Hpc, %m4, %bs4, %Hres, Hcs⟩
  · simp only [cfLo]
    rw [hoff, hdl, Nat.min_eq_left h4']
    iframe Hf Hbuf Hfd Hcs Hpc; iframe #
  rw [hoff, dataPage_length] at Hres
  simp only [cfLo]
  rw [hoff, hdl, Nat.min_eq_left h4']
  icases (mcellsAny_single (GF := GF) base len (4096 * hwm) (4096 * hwm + 4096)
    (Nat.le_add_right _ _) (Nat.le_trans hin Hsz)).1 $$ [Hpc] with Hpc
  · rw [Hmaps]; iexact Hpc
  rw [Nat.add_sub_cancel_left]
  obtain ⟨hR, ⟨rfl, rfl, -, hd4⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · obtain ⟨-, -, -, hs4, hm4, -, hok4⟩ := dataW_after (p := p) hcc hbl hmp hhwm h2 hin hdl h30 hR
    cases err with
    | nil => exact absurd rfl hne
    | ok ie =>
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact hne
    ihave Herr := dataErrC γ γc db f fd p mp hwm base len γm m4 bs4 m2.size _ hwm
      ⟨by rw [hm4]; exact Hmaps, by rw [hs4]; exact Hsz, Hbase, Hl41, h2, by rw [hs4]; exact hin,
        hok4⟩
      $$ [Hown Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc4 Hpc Htop]
    · iframe Hown Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc4 Hpc Htop; iframe #
    iunfold commitErrC at Herr
    iexact Herr
  obtain ⟨hcc4, hbl4, hmp4, hs4, hm4, ho4, -⟩ := dataW_after (p := p) hcc hbl hmp hhwm h2 hin hdl h30 hR
  (try wp_auto)
  wp_apply wp_Fd f fd p _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  obtain ⟨M5, B5, H, F, T, hsplit, hH, hF, hHc, hsyn, hok5, hokF5, hokF5', hc5, hcl5, hbl5, hpg5,
    hm5, hs5, ho5, ht5⟩ := dataS_facts (p := p) (v := v) hcc4 hbl4 hmp4 hmv hhwm h2
      (by rw [ho4]; exact Hok2) (by rw [hs4]; exact Hgrow) (by rw [hs4]; exact h30) hd4 Ht Hb Hboot
  rw [hsplit]
  wp_apply wp_Fdatasync fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ dbCrashN γc (dbOk p) m4 H F T
      8192 (4096 * hwm) false hH hF (fun _ => hHc) dbCrashN_disj (by rw [hsyn]; exact hok5) hokF5
    $$ [Hfd Hcs] as %e ⟨Hfd, Hs⟩
  · iframe Hfd Hcs; iframe #
  icases Hs with (⟨%He, Hcs⟩ | ⟨%He, Hcs⟩)
  rotate_left
  · unfold errnoErr; rw [if_neg He]
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    ihave Herr := dataErrC γ γc db f fd p mp hwm base len γm { m4 with ok := false } (H ++ (F ++ T))
      m2.size _ hwm ⟨by rw [← hm4] at Hmaps; exact Hmaps, by rw [← hs4] at Hsz; exact Hsz, Hbase,
        Hl41, h2, by rw [← hs4] at hin; exact hin, hokF5'⟩
      $$ [Hown Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc4 Hpc Htop]
    · iframe Hown Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc4 Hpc Htop; iframe #
    iunfold commitErrC at Herr
    iexact Herr
  subst He
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  rw [hsyn]
  -- the meta page
  wp_apply (wp_slice_make2 (V := w8) (W64 4096)) as %mbuf ⟨Hmb, -⟩
  · ipureintro; decide
  (try wp_auto)
  ihave %Hmblen := ownSlice_len $$ Hmb
  ihave %Hmbpos := ownSlice_ptr_pos mbuf _ _
    (List.ne_nil_of_length_pos (by rw [List.length_replicate]; decide)) $$ Hmb
  have hmbl : sint.Z mbuf.len = 4096 := by
    have h1 := Hmblen.1; have h2 := Hmblen.2; simp only [List.length_replicate] at h1
    have : sint.nat mbuf.len = (sint.Z mbuf.len).toNat := rfl
    omega
  wp_apply wp_pageAt
  · ipureintro; rw [hmbl]; exact ⟨Hmbpos, by decide, by decide⟩
  rw [show sint.Z (W64 0) = 0 from rfl, loc_add_0]
  icases ownSlice_bytes_acc go.uint8 (.scalar _ _ .isPlainScalar_uint8) mbuf _ _ Hmbpos $$ Hmb
    with ⟨Hb, Hmclose⟩
  simp only [flatMap_encode_w8, show zero_val w8 = (0 : w8) from rfl]
  icases (zeroPage_meta_view _ _ Hmbpos).1 $$ [Hb] with ⟨Hh, Hmm, Hr⟩
  · iexact Hb
  (try wp_auto)
  wp_apply wp_write m_ptr mbuf.ptr (nextMeta mv) _ _ $$ [m Hh Hmm] as ⟨m, Hh, Hmm⟩
  · iframe m Hh Hmm; ipureintro; exact ⟨Hmpos, Hmbpos⟩
  (try wp_auto)
  -- `metalock`: the handle is not failed (the writer's `cur`)
  ihave #Hpkg2 := Hpkg
  iunfold pkgFacts at Hpkg2
  icases Hpkg2 with ⟨#Hsync, -⟩
  wp_apply sync.Mutex.wp_Lock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p) $$ [$Hmeta $Hsync]
    as ⟨Hlocked, HR⟩
  iunfold metaRC at HR
  icases HR with ⟨%b, %mpx, %hwmx, %c, %T, Hfl, Hcm, Hcls2, Hauth, Hout2, Hrest⟩
  icombine Hcur Hcm gives % ⟨_, Hceq⟩
  cases Hceq
  dsimp only
  icases Hrest with ⟨Hfail, %Hmeta', Hlast, Hown2, %B0, #HB0, #Htx0, %HT0⟩
  obtain ⟨-, -, HTn⟩ := Hmeta'
  (try wp_auto)
  -- the meta buffer holds the meta page
  ihave Hh : mbuf.ptr ↦ metaHdrOf mv $$ [Hh]
  · simp only [metaHdrOf, pageHdr, nextMeta]; iexact Hh
  ihave Hmm : (mbuf.ptr +ₗ 16) ↦ commitOf mv $$ [Hmm]
  · simp only [commitOf, nextMeta]; iexact Hmm
  ihave Hb := (pageMeta_view mbuf.ptr _ _ _ _ Hmbpos).2 $$ [Hh Hmm Hr]
  · iframe Hh Hmm Hr
  ihave Hmb := Hmclose $$ %(metaPageOf mv) [] [Hb]
  · ipureintro; rw [metaPageOf_length, List.length_replicate]
  · simp only [metaPageOf]; iexact Hb
  -- the meta cells out of the invariant
  imod metas_out γ p base len γm mp hwm $$ [Hinv Htok Hcur Hout Hout2]
    with ⟨Htok, Hcur, Hout, Hout2, Hc0, Hc1⟩
  · iframe Htok Hcur Hout Hout2; iframe #
  have hml : mp.length = 8192 := Hok.1
  have hi1 := slot_next mv.txid'
  obtain ⟨i, hi⟩ : ∃ i, i = 1 - mv.txid'.toNat % 2 := ⟨_, rfl⟩
  rw [← hi] at hi1
  have hi2 : i < 2 := by rw [hi]; exact Nat.lt_of_le_of_lt (Nat.sub_le _ _) (by decide)
  have hoffm : ((mv.txid' + W64 1) % W64 2 * W64 4096).toNat = 4096 * i := by
    rw [BitVec.toNat_mul, hi1]; show i * 4096 % 2 ^ 64 = _; omega
  have hoffmI : 0 ≤ ((mv.txid' + W64 1) % W64 2 * W64 4096).toInt := by
    rw [BitVec.toInt_eq_toNat_cond, hoffm]; split <;> omega
  -- meta page `i`'s cells
  ihave Hc0 := cellsB_any base 16 _ $$ Hc0
  ihave Hc1 := cellsB_any base 4112 _ $$ Hc1
  rw [show ((mp.drop 16).take 64).length = 64 by simp only [List.length_take, List.length_drop, hml]; rfl,
    show ((mp.drop 4112).take 64).length = 64 by simp only [List.length_take, List.length_drop, hml]; rfl]
  icases (hdrTails base).1 $$ Hwc4 with ⟨T0, T1⟩
  icases (pick_page (fun k => iprop(hdrTail (GF := GF) base k ∗ cellsAny (GF := GF) base (4096 * k + 16) 64))
    i hi2).1 $$ [T0 T1 Hc0 Hc1] with ⟨⟨Ti, Hci⟩, Hother⟩
  · iframe T0 T1 Hc0 Hc1
  ihave Hpi := metaPage_cells base i $$ [Ti Hci]
  · iframe Ti Hci
  -- its write
  have hs5' : M5.size = m2.size := by rw [hs5, hs4]
  have hm5' : M5.maps = {[base := len]} := by rw [hm5, hm4]; exact Hmaps
  have h8' : 8192 ≤ M5.size := by rw [hs5']; exact Nat.le_trans h8 h4'
  have hil : 4096 * i + 4096 ≤ M5.size := by
    have : 4096 * i + 4096 ≤ 8192 := by omega
    exact Nat.le_trans this h8'
  ihave Hpi := (mcellsAny_single (GF := GF) base len (4096 * i) (4096 * i + 4096)
    (Nat.le_add_right _ _) (by rw [← hs5'] at Hsz; exact Nat.le_trans hil Hsz)).2 $$ [Hpi]
  · rw [Nat.add_sub_cancel_left]; iexact Hpi
  rw [← hm5']
  have hobl2 := fun fb => metaW_obl (p := p) hc5 hbl5 (metaPageOf_length mv) h8' hcl5
    (metaPageOf_meta mv) 8192 fb
  rw [← hi, ← hoffm] at hobl2
  wp_apply wp_WriteAt f fd p (DFrac.own (1 : Qp).half) mbuf (metaPageOf mv) (DFrac.own 1)
      ((mv.txid' + W64 1) % W64 2 * W64 4096) (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ dbCrashN γc
      (dbOk p) M5 B5 8192 (4096 * hwm) rfl hoffmI (by rw [metaPageOf_length]; decide)
      (by rw [metaPageOf_length]; decide) dbCrashN_disj
      (.inl (by rw [hoffm, metaPageOf_length]; omega)) (hobl2 _)
      $$ [Hf Hmb Hfd Hcs Hpi]
    as %n2 %err2 ⟨Hf, Hmb, Hfd, Hpi, %m6, %bs6, %Hres2, Hcs⟩
  · simp only [cfLo]
    rw [hoffm, metaPageOf_length, Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) hil)]
    iframe Hf Hmb Hfd Hcs Hpi; iframe #
  rw [hoffm, metaPageOf_length] at Hres2
  simp only [cfLo]
  rw [hoffm, metaPageOf_length, Nat.min_eq_left (Nat.le_trans (Nat.le_add_right _ _) hil)]
  icases (mcellsAny_single (GF := GF) base len (4096 * i) (4096 * i + 4096)
    (Nat.le_add_right _ _) (by rw [← hs5'] at Hsz; exact Nat.le_trans hil Hsz)).1 $$ [Hpi] with Hpi
  · rw [hm5']; iexact Hpi
  rw [Nat.add_sub_cancel_left]
  obtain ⟨hR2, hsucc2⟩ := Hres2
  rw [hi] at hR2
  obtain ⟨hM6, hc6, hl6, hm6, hs6, ho6, hout6, hok6, hok6F, hok6F'⟩ :=
    metaW_after (p := p) (hwm := hwm) hc5 hbl5 (metaPageOf_length mv) h8' hcl5 (metaPageOf_meta mv) hR2
  have hlen8 : 8192 ≤ len := Nat.le_trans h8' (by rw [hs5']; exact Hsz)
  -- the meta cells against the writer's half of the meta pages
  icases metaPage_cells_split base i $$ Hpi with ⟨Ti, Hci⟩
  icases (pick_page (fun k => iprop(hdrTail (GF := GF) base k ∗ cellsAny (GF := GF) base (4096 * k + 16) 64))
    i hi2).2 $$ [Ti Hci Hother] with ⟨⟨T0, Hc0⟩, ⟨T1, Hc1⟩⟩
  · iframe Ti Hci Hother
  rw [show 4096 * 0 + 16 = 16 from rfl, show 4096 * 1 + 16 = 4112 from rfl]
  iunfold cellsAny at Hc0 Hc1
  icases Hc0 with ⟨%v0, Hc0⟩
  icases Hc1 with ⟨%v1, Hc1⟩
  icases (csOwn_idle _ _ _ rfl).1 $$ Hcs with ⟨Hv, ⟨Hm6, Hb6⟩, %Hwf6⟩
  have hfb6 : 4096 * hwm ≤ bs6.length := by rw [hl6, hs6, hs5']; exact h4'
  icases (writer_thrBytes p m6 bs6 hwm h2 hfb6).1 $$ Hb6 with ⟨Hmx, Htl⟩
  have hb6 : m6.maps !! base = some len := by rw [hm6, hm5']; exact GMap.lookup_insert _ _ _
  have hXl : (bs6.take 8192).length = 8192 := by
    rw [List.length_take, hl6, hs6]; exact Nat.min_eq_left h8'
  iapply window_agree _ rfl p _ m6 base len hb6 (by simp) _ _ (bs6.take 8192) 16 64 v0
    (by rw [hXl]; decide) (Nat.le_trans (by decide) hlen8) $$ Hos Hm6 Hmx Hc0
  iintro Hm6 Hmx Hc0
  iapply window_agree _ rfl p _ m6 base len hb6 (by simp) _ _ (bs6.take 8192) 4112 64 v1
    (by rw [hXl]; decide) (Nat.le_trans (by decide) hlen8) $$ Hos Hm6 Hmx Hc1
  iintro Hm6 Hmx Hc1
  ihave Hcs := (csOwn_idle (GF := GF) p γc ⟨m6, bs6, 8192, 4096 * hwm, .idle⟩ rfl).2
    $$ [Hv Hm6 Hmx Htl]
  · iframe Hv Hm6
    isplitl
    · iapply (writer_thrBytes p _ bs6 hwm h2 hfb6).2; iframe
    · ipureintro; exact Hwf6
  rcases hsucc2 with ⟨rfl, rfl, -, hd6⟩ | ⟨rfl, hne2⟩
  rotate_left
  · -- the meta `WriteAt` failed: fail the handle
    cases err2 with
    | nil => exact absurd rfl hne2
    | ok ie =>
    (try wp_auto)
    have hl1 : (((bs6.take 8192).map Prod.fst).drop 16 |>.take 64).length = 64 := by
      simp only [List.length_take, List.length_drop, List.length_map, hXl]; rfl
    imod meta_failC γ db p base len γm mp hwm
        ((((bs6.take 8192).map Prod.fst).drop 16).take 64 ++
          (((bs6.take 8192).map Prod.fst).drop 4112).take 64)
        (metas_length _ hXl) T _ _ _ c
        $$ [Htok Hcur Hcm Hout Hout2 Hc0 Hc1 Hfl Hfail Hauth Hown2 Hown Hcls2]
      with ⟨HR, #Hfailed, Hown, Htok, Hcur, Hout⟩
    · rw [List.take_left' hl1, List.drop_left' hl1]
      iframe Htok Hcur Hcm Hout Hout2 Hc0 Hc1 Hfl Hfail Hauth Hown2 Hown Hcls2; iframe #
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hlocked HR]
    · iexact HR
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact hne2
    ihave Herr := dataErrTC γ γc db f fd p mp hwm base len γm m6 bs6 m2.size _ _
      ⟨by rw [hm6]; exact hm5', by rw [hs6, hs5']; exact Hsz, Hbase, Hl41, h2,
        by rw [hs6, hs5']; exact hin, hok6⟩
      $$ [Hown Hfailed Hcur Hmap Hout Hflds Hcls Htok T0 T1 Hpc Htop Hfsz Hdsz Hf Hfd Hcs]
    · iframe Hown Hcur Hmap Hout Hflds Hcls Htok T0 T1 Hpc Htop Hfsz Hdsz Hf Hfd Hcs; iframe #
    iunfold commitErrC at Herr
    iexact Herr
  (try wp_auto)
  -- the meta write succeeded: `Fdatasync` the meta pages
  wp_apply wp_Fd f fd p _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  obtain ⟨hok', hcur', hcr', hcp', hct'⟩ := metaPagesOk_commit mp i (metaPageOf mv) Hok
    (by rw [hmv]; exact Ht) (by rw [show curPgid mp = hwm from hhwm]; exact Hb) hi2
    (metaPageOf_length mv) (by rw [metaPageOf_meta, commitMeta, hmv])
  generalize hmp' : setPage mp i (metaPageOf mv) = mp' at hok' hcur' hcr' hcp' hct'
  rw [commitMeta, hmv] at hcur'
  rw [hmv] at hct'
  rw [show curPgid mp = hwm from hhwm] at hcr' hcp'
  have hmpl : mp'.length = 8192 := hok'.1
  obtain ⟨M7, B7, H6, F6, T6, hsplit6, hH6, hF6, hsyn6, hok7, hcc7, hbl7, htk7, hpg7, hm7, hs7, ho7,
    hok7', hok7M, hX⟩ := metaS_facts (p := p) (v := v) hl6 hs6 (by rw [ho6, ho5]) h2
      (by rw [hs5']; exact Hgrow) (by rw [hs5']; exact h30) hi (by rw [hi]; exact hout6) hd6 ht5 hml
      hpg5 hmp'.symm hok' hcur' hcr' hcp' hct' Hboot
      (by have h := hcc4.tx.2; rw [hmp4, hmv, show curPgid mp = hwm from hhwm] at h; exact h)
  rw [hX]
  rw [hsplit6] at hok6F hok6F'
  rw [hsplit6]
  wp_apply wp_Fdatasync fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ dbCrashN γc (dbOk p) m6 H6 F6
      T6 8192 (4096 * hwm) true hH6 hF6 (fun h => by cases h) dbCrashN_disj
      (by rw [hsyn6]; exact hok7) hok6F' $$ [Hfd Hcs] as %e2 ⟨Hfd, Hs⟩
  · iframe Hfd Hcs; iframe #
  have hl1 : ((mp'.drop 16).take 64).length = 64 := by
    simp only [List.length_take, List.length_drop, hmpl]; rfl
  have hmc : ((mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64).length = 128 := by
    simp only [List.length_append, List.length_take, List.length_drop, hmpl]; rfl
  icases Hs with (⟨%He2, Hcs⟩ | ⟨%He2, Hcs⟩)
  rotate_left
  · -- the meta's sync failed: fail the handle
    unfold errnoErr; rw [if_neg He2]
    (try wp_auto)
    imod meta_failC γ db p base len γm mp hwm ((mp'.drop 16).take 64 ++ (mp'.drop 4112).take 64)
        hmc T _ _ _ c $$ [Htok Hcur Hcm Hout Hout2 Hc0 Hc1 Hfl Hfail Hauth Hown2 Hown Hcls2]
      with ⟨HR, #Hfailed, Hown, Htok, Hcur, Hout⟩
    · rw [List.take_left' hl1, List.drop_left' hl1]
      iframe Htok Hcur Hcm Hout Hout2 Hc0 Hc1 Hfl Hfail Hauth Hown2 Hown Hcls2; iframe #
    wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
      $$ [$Hmeta $Hsync $Hlocked HR]
    · iexact HR
    (try wp_auto)
    iapply HΦ
    iright
    isplitr
    · ipureintro; simp
    ihave Herr := dataErrTC γ γc db f fd p mp hwm base len γm { m6 with ok := false } (H6 ++ (F6 ++ T6))
      m2.size _ _
      ⟨by show m6.maps = _; rw [hm6]; exact hm5', by show m6.size ≤ len; rw [hs6, hs5']; exact Hsz,
        Hbase, Hl41, h2, by show _ ≤ m6.size; rw [hs6, hs5']; exact hin, hok6F⟩
      $$ [Hown Hfailed Hcur Hmap Hout Hflds Hcls Htok T0 T1 Hpc Htop Hfsz Hdsz Hf Hfd Hcs]
    · iframe Hown Hcur Hmap Hout Hflds Hcls Htok T0 T1 Hpc Htop Hfsz Hdsz Hf Hfd Hcs; iframe #
    iunfold commitErrC at Herr
    iexact Herr
  subst He2
  unfold errnoErr; rw [if_pos rfl]
  (try wp_auto)
  rw [hsyn6]
  -- freeze the data page: its `pageIs`, its cells holding it
  have hs7' : M7.size = m2.size := by rw [hs7, hs6, hs5']
  have hm7' : M7.maps = {[base := len]} := by rw [hm7, hm6]; exact hm5'
  have hfb7 : 4096 * (hwm + 1) ≤ M7.size := by
    rw [hs7']; exact Nat.le_trans (by rw [Nat.mul_add, Nat.mul_one]; exact Nat.le_refl _) hin
  imod cs_freeze dbCrashN p γc (dbOk p) M7 B7 8192 (4096 * hwm) 8192 (4096 * (hwm + 1)) ⊤
      (fun _ _ => CoPset.mem_full) (Nat.le_trans h8 (Nat.mul_le_mul_left _ (Nat.le_succ _))) hfb7
      (fun _ => ⟨Nat.le_refl _, Nat.mul_le_mul_left _ (Nat.le_succ _)⟩) hok7' $$ Hci Hcs
    with ⟨Hcs, Hfr⟩
  ihave Hpg := frozen_page p B7 hwm h2 (by rw [hbl7]; exact hfb7) $$ Hfr
  rw [hpg7]
  imod pageIs_of p hwm DFrac.discard (dataPage mv.pgid' v) (dataPage_length _ _) $$ Hpg with #HBp
  icases (csOwn_idle _ _ _ rfl).1 $$ Hcs with ⟨Hv, ⟨Hm7, Hb7⟩, %Hwf7⟩
  have hb7 : M7.maps !! base = some len := by rw [hm7']; exact GMap.lookup_insert _ _ _
  iunfold pageIs at HBp
  icases HBp with ⟨-, #Hpg⟩
  iunfold cellsAny at Hpc
  icases Hpc with ⟨%vf, Hpc⟩
  have hplen : 4096 * hwm + ((dataPage mv.pgid' v).map (·, true)).length ≤ len := by
    rw [List.length_map, dataPage_length]; exact Nat.le_trans hin Hsz
  iapply cellsR_agree _ rfl p _ M7 base len hb7 DFrac.discard (by simp) _
    ((dataPage mv.pgid' v).map (·, true)) (4096 * hwm) vf hplen $$ Hos Hm7 Hpg [Hpc]
  · rw [List.length_map, dataPage_length]; iexact Hpc
  iintro Hm7 - Hpc
  rw [show ((dataPage mv.pgid' v).map (·, true)).map Prod.fst = dataPage mv.pgid' v by
    rw [List.map_map]; exact List.map_id _]
  ihave Hcs := (csOwn_idle (GF := GF) p γc ⟨M7, B7, 8192, 4096 * (hwm + 1), .idle⟩ rfl).2
    $$ [Hv Hm7 Hb7]
  · iframe Hv Hm7 Hb7; ipureintro; exact Hwf7
  imod pageIs_of p hwm DFrac.discard (dataPage mv.pgid' v) (dataPage_length _ _) $$ Hpg with #HBp
  -- publish: the meta pages, page `hwm` committed, the owner, the last txid, the transaction
  imod metas_publish γ p base len γm mp mp' hwm (dataPage mv.pgid' v)
    (by rw [hs7'] at hfb7; exact Nat.le_trans hfb7 Hsz) h2 hmpl
    $$ [Htok Hcur Hcm Hout Hout2 Hc0 Hc1 Hpc] with ⟨Htok, Hcur, Hcm, Hout, Hout2⟩
  · iframe Htok Hcur Hcm Hout Hout2 Hc0 Hc1 Hpc; iframe #
  iunfold dbOwner at Hown
  imod ghostVar_update_halves (mv.txid'.toNat + 1, hwm + 1) γ.own _ _ $$ Hown Hown2 with ⟨Hown, Hown2⟩
  imod mono_nat_own_update (mv.txid'.toNat + 1) (by rw [hmv]; omega) $$ Hlast with ⟨Hlast, #Hlb⟩
  imod ghost_map_insert_persist (mv.txid'.toNat + 1) (some v : Option w64) (HTn _ (by rw [hmv]; omega))
    $$ Hauth with ⟨Hauth, #Htx⟩
  wp_apply sync.Mutex.wp_Unlock db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p)
    $$ [$Hmeta $Hsync $Hlocked Hfl Hcm Hcls2 Hauth Hout2 Hfail Hlast Hown2]
  · iunfold metaRC
    iexists false, mp', hwm + 1, c, T.insert (mv.txid'.toNat + 1) (some v)
    iframe Hfl Hcm Hcls2 Hauth Hout2
    dsimp only
    rw [hct']
    iframe Hfail Hlast Hown2
    isplitr
    · ipureintro
      refine ⟨hok', hcp'.symm, fun k hk => ?_⟩
      rw [GMap.lookup_insert_ne _ _ (by omega)]
      exact HTn k (by rw [hmv]; omega)
    iexists dataPage mv.pgid' v
    rw [hcr', dataPage_val]
    iframe HBp
    isplitr
    · unfold dbTx; iframe Htx; ipureintro; exact Hvp
    · ipureintro; exact GMap.lookup_insert _ _ _
  (try wp_auto)
  -- `rwlock`'s resource at the new meta pages, the high water mark one page on
  iapply HΦ
  ileft
  isplitr
  · ipureintro; rfl
  ihave Hwc4 := (hdrTails base).2 $$ [T0 T1]
  · iframe T0 T1
  ihave Hwc := (writerCells_top base (hwm + 1) len).2 $$ [Hwc4 Htop]
  · rw [show 4096 * (hwm + 1) = 4096 * hwm + 4096 by rw [Nat.mul_add, Nat.mul_one],
      show len - (4096 * hwm + 4096) = len - 4096 * hwm - 4096 by rw [Nat.sub_sub]]
    iframe Hwc4 Htop
  isplitl [Hfsz Hdsz Hmap Hflds Hcls Hf Hfd Hcs Htok Hcur Hout Hwc]
  · iapply rwRC_of γ γc db f fd p mp' (hwm + 1) base len γm M7 B7 ho7
    iapply writerStC_mk γ γc db f fd p mp' false (hwm + 1) base len γm M7 B7 m2.size
      ⟨⟨Nat.le_succ_of_le h2, hfb7, hok7M, fun _ => ⟨htk7, hcc7, hs7'.symm, hfd,
          by rw [hs7']; exact h16, by rw [hs7']; exact h30, hl30⟩⟩,
        hm7', by rw [hs7']; exact Hsz, Hbase, Hl41⟩
    iframe; iframe #
  isplitl [Hown]
  · unfold dbOwner; iexact Hown
  isplitr
  · unfold dbTx; iframe Htx; ipureintro; exact Hvp
  · unfold dbLast; iexact Hlb

end proof

end bboltfs
end EtcdGrove
end Perennial
