/- Lean-first (no Rocq counterpart). The proof of `db.commit(m, v)`'s crash-aware spec
(`DB.commit.specCrash`): `DB__commit.lean`'s, step by step, over the crash invariant of the file.
The writer holds its idle state `⟨m, bs, 8192, 4096 * hwm, .idle⟩` (`writerFileC`); each file
operation is its crash-aware spec, whose obligations are, for the states it may pass through:
- `Truncate`, its `Sync` and the data page's `WriteAt` and `Fdatasync`: `commitClean` (the meta
  pages and the current root page untouched, `commitClean_of_prefix`);
- the meta page's `WriteAt` and a failed `Fdatasync` of it: `commitMetaSt` (`commitMetaSt_of`
  after the data page's sync, which keeps the clean meta pages among the durable bytes known, and
  `commitMetaSt_wreach`), with `cacheSlot` of the slot written (`metaW_reach`);
- a successful `Fdatasync` of the meta page: `commitClean` at the new meta pages, whose root page
  is the data page (`bootOk` of it is the spec's premise).
Then `cs_freeze` freezes the data page (its `pageIs` and its cells' agreement come from its
discarded copy). -/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__commitCrash
public import Spec.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmapCrash
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__commit
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.DB__mmapCrash
public import Proof.os.CrashStSpec
public import Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.CrashKc

@[expose] public section

noncomputable section

-- the kernel's check of some `omega` proofs below recurses deeply
set_option maxRecDepth 20000

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs
open Fs

section pure
variable [GooseExts]


/-- An equation `omega` does not look into (`curPgid` of meta pages: `omega` unfolds it). -/
def HideEq (a b : Nat) : Prop := a = b

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

/-- `commitClean` of a state whose bytes below the high water mark are the same. -/
theorem commitClean_of_prefix {m m' : OsMeta} {bs bs' : List ByteG} (h : commitClean m bs)
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
    fun k hk => by rw [hpre k (by omega)]; exact h.metas k hk, fun k hk => ?_, by rw [ht]; exact h.tx,
    fun k h1 h2 => ?_⟩
  · rw [ht, take_drop_congr hpre' (by omega)]; exact h.boot
  · rw [ht, hpre _ (by omega)]; exact h.root k hk
  · rw [ht] at h2; rw [hpre k h2]; exact h.frz k h1 h2

theorem commitClean_hwm {m : OsMeta} {bs : List ByteG} (h : commitClean m bs) :
    2 ≤ curRoot ((bs.map Prod.fst).take 8192) ∧
      curRoot ((bs.map Prod.fst).take 8192) < curPgid ((bs.map Prod.fst).take 8192) :=
  ⟨h.ok.2.2.1, h.ok.2.2.2.1⟩

/-- Bytes kept below `fb` (`H ++ F`), the rest replaced. -/
theorem keep_prefix {α : Type} (H F T X : List α) (k : Nat) (hk : k < H.length + F.length) :
    (H ++ (F ++ X))[k]? = (H ++ (F ++ T))[k]? := by
  rw [← List.append_assoc, ← List.append_assoc]
  generalize hA : H ++ F = A
  have : A.length = H.length + F.length := by rw [← hA, List.length_append]
  rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]

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

/-- `commitMetaSt` does not look at the mappings or `ok`. -/
theorem commitMetaSt_meta {m m' : OsMeta} {bs : List ByteG} {mp : List w8} {N : Meta}
    {s : Nat} (h : commitMetaSt m bs mp N s) (hhi : m'.hi = m.hi) (hlo : m'.lo = m.lo) :
    commitMetaSt m' bs mp N s :=
  ⟨h.s2, h.sTx, hhi ▸ h.hi, hlo ▸ h.lo, h.ok, h.slot, hlo ▸ h.pg, h.boot, h.root, h.metaS, h.tx,
    h.nValid, h.nTx, h.nTxS, h.nRoot, h.nRootPg, h.nTxPg, h.nPg, hlo ▸ h.nPgLo, h.nBoot, h.nPage, h.frz⟩

theorem take8192_congr {l l' : List ByteG} {N : Nat} (h : ∀ k < N, l'[k]? = l[k]?)
    (hN : 8192 ≤ N) : (l'.map Prod.fst).take 8192 = (l.map Prod.fst).take 8192 :=
  take_congr' (fun k hk => by rw [List.getElem?_map, List.getElem?_map, h k hk]) hN

theorem arith_hwm (hwm s : Nat) (h2 : 2 ≤ hwm) (hsz : (hwm + 2) * 4096 ≤ s) :
    4 * 4096 ≤ s ∧ 4096 * hwm ≤ s ∧ 4096 * (hwm + 1) ≤ s ∧ 8192 ≤ 4096 * hwm ∧
      4096 * hwm + 4096 ≤ s := by
  omega

theorem arith_sub4096 (a b : Nat) (h : a + 4096 ≤ b) : b - a = 4096 + (b - a - 4096) := by
  omega

/-- The slot the next commit writes. -/
theorem slot_next (t : w64) :
    ((t + W64 1) % W64 2).toNat = 1 - t.toNat % 2 := by
  rw [BitVec.toNat_umod, BitVec.toNat_add]
  show ((t.toNat + 1) % 2 ^ 64) % 2 = _
  omega

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



/-! ### Syncs -/

/-- The bytes `bs`, durable. -/
abbrev durAll (bs : List ByteG) : List ByteG := bs.map fun x => durB x.1

theorem durAll_fst (bs : List ByteG) : (durAll bs).map Prod.fst = bs.map Prod.fst := by
  simp [durAll, List.map_map, Function.comp_def]

theorem durAll_length (bs : List ByteG) : (durAll bs).length = bs.length := by simp [durAll]

theorem durAll_dur {bs : List ByteG} {k : Nat} {b : w8} (h : bs[k]? = some (durB b)) :
    (durAll bs)[k]? = some (durB b) := by
  simp [durAll, List.getElem?_map, h]

theorem durAll_of {bs : List ByteG} {k : Nat} (hk : k < bs.length) :
    ∃ b, (durAll bs)[k]? = some (durB b) :=
  ⟨bs[k].1, by simp [durAll, List.getElem?_map, List.getElem?_eq_getElem hk]⟩

/-- **A sync, the frozen bytes durable**: every byte durable. -/
theorem csSynced_eq (m : OsMeta) (H F T : List ByteG) (fa fb : Nat)
    (hF : ∀ y ∈ F, y = durB y.1) :
    csSynced m H F T fa fb = ⟨m.synced, durAll (H ++ (F ++ T)), fa, fb, .idle⟩ := by
  have e : F.map (fun x => durB x.1) = F := by
    apply List.ext_getElem (by simp); intro k h1 h2
    simp only [List.getElem_map]; exact (hF _ (List.getElem_mem h2)).symm
  show (⟨m.synced, H.map (fun x => durB x.1) ++ (F ++ T.map (fun x => durB x.1)), fa, fb, .idle⟩ : CSt) = _
  rw [durAll, List.map_append, List.map_append, e]

/-- `commitClean` of the bytes made durable. -/
theorem commitClean_durAll {m M : OsMeta} {bs : List ByteG} (h : commitClean m bs)
    (hhi : M.hi ≤ 2 ^ 30) (hlo : 4 * 4096 ≤ M.lo)
    (hpg : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ M.lo) : commitClean M (durAll bs) := by
  have ht : (durAll bs).map Prod.fst = bs.map Prod.fst := durAll_fst bs
  refine ⟨hhi, hlo, by rw [ht]; exact h.ok, by rw [ht]; exact h.slot, by rw [ht]; exact hpg,
    by rw [ht]; exact h.boot, fun k hk => ?_, fun k hk => ?_, by rw [ht]; exact h.tx,
    fun k h1 h2 => ?_⟩
  · obtain ⟨b, hb⟩ := h.metas k hk; exact ⟨b, durAll_dur hb⟩
  · rw [ht]; obtain ⟨b, hb⟩ := h.root k hk; exact ⟨b, durAll_dur hb⟩
  · rw [ht] at h2; obtain ⟨b, hb⟩ := h.frz k h1 h2; exact ⟨b, durAll_dur hb⟩

/-- The bytes `[8192, 4096 hwm)` (the frozen ones) of a `commitClean` state, durable. -/
theorem commitClean_frozen {m : OsMeta} {bs : List ByteG} {hwm : Nat} (h : commitClean m bs)
    (hpg : curPgid ((bs.map Prod.fst).take 8192) = hwm) :
    ∀ y ∈ (bs.drop 8192).take (4096 * hwm - 8192), y = durB y.1 := by
  intro y hy
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
  simp only [List.length_take, List.length_drop] at hk
  obtain ⟨b, hb⟩ := h.frz (8192 + k) (by omega) (by rw [hpg]; omega)
  have e : ((bs.drop 8192).take (4096 * hwm - 8192))[k]? = some (durB b) := by
    rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop, hb]
  rw [List.getElem?_eq_getElem (by simp; omega), Option.some.injEq] at e
  rw [e]

/-! ### `Truncate` -/

/-- The states a growing `Truncate` reaches keep `commitClean`. -/
theorem treach_commitClean {m m' : OsMeta} {bs bs' : List ByteG} {sz : Nat}
    (h : commitClean m bs) (hl : bs.length = m.size) (hsz : sz ≤ 2 ^ 30) (hg : m.size ≤ sz)
    (h16 : 4 * 4096 ≤ m.size) (hpgs : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m.size)
    (hR : TReach m bs sz m' bs') :
    commitClean m' bs' ∧ bs'.length = m'.size ∧ m.size ≤ m'.size ∧ m'.size ≤ sz ∧
      m'.maps = m.maps := by
  have hhi := h.hi
  have hlo := h.lo
  have hpg := h.pg
  cases hR with
  | refl => exact ⟨h, hl, Nat.le_refl _, hg, rfl⟩
  | ann =>
    refine ⟨commitClean_of_prefix h (fun _ _ => rfl) (by simp only [announce_hi]; omega)
      (by simp only [announce_lo]; omega) (by simp only [announce_lo]; omega),
      by rw [announce_size]; exact hl, by rw [announce_size]; exact Nat.le_refl _,
      by rw [announce_size]; exact hg,
      announce_maps _ _ _ _⟩
  | grown n zs hzl =>
    refine ⟨commitClean_of_prefix h (fun k hk => List.getElem?_append_left (by omega))
      (by show max m.hi sz ≤ _; omega) (by show _ ≤ min m.lo sz; omega)
      (by show _ ≤ min m.lo sz; omega), ?_, by show m.size ≤ sz; exact hg, Nat.le_refl _,
      announce_maps m (min m.size sz) (max m.size sz) sz⟩
    show _ = sz
    simp only [List.length_append, List.length_map, hzl]; omega

/-- **`Truncate`'s obligation** (`os.File.Truncate.specCrashS`). -/
theorem trunc_obl {i : Ino} {m : OsMeta} {bs : List ByteG} {sz : Nat}
    (h : commitClean m bs) (hl : bs.length = m.size) (hsz : sz ≤ 2 ^ 30) (hg : m.size ≤ sz)
    (h16 : 4 * 4096 ≤ m.size) (hpgs : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m.size)
    (fa fb : Nat) (hfa : fa ≤ fb) (hfb : fb ≤ m.size) :
    ∀ m' bs', TReach m bs sz m' bs' →
      dbOk (some (i, ⟨m', bs', fa, fb, .idle⟩)) ∧
        ∀ t n, dbOk (some (i, ⟨m', bs', fa, fb, .trunc t sz n⟩)) := by
  intro m' bs' hR
  obtain ⟨hc, hl', h1, h2, -⟩ := treach_commitClean h hl hsz hg h16 hpgs hR
  have hpre : (bs'.map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 := by
    cases hR with
    | refl => rfl
    | ann => rfl
    | grown n zs hzl =>
      exact take8192_congr (N := 8192) (fun k hk => List.getElem?_append_left (by omega)) (Nat.le_refl _)
  have hpgs' : 4096 * curPgid ((bs'.map Prod.fst).take 8192) ≤ m'.size := by rw [hpre]; omega
  have hfb' : fb ≤ m'.size := by omega
  have hhi := hc.hi
  refine ⟨commitClean_okS ⟨m', bs', fa, fb, .idle⟩ ⟨hl', hfa, hfb', trivial⟩ trivial hc
    (Nat.le_refl _) (by show m'.hi ≤ 2 ^ 30; exact hhi) (fun _ _ => trivial), fun t n => ?_⟩
  have hlo := hc.lo
  have hpg := hc.pg
  have hrp := hc.ok.2.2.2.1
  have hr2 := hc.ok.2.2.1
  have hcc : commitClean { m' with lo := min m'.lo sz } bs' :=
    commitClean_of_prefix hc (fun _ _ => rfl) hhi (by show _ ≤ min m'.lo sz; omega)
      (by show _ ≤ min m'.lo sz; omega)
  refine commitClean_okS ⟨m', bs', fa, fb, .trunc t sz n⟩ ⟨hl', hfa, hfb', h2⟩ trivial hcc
    (by show min m'.lo sz ≤ (m'.announce (min m'.size sz) (max m'.size sz) sz).lo
        simp only [announce_lo]; omega)
    (by show (m'.announce (min m'.size sz) (max m'.size sz) sz).hi ≤ 2 ^ 30
        simp only [announce_hi]; omega) (fun k hk => ?_)
  show ¬ inRange (min m'.size sz) (max m'.size sz) k = true
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
  simp only at hk
  unfold curRoot curPgid at *
  rcases hk with hk | ⟨-, hk⟩ <;> omega

/-! ### The data page's write -/

/-- What the data page's write (at the high water mark or past it, inside the file) reaches:
`commitClean`, the bytes below it unchanged. -/
theorem dataW_reach {m m' : OsMeta} {bs bs' : List ByteG} {off : Nat} {D : List w8}
    {nn : Nat} (h : commitClean m bs) (hl : bs.length = m.size)
    (hoff : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ off) (hoffs : off ≤ m.size)
    (hD : off + D.length ≤ 2 ^ 30) (h30 : m.size ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size)
    (hR : WReach m bs off D nn m' bs') :
    commitClean m' bs' ∧ WIn m bs off D m' bs' ∧ off + nn ≤ m'.size ∧
      (bs'.map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 := by
  obtain ⟨hW, hS, -⟩ := hR.wIn hl hoffs
  have hw := commitClean_hwm h
  have hpre : ∀ k < 4096 * curPgid ((bs.map Prod.fst).take 8192), bs'[k]? = bs[k]? :=
    fun k hk => hW.out k (.inl (by omega))
  have hhi := h.hi
  have hlo := h.lo
  have hpg := h.pg
  have h1 := hW.lo
  have h2 := hW.hi
  simp only [wT] at h1 h2
  exact ⟨commitClean_of_prefix h hpre (by omega) (by omega) (by omega), hW, hS,
    take8192_congr hpre (by omega)⟩

/-- **The data page's write's obligation** (`os.File.WriteAt.specCrashS`): it misses the meta
pages and the current root page. -/
theorem dataW_obl {i : Ino} {m : OsMeta} {bs : List ByteG} {off : Nat} {D : List w8}
    (h : commitClean m bs) (hl : bs.length = m.size)
    (hoff : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ off) (hoffs : off ≤ m.size)
    (hD : off + D.length ≤ 2 ^ 30) (h30 : m.size ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size)
    (fa fb : Nat) (hfab : fa ≤ fb) (hfb : fb ≤ m.size) (hfo : fb ≤ off) :
    ∀ nn m' bs', WReach m bs off D nn m' bs' →
      dbOk (some (i, ⟨m', bs', fa, fb, .idle⟩)) ∧ (nn < D.length → ∀ t n,
        PwFresh m' bs' (off + nn) (D.drop nn) n →
        dbOk (some (i, ⟨m', bs', fa, fb, .write t (off + nn) (D.drop nn) n⟩))) := by
  intro nn m' bs' hR
  obtain ⟨hc, hW, hS, ht⟩ := dataW_reach h hl hoff hoffs hD h30 h16 hR
  have hs1 := hW.sz1
  have hs2 := hW.sz2
  simp only [wT] at hs2
  have hfb' : fb ≤ m'.size := by omega
  have hhi := hc.hi
  refine ⟨commitClean_okS ⟨m', bs', fa, fb, .idle⟩ ⟨hW.len, hfab, hfb', trivial⟩ trivial hc
    (Nat.le_refl _) (by show m'.hi ≤ 2 ^ 30; exact hhi) (fun _ _ => trivial), fun hlt t n _ => ?_⟩
  have hlo := hc.lo
  have hpg := hc.pg
  have hoff' : 4096 * curPgid ((bs'.map Prod.fst).take 8192) ≤ off := by rw [ht]; exact hoff
  have hdl : (D.drop nn).length = D.length - nn := List.length_drop ..
  have hcc : commitClean { m' with lo := (cfMeta m' (off + nn) (D.drop nn).length).lo } bs' :=
    commitClean_of_prefix hc (fun _ _ => rfl) hhi
      (by simp only [cfMeta, announce_lo]; omega) (by simp only [cfMeta, announce_lo]; omega)
  refine commitClean_okS ⟨m', bs', fa, fb, .write t (off + nn) (D.drop nn) n⟩
    ⟨hW.len, hfab, hfb', .inr (by show fb ≤ off + nn; omega)⟩ hS hcc (Nat.le_refl _)
    (by show (cfMeta m' (off + nn) (D.drop nn).length).hi ≤ 2 ^ 30
        simp only [cfMeta, announce_hi]; omega) (fun k hk => ?_)
  show ¬ inRange (min (off + nn) m'.size) (off + nn + (D.drop nn).length) k = true
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
  rw [ht] at hk
  have hrp := h.ok.2.2.2.1
  have hr2 := h.ok.2.2.1
  unfold curRoot curPgid at *
  rcases hk with hk | ⟨-, hk⟩ <;> omega

/-- What the data page's write reaches, as the writer's state. -/
theorem dataW_after {i : Ino} {m2 m4 : OsMeta} {bs2 bs4 : List ByteG} {hwm : Nat}
    {mp D : List w8} (hcc : commitClean m2 bs2) (hbl : bs2.length = m2.size)
    (hmp : (bs2.map Prod.fst).take 8192 = mp) (hpg : curPgid mp = hwm) (h2 : 2 ≤ hwm)
    (h4 : 4096 * hwm + 4096 ≤ m2.size) (hD : D.length = 4096) (h30 : m2.size ≤ 2 ^ 30)
    (h16 : 4 * 4096 ≤ m2.size) {nn : Nat} (hR : WReach m2 bs2 (4096 * hwm) D nn m4 bs4) :
    commitClean m4 bs4 ∧ bs4.length = m4.size ∧ (bs4.map Prod.fst).take 8192 = mp ∧
      m4.size = m2.size ∧ m4.maps = m2.maps ∧ True ∧
      (∀ M : GMap Loc Nat, dbOk (some (i, ⟨{ m4 with maps := M }, bs4, 8192, 4096 * hwm, .idle⟩))) := by
  obtain ⟨hc, hW, -, ht⟩ := dataW_reach hcc hbl (by rw [hmp, hpg]; exact Nat.le_refl _) (by omega)
    (by rw [hD]; omega) h30 h16 hR
  have hs1 := hW.sz1
  have hs2 := hW.sz2
  simp only [wT, hD] at hs2
  refine ⟨hc, hW.len, by rw [ht, hmp], by omega, hW.maps, trivial,
    writer_okS (m := m4) 8192 (4096 * hwm) hW.len (by omega) (by omega) hc⟩

/-! ### The meta write -/

/-- `commitMetaSt` of a state whose bytes out of the page `1 - s` are the same. -/
theorem commitMetaSt_out {m m' : OsMeta} {bs bs' : List ByteG} {mp : List w8} {N : Meta}
    {s : Nat} (h : commitMetaSt m bs mp N s)
    (hout : ∀ k, (k < 4096 * (1 - s) ∨ 4096 * (1 - s) + 4096 ≤ k) → bs'[k]? = bs[k]?)
    (hhi : m'.hi ≤ 2 ^ 30) (hlo : 4 * 4096 ≤ m'.lo) (hpg : 4096 * curPgid mp ≤ m'.lo)
    (hnp : 4096 * N.pgid'.toNat ≤ m'.lo) : commitMetaSt m' bs' mp N s := by
  have hs2 := h.s2
  have hpage : ∀ r, 2 ≤ r → ((bs'.map Prod.fst).drop (4096 * r)).take 4096 =
      ((bs.map Prod.fst).drop (4096 * r)).take 4096 := fun r hr =>
    window_congr fun k h1 _ => by
      rw [List.getElem?_map, List.getElem?_map, hout k (.inr (by omega))]
  have hR2 := h.ok.2.2.1
  have hNR := h.nRoot
  refine ⟨hs2, h.sTx, hhi, hlo, h.ok, h.slot, hpg,
    by rw [hpage _ hR2]; exact h.boot, fun k hk => by rw [hout _ (.inr (by omega))]; exact h.root k hk,
    fun k hk => by rw [hout _ (by omega)]; exact h.metaS k hk, h.tx, h.nValid, h.nTx, h.nTxS, hNR,
    h.nRootPg, h.nTxPg, h.nPg, hnp, by rw [hpage _ hNR]; exact h.nBoot,
    fun k hk => by rw [hout _ (.inr (by omega))]; exact h.nPage k hk,
    fun k h1 h2 => by rw [hout _ (.inr (by omega))]; exact h.frz k h1 h2⟩

/-- **The meta write's obligation** (`os.File.WriteAt.specCrashS`): from a synced state (every
byte durable) whose meta pages are `mp`, writing the page `D` (whose meta is `N`) at slot
`1 - s`. Every state it reaches keeps `commitMetaSt` and knows slot `1 - s` as the old meta,
then `N` (`SlotK`). -/
theorem metaW_obl {i : Ino} {m : OsMeta} {B : List w8} {mp : List w8} {N : Meta}
    {s : Nat} {D : List w8} (h : commitMetaSt m (B.map durB) mp N s) (hl : B.length = m.size)
    (hD : D.length = 4096) (h8 : 4 * 4096 ≤ m.size) (h30 : m.size ≤ 2 ^ 30)
    (hmp : B.take 8192 = mp) (hw : pageMeta D = N) (hlos : m.lo ≤ m.size) (fa fb : Nat)
    (hfa : 8192 ≤ fa) (hfab : fa ≤ fb) (hfb : fb ≤ m.size) :
    ∀ nn m' bs', WReach m (B.map durB) (4096 * (1 - s)) D nn m' bs' →
      (∀ M : GMap Loc Nat, dbOk (some (i, ⟨{ m' with maps := M }, bs', fa, fb, .idle⟩))) ∧
      (nn < D.length → ∀ t n,
        PwFresh m' bs' (4096 * (1 - s) + nn) (D.drop nn) n →
        dbOk (some (i, ⟨m', bs', fa, fb, .write t (4096 * (1 - s) + nn) (D.drop nn) n⟩))) := by
  intro nn m' bs' hR
  have hs2 := h.s2
  have hl' : (B.map durB).length = m.size := by simp [hl]
  have hoff : 4096 * (1 - s) ≤ m.size := by omega
  obtain ⟨hW, hS, -⟩ := hR.wIn hl' hoff
  have hK := wreach_kw 0 0 hR hl' hoff
  have hs1 := hW.sz1
  have hsz2 := hW.sz2
  have hhi0 := h.hi
  have hlo0 := h.lo
  have h1 := hW.lo
  have h2 := hW.hi
  simp only [wT, hD] at h1 h2 hsz2
  have hout : ∀ k, (k < 4096 * (1 - s) ∨ 4096 * (1 - s) + 4096 ≤ k) → bs'[k]? = (B.map durB)[k]? :=
    fun k hk => hW.out k (by rw [hD]; exact hk)
  have hpg0 := h.pg
  have hnp0 := h.nPgLo
  have hM : commitMetaSt m' bs' mp N s :=
    commitMetaSt_out h hout (by omega) (by omega) (by omega) (by omega)
  -- the slot written, from what the states know
  have hX : ∀ k < 64, (⟨m, B.map durB, 0, 0, .idle⟩ : CSt).kc (4096 * (1 - s) + 16 + k) =
      some [((slotOf B (1 - s)).getD k 0, 0)] := fun k hk => by
    rw [kc_synced hl (by omega), slotOf_getD _ _ _ hk]
  have hvX : metaValid (decode (slotOf B (1 - s)) : Meta) →
      (decode (slotOf B (1 - s)) : Meta) = fileMeta mp (1 - s) ∨
        (decode (slotOf B (1 - s)) : Meta) = N := fun _ => .inl (by
    rw [slotOf_fileMeta _ _ (by omega), ← hmp, fileMeta_take _ _ _ (by omega)])
  have hvD : metaValid (decode ((List.range 64).map fun k =>
      D.getD (4096 * (1 - s) + 16 + k - 4096 * (1 - s)) 0) : Meta) →
      (decode ((List.range 64).map fun k => D.getD (4096 * (1 - s) + 16 + k - 4096 * (1 - s)) 0) : Meta) =
        fileMeta mp (1 - s) ∨
      (decode ((List.range 64).map fun k => D.getD (4096 * (1 - s) + 16 + k - 4096 * (1 - s)) 0) : Meta) =
        N := fun _ => .inr (by
    rw [← hw, pageMeta]; congr 1
    apply List.ext_getElem (by simp; omega); intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop]
    simp only [List.length_map, List.length_range] at h1
    rw [show 4096 * (1 - s) + 16 + k - 4096 * (1 - s) = 16 + k by omega, getD_lt _ (by omega)])
  have hfacts : ∀ st : CSt, st.Wf → BusyOk st → st.bs = bs' →
      ((∀ b c, (⟨m, B.map durB, 0, 0, .idle⟩ : CSt).kc b = some c → st.kc b = some c) ∨
        KWr (⟨m, B.map durB, 0, 0, .idle⟩ : CSt).kc st.kc (4096 * (1 - s)) D) →
      ∀ M : OsMeta, commitMetaSt M st.bs mp N s → M.lo ≤ st.vmeta.lo → st.vmeta.hi ≤ 2 ^ 30 →
      (∀ k, (4096 * s + 16 ≤ k ∧ k < 4096 * s + 80 ∨
        (4096 * curRoot mp ≤ k ∧ k < 4096 * curRoot mp + 4096) ∨
        (4096 * N.root'.root'.toNat ≤ k ∧ k < 4096 * N.root'.root'.toNat + 4096)) → st.Misses k) →
      dbOk (some (i, st)) := by
    intro st hwf hbz _ hin M hMst hlo hhi hmiss
    exact commitMeta_okS st hwf hbz hMst hlo hhi hmiss
      ⟨_, _, kw_slotK (slotOf_length _ _) (by omega) (by rw [hD]; omega) hX hin, hvX, hvD⟩
  have hfb' : fb ≤ m'.size := by omega
  refine ⟨fun M => hfacts ⟨{ m' with maps := M }, bs', fa, fb, .idle⟩ ⟨hW.len, hfab, hfb', trivial⟩
    trivial rfl (hK.2.imp (fun h => h.2) id) { m' with maps := M } (commitMetaSt_meta hM rfl rfl)
    (Nat.le_refl _) (by show m'.hi ≤ 2 ^ 30; omega) (fun _ _ => trivial), fun hlt t n hfr => ?_⟩
  obtain ⟨-, hwr⟩ := kw_flight (t := t) hW.len hS hlt hfr hK
  have hdl : (D.drop nn).length = D.length - nn := List.length_drop ..
  refine hfacts ⟨m', bs', fa, fb, .write t (4096 * (1 - s) + nn) (D.drop nn) n⟩
    ⟨hW.len, hfab, hfb', .inl (by show 4096 * (1 - s) + nn + (D.drop nn).length ≤ fa; rw [hdl, hD]; omega)⟩ hS rfl (.inr hwr)
    { m' with lo := (cfMeta m' (4096 * (1 - s) + nn) (D.drop nn).length).lo }
    (commitMetaSt_out hM (fun _ _ => rfl) (by show m'.hi ≤ _; omega)
      (by simp only [cfMeta, announce_lo]; omega) (by simp only [cfMeta, announce_lo]; omega)
      (by simp only [cfMeta, announce_lo]; omega)) (Nat.le_refl _)
    (by show (cfMeta m' (4096 * (1 - s) + nn) (D.drop nn).length).hi ≤ 2 ^ 30
        simp only [cfMeta, announce_hi]; omega) (fun k hk => ?_)
  show ¬ inRange (min (4096 * (1 - s) + nn) m'.size) (4096 * (1 - s) + nn + (D.drop nn).length) k = true
  simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
  have hrp := h.ok.2.2.2.1
  have hr2 := h.ok.2.2.1
  have hnr := h.nRoot
  unfold curRoot at *
  rw [hdl, hD]
  rcases hk with hk | ⟨hk, -⟩ | ⟨hk, -⟩ <;> omega

/-- `metaW_obl` as `os.File.WriteAt.specCrashS` takes it. -/
theorem metaW_obl_spec {i : Ino} {m : OsMeta} {B : List w8} {mp : List w8} {N : Meta}
    {s : Nat} {D : List w8} (h : commitMetaSt m (B.map durB) mp N s) (hl : B.length = m.size)
    (hD : D.length = 4096) (h8 : 4 * 4096 ≤ m.size) (h30 : m.size ≤ 2 ^ 30)
    (hmp : B.take 8192 = mp) (hw : pageMeta D = N) (hlos : m.lo ≤ m.size) (fa fb : Nat)
    (hfa : 8192 ≤ fa) (hfab : fa ≤ fb) (hfb : fb ≤ m.size) :
    ∀ nn m' bs', WReach m (B.map durB) (4096 * (1 - s)) D nn m' bs' →
      dbOk (some (i, ⟨m', bs', fa, fb, .idle⟩)) ∧ (nn < D.length → ∀ t n,
        PwFresh m' bs' (4096 * (1 - s) + nn) (D.drop nn) n →
        dbOk (some (i, ⟨m', bs', fa, fb, .write t (4096 * (1 - s) + nn) (D.drop nn) n⟩))) :=
  fun nn m' bs' hR =>
    let h' := metaW_obl (i := i) h hl hD h8 h30 hmp hw hlos fa fb hfa hfab hfb nn m' bs' hR
    ⟨h'.1 m'.maps, h'.2⟩


end pure


section pure2
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]


/-- After the data page's sync: what the meta write needs (`commitMetaSt`), from `commitClean`,
the data page at the high water mark (clean), and the meta pages durable. -/
theorem commitMetaSt_of {m : OsMeta} {bs : List ByteG} {v : w64} (h : commitClean m bs)
    (ht : (curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat + 1 < 2 ^ 64)
    (hb : (curPgid ((bs.map Prod.fst).take 8192) + 2) * 4096 ≤ 2 ^ 30)
    (hlo : 4096 * (curPgid ((bs.map Prod.fst).take 8192) + 1) ≤ m.lo)
    (hpage : ∀ k < 4096, bs[4096 * curPgid ((bs.map Prod.fst).take 8192) + k]? =
      (dataPage (curMeta ((bs.map Prod.fst).take 8192)).pgid' v)[k]?.map durB)
    (hboot : bootOk ((curMeta ((bs.map Prod.fst).take 8192)).txid'.toNat + 1) (some v)) :
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
  have hmetas := h.metas
  have hfrz := h.frz
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
    ?_, ?_, hfrz⟩
  · intro k hk
    obtain ⟨b, hb'⟩ := hmetas (4096 * ((curMeta mp).txid'.toNat % 2) + 16 + k) (by omega)
    exact ⟨b, by rw [hmpk _ (by omega), hb']; rfl, hb'⟩
  · show ((curMeta mp).txid'.toNat : Int) < ((commitOf (curMeta mp)).txid'.toNat : Int)
    rw [htx]; omega
  · rw [htx, hrtN, hpgB, dataPage_val]; exact hboot
  · intro k hk
    rw [hrtN, hpage k hk, List.getElem?_eq_getElem (by omega)]
    exact ⟨_, rfl⟩



theorem synced_hi_eq (m : OsMeta) : m.synced.hi = m.size := rfl
theorem synced_lo_eq (m : OsMeta) : m.synced.lo = m.size := rfl
theorem synced_size_eq (m : OsMeta) : m.synced.size = m.size := rfl
theorem synced_maps_eq (m : OsMeta) : m.synced.maps = m.maps := rfl

/-! ### `commit`'s states, named -/

/-- The bytes of a state in three parts: the meta pages `H`, the frozen pages `F`, the rest. -/
theorem split_commit {bs : List ByteG} {hwm : Nat} (h2 : 2 ≤ hwm) (hl : 4096 * hwm ≤ bs.length) :
    bs = bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++ bs.drop (4096 * hwm)) ∧
      (bs.take 8192).length = 8192 ∧
      8192 + ((bs.drop 8192).take (4096 * hwm - 8192)).length = 4096 * hwm :=
  ⟨(split3_eq bs 8192 (4096 * hwm) (by omega)).symm, by rw [List.length_take]; omega,
    by rw [List.length_take, List.length_drop]; omega⟩

theorem durAll_eq (bs : List ByteG) : durAll bs = (bs.map Prod.fst).map durB := by
  simp [durAll, List.map_map, Function.comp_def]

/-- `commit`'s growth (`Truncate` to `len`, then `Sync`): the grown state's sync, named, its
obligations, and the state it leaves. -/
theorem grow_facts {i : Ino} {m : OsMeta} {bs : List ByteG} {hwm len : Nat}
    (h : commitClean m bs) (hl : bs.length = m.size)
    (hpg : curPgid ((bs.map Prod.fst).take 8192) = hwm) (h2 : 2 ≤ hwm)
    (h4 : 4096 * hwm ≤ m.size) (hsz : m.size ≤ len) (h30 : len ≤ 2 ^ 30) (h16 : 4 * 4096 ≤ m.size)
    (zs : List Cands) (n : Nat) (hzl : zs.length = len - m.size) :
    ∃ (M3 : OsMeta) (B3 H F T : List ByteG),
      bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])) = H ++ (F ++ T) ∧ H.length = 8192 ∧
      8192 + F.length = 4096 * hwm ∧ (∀ y ∈ F, y = durB y.1) ∧
      csSynced (rsPost m len len) H F T 8192 (4096 * hwm) = ⟨M3, B3, 8192, 4096 * hwm, .idle⟩ ∧
      commitClean M3 B3 ∧ M3.size = len ∧ M3.maps = m.maps ∧ True ∧
      (B3.map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 ∧
      (∀ M : GMap Loc Nat, dbOk (some (i, ⟨{ M3 with maps := M }, B3, 8192, 4096 * hwm, .idle⟩))) ∧
      dbOk (some (i, ⟨M3, B3, 8192, 4096 * hwm, .idle⟩)) ∧
      (∀ M : GMap Loc Nat, dbOk (some (i, ⟨{ rsPost m len len with maps := M }, H ++ (F ++ T),
        8192, 4096 * hwm, .idle⟩))) := by
  generalize hG : bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])) = G
  have hR : TReach m bs len (rsPost m len len) G := by rw [← hG]; exact .grown n zs hzl
  obtain ⟨hcG, hlG, -, -, hmG⟩ := treach_commitClean h hl h30 hsz h16 (by rw [hpg]; exact h4) hR
  have hsG : (rsPost m len len).size = len := rfl
  have hpreG : ∀ k < 4096 * hwm, G[k]? = bs[k]? := fun k hk => by
    rw [← hG]; exact List.getElem?_append_left (by omega)
  have htG : (G.map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 := take8192_congr hpreG (by omega)
  obtain ⟨e, hH, hF⟩ := split_commit (bs := G) h2 (by rw [hlG, hsG]; omega)
  have hFd := commitClean_frozen hcG (hwm := hwm) (by rw [htG, hpg])
  have hpg' : 4096 * curPgid ((G.map Prod.fst).take 8192) ≤ len := by rw [htG, hpg]; omega
  have hcS : commitClean (rsPost m len len).synced (durAll G) :=
    commitClean_durAll hcG (by rw [synced_hi_eq]; exact h30) (by rw [synced_lo_eq]; show 4 * 4096 ≤ len; omega) hpg'
  have hlS : (durAll G).length = (rsPost m len len).synced.size := by rw [durAll_length, hlG]; rfl
  have htS : ((durAll G).map Prod.fst).take 8192 = (bs.map Prod.fst).take 8192 := by
    rw [durAll_fst, htG]
  have hab : 8192 ≤ 4096 * hwm := by omega
  have hbl : 4096 * hwm ≤ len := by omega
  refine ⟨_, _, _, _, _, e, hH, hF, hFd, by rw [csSynced_eq _ _ _ _ _ _ hFd, ← e], hcS, rfl,
    hmG, trivial, htS,
    writer_okS 8192 (4096 * hwm) hlS hab (by show 4096 * hwm ≤ len; exact hbl) hcS,
    writer_okS 8192 (4096 * hwm) hlS hab (by show 4096 * hwm ≤ len; exact hbl) hcS _, fun M => ?_⟩
  rw [← e]
  exact writer_okS (m := rsPost m len len) 8192 (4096 * hwm) (by rw [hlG]) hab
    (by show 4096 * hwm ≤ len; exact hbl) hcG M

/-- The data page's sync (`Fdatasync`): obligations, and what the meta write needs of the
state it leaves (every byte durable). -/
theorem dataS_facts {i : Ino} {m4 : OsMeta} {bs4 : List ByteG} {hwm : Nat} {mp : List w8}
    {mv : Meta} {v : w64} (hc : commitClean m4 bs4) (hl : bs4.length = m4.size)
    (hmp : (bs4.map Prod.fst).take 8192 = mp) (hmv : curMeta mp = mv) (hpg : curPgid mp = hwm)
    (h2 : 2 ≤ hwm) (hsz : (hwm + 2) * 4096 ≤ m4.size) (h30 : m4.size ≤ 2 ^ 30)
    (hd : ∀ i < 4096, (bs4[4096 * hwm + i]?).map Prod.fst = (dataPage mv.pgid' v)[i]?)
    (ht : mv.txid'.toNat + 1 < 2 ^ 64) (hb : (hwm + 2) * 4096 ≤ 2 ^ 30)
    (hboot : bootOk (mv.txid'.toNat + 1) (some v)) :
    ∃ (M5 : OsMeta) (H F T : List ByteG),
      bs4 = H ++ (F ++ T) ∧ H.length = 8192 ∧ 8192 + F.length = 4096 * hwm ∧ (∀ y ∈ F, y = durB y.1) ∧
      csSynced m4 H F T 8192 (4096 * hwm) =
        ⟨M5, (bs4.map Prod.fst).map durB, 8192, 4096 * hwm, .idle⟩ ∧
      dbOk (some (i, ⟨M5, (bs4.map Prod.fst).map durB, 8192, 4096 * hwm, .idle⟩)) ∧
      (∀ M : GMap Loc Nat, dbOk (some (i, ⟨{ m4 with maps := M }, H ++ (F ++ T),
        8192, 4096 * hwm, .idle⟩))) ∧
      commitMetaSt M5 ((bs4.map Prod.fst).map durB) mp (commitOf mv) (mv.txid'.toNat % 2) ∧
      (bs4.map Prod.fst).length = M5.size ∧
      (∀ k < 4096, (bs4.map Prod.fst)[4096 * hwm + k]? = (dataPage mv.pgid' v)[k]?) ∧
      M5.maps = m4.maps ∧ M5.size = m4.size ∧ (bs4.map Prod.fst).take 8192 = mp ∧
      M5.lo ≤ M5.size := by
  obtain ⟨h16, hbs, -, hab, h44⟩ := arith_hwm hwm m4.size h2 hsz
  obtain ⟨e, hH, hF⟩ := split_commit (bs := bs4) h2 (by rw [hl]; exact hbs)
  have hFd := commitClean_frozen hc (hwm := hwm) (by rw [hmp, hpg])
  have hpg' : 4096 * curPgid ((bs4.map Prod.fst).take 8192) ≤ m4.size := by rw [hmp, hpg]; exact hbs
  have hcS : commitClean m4.synced (durAll bs4) :=
    commitClean_durAll hc (by rw [synced_hi_eq]; exact h30) (by rw [synced_lo_eq]; exact h16)
      (by rw [synced_lo_eq]; exact hpg')
  have htS : ((durAll bs4).map Prod.fst).take 8192 = mp := by rw [durAll_fst, hmp]
  have hpage : ∀ k < 4096, (durAll bs4)[4096 * curPgid ((durAll bs4).map Prod.fst |>.take 8192) + k]? =
      (dataPage (curMeta ((durAll bs4).map Prod.fst |>.take 8192)).pgid' v)[k]?.map durB := by
    intro k hk
    rw [htS, hpg, hmv, durAll, List.getElem?_map, ← hd k hk]
    cases bs4[4096 * hwm + k]? <;> rfl
  have hc5 := commitMetaSt_of (v := v) hcS (by rw [htS, hmv]; exact ht) (by rw [htS, hpg]; exact hb)
    (by rw [htS, hpg, synced_lo_eq, Nat.mul_add, Nat.mul_one]; exact h44) hpage
    (by rw [htS, hmv]; exact hboot)
  rw [htS, hmv] at hc5
  have hlS : (durAll bs4).length = m4.synced.size := by rw [durAll_length, hl]; rfl
  refine ⟨m4.synced, _, _, _, e, hH, hF, hFd, by rw [csSynced_eq _ _ _ _ _ _ hFd, ← e, durAll_eq],
    (by
        rw [← durAll_eq]
        exact commitClean_okS
          { m := m4.synced, bs := durAll bs4, fa := 8192, fb := 4096 * hwm, busy := .idle }
          ⟨hlS, hab, hbs, trivial⟩ trivial hcS (Nat.le_refl _) h30 (fun _ _ => trivial)),
    fun M => (by rw [← e]; exact writer_okS (m := m4) 8192 (4096 * hwm) hl hab hbs hc M),
    (by rw [← durAll_eq]; exact hc5), (by rw [List.length_map, hl]; rfl),
    fun k hk => (by rw [List.getElem?_map, ← hd k hk]), rfl, rfl, hmp, Nat.le_refl _⟩

/-- The meta write succeeded (the meta pages are the new ones `mp'`); its sync leaves
`commitClean` at `mp'`, whose root page is the data page. -/
theorem metaS_facts {ino : Ino} {M5 m6 : OsMeta} {B5 : List w8} {bs6 : List ByteG} {hwm i : Nat}
    {mp mp' : List w8} {mv : Meta} {v : w64}
    (hl6 : bs6.length = m6.size) (hs6 : m6.size = M5.size)
    (h2 : 2 ≤ hwm) (hsz : (hwm + 2) * 4096 ≤ M5.size) (h30 : M5.size ≤ 2 ^ 30)
    (hi : i = 1 - mv.txid'.toNat % 2)
    (hout : ∀ k, (k < 4096 * i ∨ 4096 * i + 4096 ≤ k) → bs6[k]? = (B5.map durB)[k]?)
    (hd : ∀ j < 4096, (bs6[4096 * i + j]?).map Prod.fst = (metaPageOf mv)[j]?)
    (ht5 : B5.take 8192 = mp) (hml : mp.length = 8192)
    (hpg5 : ∀ k < 4096, B5[4096 * hwm + k]? = (dataPage mv.pgid' v)[k]?)
    (hmp' : mp' = setPage mp i (metaPageOf mv))
    (hok' : metaPagesOk mp') (hcur' : curMeta mp' = commitOf mv) (hcr' : curRoot mp' = hwm)
    (hcp' : curPgid mp' = hwm + 1) (hct' : (curMeta mp').txid'.toNat = mv.txid'.toNat + 1)
    (hboot : bootOk (mv.txid'.toNat + 1) (some v)) (htxm : mv.txid'.toNat < hwm) :
    ∃ (M7 : OsMeta) (B7 H F T : List ByteG),
      bs6 = H ++ (F ++ T) ∧ H.length = 8192 ∧ 8192 + F.length = 4096 * hwm ∧ (∀ y ∈ F, y = durB y.1) ∧
      csSynced m6 H F T 8192 (4096 * hwm) = ⟨M7, B7, 8192, 4096 * hwm, .idle⟩ ∧
      dbOk (some (ino, ⟨M7, B7, 8192, 4096 * hwm, .idle⟩)) ∧
      commitClean M7 B7 ∧ B7.length = M7.size ∧ (B7.map Prod.fst).take 8192 = mp' ∧
      (B7.drop (4096 * hwm)).take (4096 * (hwm + 1) - 4096 * hwm) =
        (dataPage mv.pgid' v).map durB ∧
      M7.maps = m6.maps ∧ M7.size = m6.size ∧ True ∧
      dbOk (some (ino, ⟨M7, B7, 8192, 4096 * (hwm + 1), .idle⟩)) ∧
      (∀ M : GMap Loc Nat, dbOk (some (ino, ⟨{ M7 with maps := M }, B7, 8192, 4096 * (hwm + 1), .idle⟩))) ∧
      (bs6.take 8192).map Prod.fst = mp' := by
  obtain ⟨h16, h4, h5, h8, h44⟩ := arith_hwm hwm M5.size h2 hsz
  have hi2 : i < 2 := by rw [hi]; omega
  have hD := metaPageOf_length mv
  have hdp := dataPage_length mv.pgid' v
  obtain ⟨e, hH, hF⟩ := split_commit (bs := bs6) h2 (by rw [hl6, hs6]; exact h4)
  -- the meta pages
  have hX : (bs6.take 8192).map Prod.fst = mp' := by
    rw [hmp']
    apply List.ext_getElem?; intro k
    rw [setPage_getElem? _ _ _ _ hml hi2 hD, List.getElem?_map, List.getElem?_take]
    by_cases hk : k < 8192
    · rw [if_pos hk]
      by_cases hw : 4096 * i ≤ k ∧ k < 4096 * i + 4096
      · rw [if_pos hw, ← hd (k - 4096 * i) (by omega), show 4096 * i + (k - 4096 * i) = k by omega]
      · rw [if_neg hw, hout k (by omega), ← ht5, List.getElem?_take, if_pos hk, List.getElem?_map,
          Option.map_map]
        cases B5[k]? <;> rfl
    · rw [if_neg hk, if_neg (by omega), List.getElem?_eq_none (by omega)]; rfl
  have hX7 : ((durAll bs6).map Prod.fst).take 8192 = mp' := by
    rw [durAll_fst, ← List.map_take, hX]
  -- the frozen pages
  have hFd : ∀ y ∈ (bs6.drop 8192).take (4096 * hwm - 8192), y = durB y.1 := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    simp only [List.length_take, List.length_drop] at hk
    have e1 : ((bs6.drop 8192).take (4096 * hwm - 8192))[k]? = (B5.map durB)[8192 + k]? := by
      rw [List.getElem?_take, if_pos (by omega), List.getElem?_drop, hout _ (.inr (by omega))]
    rw [List.getElem?_map, List.getElem?_eq_getElem (by rw [hs6] at hl6; simp at hk ⊢; omega)] at e1
    cases hb : B5[8192 + k]? with
    | none => rw [hb] at e1; cases e1
    | some b =>
      rw [hb, Option.map_some, Option.some.injEq] at e1
      rw [e1]
  have hl7 : (durAll bs6).length = m6.synced.size := by rw [durAll_length, hl6]; rfl
  -- the root page: the data page
  have hpg7 : ∀ k < 4096, ((durAll bs6).map Prod.fst)[4096 * hwm + k]? = (dataPage mv.pgid' v)[k]? := by
    intro k hk
    rw [durAll_fst, List.getElem?_map, hout _ (.inr (by omega)), List.getElem?_map, Option.map_map,
      show (Prod.fst ∘ durB) = id from rfl, Option.map_id, hpg5 k hk]; rfl
  have hpB : (((durAll bs6).map Prod.fst).drop (4096 * curRoot mp')).take 4096 = dataPage mv.pgid' v := by
    rw [hcr']
    apply List.ext_getElem?; intro k
    simp only [List.getElem?_take, List.getElem?_drop]
    split
    · exact hpg7 k ‹_›
    · rw [List.getElem?_eq_none (by omega)]
  have hcc7 : commitClean m6.synced (durAll bs6) := by
    refine ⟨by rw [synced_hi_eq, hs6]; exact h30, by rw [synced_lo_eq, hs6]; exact h16,
      by rw [hX7]; exact hok', ?_, by rw [hX7, hcp', synced_lo_eq, hs6]; exact h5,
      by rw [hX7, hpB, hct', dataPage_val]; exact hboot,
      fun k hk => durAll_of (by rw [hl6, hs6]; exact Nat.lt_of_lt_of_le hk (Nat.le_trans h8 h4)),
      fun k hk => durAll_of (by
        rw [hl6, hX7, hcr', hs6]; exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hk _) h44),
      by rw [hX7]; exact ⟨by rw [hct']; exact Nat.le_add_left 1 _,
        by rw [hct', hcp']; exact Nat.succ_lt_succ htxm⟩,
      fun k _ hk => durAll_of (by rw [hl6, hs6]; rw [hX7, hcp'] at hk; exact Nat.lt_of_lt_of_le hk h5)⟩
    unfold curInSlot
    rw [hX7, hct', show (mv.txid'.toNat + 1) % 2 = i by omega, hcur', hmp',
      fileMeta_setPage_same mp i _ hml hi2 hD, metaPageOf_meta]
  have hpg7' : ((durAll bs6).drop (4096 * hwm)).take (4096 * (hwm + 1) - 4096 * hwm) =
      (dataPage mv.pgid' v).map durB := by
    apply List.ext_getElem?; intro k
    rw [List.getElem?_take, List.getElem?_drop, List.getElem?_map]
    by_cases hk : k < 4096 * (hwm + 1) - 4096 * hwm
    · rw [if_pos hk]
      have := hpg7 k (by omega)
      rw [durAll_fst, List.getElem?_map] at this
      rw [List.getElem?_map, ← this, Option.map_map]; rfl
    · rw [if_neg hk, List.getElem?_eq_none (by rw [List.length_map, hdp]; omega)]
  have hfb : 4096 * (hwm + 1) ≤ m6.size := by rw [hs6]; exact h5
  have hab : 8192 ≤ 4096 * hwm := h8
  have hbs : 4096 * hwm ≤ m6.size := by rw [hs6]; exact h4
  have hab1 : 8192 ≤ 4096 * (hwm + 1) := Nat.le_trans h8 (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have h30' : m6.size ≤ 2 ^ 30 := by rw [hs6]; exact h30
  refine ⟨_, _, _, _, _, e, hH, hF, hFd, (by rw [csSynced_eq _ _ _ _ _ _ hFd, ← e]),
    commitClean_okS { m := m6.synced, bs := durAll bs6, fa := 8192, fb := 4096 * hwm, busy := .idle }
      ⟨hl7, hab, hbs, trivial⟩ trivial hcc7 (Nat.le_refl _) h30' (fun _ _ => trivial),
    hcc7, hl7, hX7, hpg7', rfl, rfl, trivial,
    commitClean_okS
      { m := m6.synced, bs := durAll bs6, fa := 8192, fb := 4096 * (hwm + 1), busy := .idle }
      ⟨hl7, hab1, hfb, trivial⟩ trivial hcc7 (Nat.le_refl _) h30' (fun _ _ => trivial),
    writer_okS (m := m6.synced) 8192 (4096 * (hwm + 1)) hl7 hab1 hfb hcc7,
    hX⟩


end pure2


end osfs_bboltfs
end EtcdGrove
end Perennial
