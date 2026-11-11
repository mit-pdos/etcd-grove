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

/-- **After the meta write** (`os.File.WriteAt.specCrashS`'s post): only the slot changed, the
size and mappings did not, and the state is `Ok` with any mappings. -/
theorem metaW_after2 {i : Ino} {m m' : OsMeta} {B : List w8} {bs' : List ByteG} {mp : List w8}
    {N : Meta} {s hwm : Nat} {D : List w8} {nn : Nat} (h : commitMetaSt m (B.map durB) mp N s)
    (hl : B.length = m.size) (hD : D.length = 4096) (h8 : 4 * 4096 ≤ m.size) (h30 : m.size ≤ 2 ^ 30)
    (hmp : B.take 8192 = mp) (hw : pageMeta D = N) (hlos : m.lo ≤ m.size)
    (hh : 4096 * hwm ≤ m.size) (h2 : 2 ≤ hwm)
    (hR : WReach m (B.map durB) (4096 * (1 - s)) D nn m' bs') :
    bs'.length = m'.size ∧ m'.maps = m.maps ∧ m'.size = m.size ∧
      (∀ k, (k < 4096 * (1 - s) ∨ 4096 * (1 - s) + 4096 ≤ k) → bs'[k]? = (B.map durB)[k]?) ∧
      (∀ M : GMap Loc Nat, dbOk (some (i, ⟨{ m' with maps := M }, bs', 8192, 4096 * hwm, .idle⟩))) := by
  have hs2 := h.s2
  have hl' : (B.map durB).length = m.size := by simp [hl]
  have hoff : 4096 * (1 - s) ≤ m.size := by omega
  obtain ⟨hW, -, -⟩ := hR.wIn hl' hoff
  have hs1 := hW.sz1
  have hsz2 := hW.sz2
  simp only [wT, hD] at hsz2
  refine ⟨hW.len, hW.maps, by omega, fun k hk => hW.out k (by rw [hD]; exact hk),
    (metaW_obl (i := i) h hl hD h8 h30 hmp hw hlos 8192 (4096 * hwm) (Nat.le_refl _) (by omega) hh
      nn m' bs' hR).1⟩


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




section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]

/-- The writer's idle state, its bytes in three segments: the meta pages, the frozen pages, the
rest (for `Sync`/`Fdatasync`). -/
theorem csOwn_split3 (i : Ino) (γc : GName) (m : OsMeta) (bs : List ByteG) (hwm : Nat)
    (h2 : 2 ≤ hwm) :
    csOwnF (GF := GF) γc (some (i, ⟨m, bs, 8192, 4096 * hwm, .idle⟩)) ⊣⊢
      csOwnF (GF := GF) γc (some (i, ⟨m, bs.take 8192 ++ ((bs.drop 8192).take (4096 * hwm - 8192) ++
        bs.drop (4096 * hwm)), 8192, 4096 * hwm, .idle⟩)) := by
  rw [split3_eq bs 8192 (4096 * hwm) (by omega)]
  exact .rfl

/-- `csOwnF` of equal states. -/
theorem csOwnF_congr (γc : GName) (s s' : CState) (h : s = s') :
    csOwnF (GF := GF) γc s ⊢ csOwnF (GF := GF) γc s' := by rw [h]

/-- `commit`'s error result, besides the error (see the spec). -/
def commitErrC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (t : Nat) :
    IProp GF :=
  iprop((∃ n', dbOwner (GF := GF) γ t n') ∗
    ∃ (mp' : List w8) (fl : Bool) (hwm : Nat) (st' : MapSt) (m' : OsMeta) (bs' : List ByteG),
      writerStFC (GF := GF) γ γc db f fd p mp' fl hwm st' m' bs' ∗
      (⌜fl = false⌝ ∨ (⌜fl = true⌝ ∗ dbFailed (GF := GF) γ)))

/-- `writerFileC` once failed asks less. -/
theorem writerFileC_fail (γc : GName) (i : Ino) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8)
    (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List ByteG) :
    writerFileC (GF := GF) γc i db f fd p mp fl hwm st m bs ⊢
      writerFileC (GF := GF) γc i db f fd p mp true hwm st m bs := by
  unfold writerFileC
  iintro ⟨%fsz, Hfsz, Hdsz, Hf, Hfd, Hcs, %Hw⟩
  iexists fsz; iframe
  ipureintro; exact ⟨Hw.1, Hw.2.1, Hw.2.2.1, fun h => by cases h⟩

/-- An error exit of `commit` while the handle is not yet failed. -/
theorem commitErrC_of (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString)
    (mp : List w8) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List ByteG) (t n : Nat) :
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
    ihave Hw := writerFileC_fail γc γ.ino db f fd p mp false hwm st m bs $$ Hw
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
    mapInv (GF := GF) γ γ.ino base len γm ∗ ghostVar γm (1 : Qp).half () ∗
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
  imod fail_cur_inv γ γ.ino base len γm mp hwm $$ [Htok Hcur Hcm] with ⟨Htok, Hcur, Hcm⟩
  · iframe; iframe #
  imod metas_in γ γ.ino base len γm mp true hwm mc hmc (fun h => by cases h)
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
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m : OsMeta) (bs : List ByteG)
    (fsz t n : Nat)
    (h : m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm + 4096 ≤ m.size ∧
      ∀ M : GMap Loc Nat, dbOk (some (γ.ino, ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩))) :
    dbOwner (GF := GF) γ t n ∗ dbFailed (GF := GF) γ ∗ ghostVar γ.cur (1 : Qp).half.half (mp, true, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ γ.ino base len γm ∗ hdrTail (GF := GF) base 0 ∗ hdrTail (GF := GF) base 1 ∗
      cellsAny (GF := GF) base (4096 * hwm) 4096 ∗
      cellsAny (GF := GF) base (4096 * hwm + 4096) (len - 4096 * hwm - 4096) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ ∗
      csOwnF (GF := GF) γc (some (γ.ino, ⟨m, bs, 8192, 4096 * hwm, .idle⟩)) ⊢
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
    (bs : List ByteG) (fsz : Nat)
    (h : (2 ≤ hwm ∧ 4096 * hwm ≤ m.size ∧
      (∀ M : GMap Loc Nat, dbOk (some (γ.ino, ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩))) ∧
      (fl = false → (bs.map Prod.fst).take 8192 = mp ∧ commitClean m bs ∧ fsz = m.size ∧
        0 ≤ fd.toInt ∧ 4 * 4096 ≤ m.size ∧ m.size ≤ 2 ^ 30 ∧ len ≤ 2 ^ 30)) ∧
      (m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41)) :
    ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ ∗
      csOwnF (GF := GF) γc (some (γ.ino, ⟨m, bs, 8192, 4096 * hwm, .idle⟩)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ γ.ino base len γm ∗ writerCells (GF := GF) base hwm len ⊢
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
    (bs : List ByteG) (fsz t n : Nat)
    (h : m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm ≤ m.size ∧
      ∀ M : GMap Loc Nat, dbOk (some (γ.ino, ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩))) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ ∗
      csOwnF (GF := GF) γc (some (γ.ino, ⟨m, bs, 8192, 4096 * hwm, .idle⟩)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ γ.ino base len γm ∗ writerCells (GF := GF) base hwm len ⊢
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
    (bs : List ByteG) (fsz t n : Nat)
    (h : m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41 ∧ 2 ≤ hwm ∧
      4096 * hwm + 4096 ≤ m.size ∧
      ∀ M : GMap Loc Nat, dbOk (some (γ.ino, ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩))) :
    dbOwner (GF := GF) γ t n ∗ ghostVar γ.cur (1 : Qp).half.half (mp, false, hwm) ∗
      ghostVar γ.map (1 : Qp).half (some (base, len, γm)) ∗ ghostVar γ.out (1 : Qp).half.half false ∗
      mapFields (GF := GF) db (DFrac.own (1 : Qp).half) (some (base, len, γm)) ∗
      db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 len ∗
      os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
      osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ ∗
      csOwnF (GF := GF) γc (some (γ.ino, ⟨m, bs, 8192, 4096 * hwm, .idle⟩)) ∗
      ghostVar γ.cls (1 : Qp).half false ∗ ghostVar γm (1 : Qp).half () ∗
      mapInv (GF := GF) γ γ.ino base len γm ∗
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
theorem frozen_page (p : Ino) (B : List ByteG) (hwm : Nat) (h2 : 2 ≤ hwm)
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
    (hwm : Nat) (base : Loc) (len : Nat) (γm : GName) (m : OsMeta) (bs : List ByteG)
    (hok : True) :
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

theorem grown_cells (base : Loc) (m0 : OsMeta) (len S : Nat) (hm : m0.maps = {[base := len]})
    (hs : m0.size = S) (hS : S ≤ len) :
    mcells (GF := GF) m0.maps m0.size len (rsCell len) ⊢
      cellsR (GF := GF) base S (len - S) (fun _ => byteCell 0) := by
  rw [hm, hs]
  refine (mcells_single (GF := GF) base len S len _ hS (Nat.le_refl _)).1.trans ?_
  exact (cellsR_congr base S (len - S) _ _ fun i _ hi => by
    unfold rsCell; rw [if_pos (by omega)]).1

theorem trunc_m0 {m m0 : OsMeta} {bs : List ByteG} {sz : Nat}
    (h : commitClean m bs) (hl : bs.length = m.size) (hsz : sz ≤ 2 ^ 30) (hg : m.size ≤ sz)
    (h16 : 4 * 4096 ≤ m.size) (hpgs : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m.size)
    (hm0 : m0 = m ∨ m0 = m.announce (min m.size sz) (max m.size sz) sz) :
    commitClean m0 bs ∧ m0.size = m.size ∧ m0.maps = m.maps := by
  rcases hm0 with rfl | rfl
  · exact ⟨h, rfl, rfl⟩
  · obtain ⟨hc, -, -, -, hmp⟩ := treach_commitClean h hl hsz hg h16 hpgs .ann
    exact ⟨hc, announce_size .., hmp⟩

end lemmas


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.Assumptions]


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
  intro γ γc db f fd p R mp st m bs v Hok Ht Hmok Hst Hvp Hboot
  have Hb1 : (curPgid mp + 1) * 4096 ≤ 2 ^ 30 := Hok.2.2.2.2
  generalize hmv : curMeta mp = mv at Ht Hvp Hboot ⊢
  generalize hhwm : curPgid mp = hwm at Hb1 ⊢
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
  have hhwm2 : hwm + 1 ≤ 2 ^ 18 := by omega
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
  have hmax : sint.Z (W64 1073741824) = 1073741824 := by rfl
  simp only [hmax]
  -- refuse to grow past maxMapSize
  by_cases Hb : (hwm + 2) * 4096 ≤ 2 ^ 30
  rotate_left
  · have hc : (1073741824 : Int) < ((hwm + 2) * 4096 : Nat) := by omega
    simp only [hc, decide_true]
    ihave ⟨%e3, #He3, %He3⟩ := pkgFacts_errMapTooLarge $$ Hpkg
    wp_auto
    ihave Herr := commitErrC_mk γ γc db f fd p mp hwm base len γm m bs _ _ hwm
      ⟨Hstp.1, Hstp.2.1, Hstp.2.2.1, Hstp.2.2.2, Hwf.1, Hwf.2.1, Hwf.2.2.1⟩
      $$ [Hown Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc]
    · iframe; iframe #
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact He3
    iunfold commitErrC at Herr
    iexact Herr
  have hc : ¬ (1073741824 : Int) < ((hwm + 2) * 4096 : Nat) := by omega
  simp only [hc, decide_false]
  clear hc hmax Hb1
  (try wp_auto)
  simp only [mapLen, hlenZ, hmZ]
  -- remap if the next high water mark passes the mapping
  wp_join (Q := fun bv => iprop((⌜bv = executeVal⌝ ∗ ∃ (base' : Loc) (len' : Nat) (γm' : GName) (m' : OsMeta),
      writerStC (GF := GF) γ γc db f fd p mp false hwm (some (base', len', γm')) m' bs ∗
      ⌜True ∧ (hwm + 2) * 4096 ≤ len'⌝ ∗
      dbOwner (GF := GF) γ mv.txid'.toNat hwm ∗
      db_ptr ↦ db ∗ minsz_ptr ↦ minsz ∗ «$res0_ptr» ↦ GoInterface.nil ∗
      v_ptr ↦ v ∗ pg_ptr ↦ mv.pgid' ∗ m_ptr ↦ nextMeta mv) ∨
    (∃ e : GoInterface, ⌜bv = returnVal #() ∧ e ≠ interface.nil⌝ ∗ db_ptr ↦ db ∗
      «$res0_ptr» ↦ e ∗ commitErrC (GF := GF) γ γc db f fd p mv.txid'.toNat)))
    with [-HΦ]
  · -- remap
    wp_apply wp_mmap γ γc db f fd p R minsz mp false hwm (some (base, len, γm)) m bs rfl (by omega)
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
      refine ⟨⟨Hmaps', by omega, Hb', Hl41⟩, trivial, by omega⟩
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
  icases csOwnF_wf' _ _ $$ Hcs with ⟨Hcs, %Hcw⟩
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
  wp_join (Q := fun bv => iprop((⌜bv = executeVal⌝ ∗ ∃ (m2 : OsMeta) (bs2 : List ByteG),
      writerStC (GF := GF) γ γc db f fd p mp false hwm (some (base, len, γm)) m2 bs2 ∗
      ⌜True ∧ (hwm + 2) * 4096 ≤ m2.size⌝ ∗
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
    have hpgs : 4096 * curPgid ((bs.map Prod.fst).take 8192) ≤ m'.size := by
      rw [show curPgid ((bs.map Prod.fst).take 8192) = hwm from hpgb]; exact Hwf.2.1
    have hobl := trunc_obl (i := γ.ino) hcc hbl (show len ≤ 2 ^ 30 from hsz.2.2) Hsz hsz.1 hpgs
      8192 (4096 * hwm) (by omega) Hwf.2.1
    rw [← hlen64] at hobl
    rw [← Hmaps]
    wp_apply wp_Truncate f fd p _ (W64 (len : Int)) _ ⟨γ.ino, true, true⟩ dbCrashN p R γc Good dbOk m' bs
        8192 (4096 * hwm) hfd rfl hlenI (by rw [hlen64]; exact Hsz) dbCrashN_disj hobl
        $$ [Hf Hfd Hcs Hmc] as %err ⟨Hf, Hfd, Hres⟩
    · simp only [hlen64]; iframe; iframe #
    simp only [hlen64]
    have h4 := Hwf.2.1
    have h4len : 4096 * hwm ≤ len := by omega
    have h16len : 4 * 4096 ≤ len := Nat.le_trans hsz.1 Hsz
    have hl30 : len ≤ 2 ^ 30 := hsz.2.2
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
    have hm0f := fun m0 (hm0 : m0 = m' ∨ m0 = m'.announce (min m'.size len) (max m'.size len) len) =>
      trunc_m0 hcc hbl hl30 Hsz hsz.1 hpgs hm0
    icases Hres with (⟨%Herr, %n, %m0, %hm0, Hg⟩ | ⟨%Herr, (⟨%n, %m0, %hm0, Hg⟩ | ⟨Hcs, Hmc⟩)⟩)
    · subst Herr
      obtain ⟨hcc0, hs0, hmp0⟩ := hm0f m0 hm0
      have hmR : (rsPost m0 len len).maps = {[base := len]} :=
        (announce_maps m0 (min m0.size len) (max m0.size len) len).trans (hmp0.trans Hmaps)
      iunfold csGrownOwn at Hg
      icases Hg with ⟨%zs, %Hzs, Hcs, Hc⟩
      obtain ⟨M3, B3, H, F, T, hsplit, hH, hF, hHc, hsyn, hcc3, hs3, hm3, -, ht3, hok3, hok3', hokG⟩ :=
        grow_facts (i := γ.ino) (len := len) hcc0 (by rw [hs0]; exact hbl) hpgb h2
          (by rw [hs0]; exact h4) (by rw [hs0]; exact Hsz) hl30 (by rw [hs0]; exact hsz.1) zs n Hzs.1
      ihave Hwc := hcells _ (grown_cells (GF := GF) base m0 len m'.size (hmp0.trans Hmaps) hs0 Hsz)
        $$ [Hwc4 Hlow Hc]
      · iframe
      (try wp_auto)
      rw [hsplit]
      wp_apply wp_Sync f fd p _ _ ⟨γ.ino, true, true⟩ dbCrashN p R γc Good dbOk (rsPost m0 len len) H F T
          8192 (4096 * hwm) hH hF hHc dbCrashN_disj (by rw [hsyn]; exact hok3')
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
        have hE : M3.maps = {[base := len]} := by rw [hm3, hmp0]; exact Hmaps
        have hF' : M3.size ≤ len := by rw [hs3]; exact Nat.le_refl _
        have hH' : (hwm + 2) * 4096 ≤ M3.size := by rw [hs3]; exact Hlen
        ihave Hws := writerStC_mk γ γc db f fd p mp false hwm base len γm M3 B3 len
            ⟨⟨h2, hA, hok3, fun _ => ⟨hD, hcc3, hs3.symm, hfd, hB, hC, hl30⟩⟩, hE, hF', Hbase, Hl41⟩
          $$ [Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc]
        · iframe Hcur Hmap Hout Hflds Hfsz Hdsz Hf Hfd Hcs Hcls Htok Hwc; iframe #
        iframe
        ipureintro
        exact ⟨trivial, hH'⟩
      · cases err2 with
        | nil => exact absurd rfl Herr2
        | ok ie =>
        (try wp_auto)
        iright
        iexists GoInterface.ok ie
        iframe
        isplitr
        · ipureintro; exact ⟨rfl, Herr2⟩
        iapply commitErrC_mk γ γc db f fd p mp hwm base len γm (rsPost m0 len len)
          (H ++ (F ++ T)) m'.size _ hwm ⟨hmR, Nat.le_refl len, Hbase, Hl41, h2, h4len, hokG⟩
        iframe; iframe #
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      obtain ⟨hcc0, hs0, hmp0⟩ := hm0f m0 hm0
      have hmR : (rsPost m0 len len).maps = {[base := len]} :=
        (announce_maps m0 (min m0.size len) (max m0.size len) len).trans (hmp0.trans Hmaps)
      iunfold csGrownOwn at Hg
      icases Hg with ⟨%zs, %Hzs, Hcs, Hc⟩
      obtain ⟨M3, B3, H, F, T, hsplit, -, -, -, -, -, -, -, -, -, -, -, hokG⟩ :=
        grow_facts (i := γ.ino) (len := len) hcc0 (by rw [hs0]; exact hbl) hpgb h2
          (by rw [hs0]; exact h4) (by rw [hs0]; exact Hsz) hl30 (by rw [hs0]; exact hsz.1) zs n Hzs.1
      ihave Hwc := hcells _ (grown_cells (GF := GF) base m0 len m'.size (hmp0.trans Hmaps) hs0 Hsz)
        $$ [Hwc4 Hlow Hc]
      · iframe
      (try wp_auto)
      iright
      iexists GoInterface.ok ie
      iframe
      isplitr
      · ipureintro; exact ⟨rfl, Herr⟩
      iapply commitErrC_mk γ γc db f fd p mp hwm base len γm (rsPost m0 len len)
        (bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) m'.size _ hwm
        ⟨hmR, Nat.le_refl len, Hbase, Hl41, h2, h4len, by rw [hsplit]; exact hokG⟩
      iframe; iframe #
    · cases err with
      | nil => exact absurd rfl Herr
      | ok ie =>
      have hcc0 := (hm0f _ (.inr rfl)).1
      have hokT : ∀ M : GMap Loc Nat, dbOk (some (γ.ino,
          ⟨{ m'.announce (min m'.size len) (max m'.size len) len with maps := M }, bs, 8192,
            4096 * hwm, .idle⟩)) :=
        writer_okS 8192 (4096 * hwm) (by rw [announce_size]; exact hbl) (by omega)
          (by rw [announce_size]; exact h4) hcc0
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
      iapply commitErrC_mk γ γc db f fd p mp hwm base len γm
        (m'.announce (min m'.size len) (max m'.size len) len) bs
        m'.size _ hwm ⟨by rw [announce_maps]; exact Hmaps, by rw [announce_size]; exact Hsz, Hbase, Hl41,
          h2, by rw [announce_size]; exact h4, hokT⟩
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
  icases csOwnF_wf' _ _ $$ Hcs with ⟨Hcs, %Hcw⟩
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
  have hobl := fun fb (k1 : 8192 ≤ fb) (k2 : fb ≤ m2.size) (k3 : fb ≤ 4096 * hwm) =>
    dataW_obl (i := γ.ino) (D := dataPage mv.pgid' v) hcc hbl
    (by rw [hmp, show curPgid mp = hwm from hhwm]; exact Nat.le_refl _) h4'
    (by rw [hdl]; exact Nat.le_trans hin h30) h30 h16 8192 fb k1 k2 k3
  rw [← hoff] at hobl
  have hO := hobl (4096 * hwm) (by omega) (by omega) (by omega)
  have a1 : (mv.pgid' * W64 4096).toNat ≤ m2.size := by rw [hoff]; exact h4'
  have a2 : (mv.pgid' * W64 4096).toNat + (dataPage mv.pgid' v).length < 2 ^ 63 := by
    rw [hoff, hdl]; omega
  have a3 : 0 < (dataPage mv.pgid' v).length := by rw [hdl]; decide
  have a4 : (dataPage mv.pgid' v).length ≤ 0x40000000 := by rw [hdl]; decide
  have a5 : (mv.pgid' * W64 4096).toNat + (dataPage mv.pgid' v).length ≤ 8192 ∨
      4096 * hwm ≤ (mv.pgid' * W64 4096).toNat := .inr (by omega)
  wp_apply wp_WriteAt f fd p (DFrac.own (1 : Qp).half) buf (dataPage mv.pgid' v) (DFrac.own 1)
      (mv.pgid' * W64 4096) (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ dbCrashN p R γc Good dbOk m2 bs2
      8192 (4096 * hwm) rfl hoffI a1 a2 a3 a4 dbCrashN_disj a5 hO
      $$ [Hf Hbuf Hfd Hcs Hpc]
    as %n %err ⟨Hf, Hbuf, Hfd, Hpc, %nn4, %m4, %bs4, %Hres, Hcs⟩
  · iframe Hf Hbuf Hfd Hcs; iframe #
    rw [hoff, hdl]; iexact Hpc
  rw [hoff, dataPage_length] at Hres
  rw [hoff, hdl]
  icases (mcellsAny_single (GF := GF) base len (4096 * hwm) (4096 * hwm + 4096)
    (Nat.le_add_right _ _) (Nat.le_trans hin Hsz)).1 $$ [Hpc] with Hpc
  · rw [Hmaps]; iexact Hpc
  rw [Nat.add_sub_cancel_left]
  obtain ⟨hR, ⟨rfl, rfl, -, hd4⟩ | ⟨rfl, hne⟩⟩ := Hres
  rotate_left
  · obtain ⟨-, -, -, hs4, hm4, -, hok4⟩ := dataW_after (i := γ.ino) hcc hbl hmp hhwm h2 hin hdl h30 h16 hR
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
  obtain ⟨hcc4, hbl4, hmp4, hs4, hm4, ho4, -⟩ := dataW_after (i := γ.ino) hcc hbl hmp hhwm h2 hin hdl h30 h16 hR
  (try wp_auto)
  wp_apply wp_Fd f fd p _ $$ [Hf] as Hf
  · iexact Hf
  (try wp_auto)
  obtain ⟨M5, H, F, T, hsplit, hH, hF, hHc, hsyn, hok5, hokF5', hc5, hbl5, hpg5, hm5, hs5, ht5,
    hlo5⟩ := dataS_facts (i := γ.ino) (v := v) hcc4 hbl4 hmp4 hmv hhwm h2
      (by rw [hs4]; exact Hgrow) (by rw [hs4]; exact h30) hd4 Ht Hb Hboot
  rw [hsplit]
  wp_apply wp_Fdatasync fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ dbCrashN p R γc Good dbOk m4 H F T
      8192 (4096 * hwm) hH hF hHc dbCrashN_disj (by rw [hsyn]; exact hok5)
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
    ihave Herr := dataErrC γ γc db f fd p mp hwm base len γm m4 (H ++ (F ++ T))
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
  imod metas_out γ γ.ino base len γm mp hwm $$ [Hinv Htok Hcur Hout Hout2]
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
  have h4M5 : 4096 * hwm ≤ M5.size := by rw [hs5']; exact h4'
  have hab : 8192 ≤ 4096 * hwm := (Nat.mul_le_mul_left 4096 h2 : 4096 * 2 ≤ 4096 * hwm)
  have h16M5 : 4 * 4096 ≤ M5.size := by
    rw [hs5']; exact Nat.le_trans (Nat.mul_le_mul_right 4096 (Nat.add_le_add_right h2 2)) Hgrow
  have h30M5 : M5.size ≤ 2 ^ 30 := by rw [hs5']; exact h30
  have hobl2 := metaW_obl_spec (i := γ.ino) (m := M5) (B := bs4.map Prod.fst) (mp := mp)
    (N := commitOf mv) (s := mv.txid'.toNat % 2) (D := metaPageOf mv) hc5 hbl5 (metaPageOf_length mv)
    h16M5 h30M5 ht5 (metaPageOf_meta mv) hlo5 8192 (4096 * hwm) (Nat.le_refl _) hab h4M5
  rw [← hi, ← hoffm] at hobl2
  have b1 : ((mv.txid' + W64 1) % W64 2 * W64 4096).toNat ≤ M5.size := by rw [hoffm]; omega
  have b2 : ((mv.txid' + W64 1) % W64 2 * W64 4096).toNat + (metaPageOf mv).length < 2 ^ 63 := by
    rw [hoffm, metaPageOf_length]; omega
  have b3 : 0 < (metaPageOf mv).length := by rw [metaPageOf_length]; decide
  have b4 : (metaPageOf mv).length ≤ 0x40000000 := by rw [metaPageOf_length]; decide
  have b5 : ((mv.txid' + W64 1) % W64 2 * W64 4096).toNat + (metaPageOf mv).length ≤ 8192 ∨
      4096 * hwm ≤ ((mv.txid' + W64 1) % W64 2 * W64 4096).toNat :=
    .inl (by rw [hoffm, metaPageOf_length]; omega)
  wp_apply wp_WriteAt f fd p (DFrac.own (1 : Qp).half) mbuf (metaPageOf mv) (DFrac.own 1)
      ((mv.txid' + W64 1) % W64 2 * W64 4096) (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ dbCrashN
      p R γc Good dbOk M5 ((bs4.map Prod.fst).map durB) 8192 (4096 * hwm) rfl hoffmI b1 b2 b3 b4
      dbCrashN_disj b5 hobl2
      $$ [Hf Hmb Hfd Hcs Hpi]
    as %n2 %err2 ⟨Hf, Hmb, Hfd, Hpi, %nn6, %m6, %bs6, %Hres2, Hcs⟩
  · iframe Hf Hmb Hfd Hcs; iframe #
    rw [hoffm, metaPageOf_length]; iexact Hpi
  rw [hoffm, metaPageOf_length] at Hres2
  rw [hoffm, metaPageOf_length]
  icases (mcellsAny_single (GF := GF) base len (4096 * i) (4096 * i + 4096)
    (Nat.le_add_right _ _) (by rw [← hs5'] at Hsz; exact Nat.le_trans hil Hsz)).1 $$ [Hpi] with Hpi
  · rw [hm5']; iexact Hpi
  rw [Nat.add_sub_cancel_left]
  obtain ⟨hR2, hsucc2⟩ := Hres2
  rw [hi] at hR2
  obtain ⟨hl6, hm6, hs6, hout6, hok6⟩ :=
    metaW_after2 (i := γ.ino) (hwm := hwm) (mp := mp) (N := commitOf mv) (D := metaPageOf mv) hc5 hbl5
      (metaPageOf_length mv) h16M5 h30M5 ht5 (metaPageOf_meta mv) hlo5 h4M5 h2 hR2
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
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hcs with ⟨Hv, ⟨Hm6, Hb6⟩, %Hwf6⟩
  have hfb6 : 4096 * hwm ≤ bs6.length := by rw [hl6, hs6, hs5']; exact h4'
  icases (writer_thrBytes γ.ino m6 bs6 hwm h2 hfb6).1 $$ Hb6 with ⟨Hmx, Htl⟩
  have hb6 : m6.maps !! base = some len := by rw [hm6, hm5']; exact GMap.lookup_insert _ _ _
  have hXl : (bs6.take 8192).length = 8192 := by
    rw [List.length_take, hl6, hs6]; exact Nat.min_eq_left h8'
  iapply window_agree _ rfl γ.ino _ m6 base len hb6 (by simp) _ _ (bs6.take 8192) 16 64 v0
    (by rw [hXl]; decide) (Nat.le_trans (by decide) hlen8) $$ Hos Hm6 Hmx Hc0
  iintro Hm6 Hmx Hc0
  iapply window_agree _ rfl γ.ino _ m6 base len hb6 (by simp) _ _ (bs6.take 8192) 4112 64 v1
    (by rw [hXl]; decide) (Nat.le_trans (by decide) hlen8) $$ Hos Hm6 Hmx Hc1
  iintro Hm6 Hmx Hc1
  ihave Hcs := (csOwnF_idle (GF := GF) γ.ino γc ⟨m6, bs6, 8192, 4096 * hwm, .idle⟩ rfl).2
    $$ [Hv Hm6 Hmx Htl]
  · iframe Hv Hm6
    isplitl
    · iapply (writer_thrBytes γ.ino _ bs6 hwm h2 hfb6).2; iframe
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
  obtain ⟨M7, B7, H6, F6, T6, hsplit6, hH6, hF6, hHc6, hsyn6, hok7, hcc7, hbl7, htk7, hpg7, hm7, hs7,
    ho7, hok7', hok7M, hX⟩ := metaS_facts (ino := γ.ino) (v := v) hl6 hs6 h2
      (by rw [hs5']; exact Hgrow) (by rw [hs5']; exact h30) hi (by rw [hi]; exact hout6) hd6 ht5 hml
      hpg5 hmp'.symm hok' hcur' hcr' hcp' hct' Hboot
      (by have h := hcc4.tx.2; rw [hmp4, hmv, show curPgid mp = hwm from hhwm] at h; exact h)
  rw [hX]
  rw [hsplit6] at hok6
  rw [hsplit6]
  wp_apply wp_Fdatasync fd (DFrac.own (1 : Qp).half) ⟨γ.ino, true, true⟩ dbCrashN p R γc Good dbOk m6 H6 F6
      T6 8192 (4096 * hwm) hH6 hF6 hHc6 dbCrashN_disj
      (by rw [hsyn6]; exact hok7) $$ [Hfd Hcs] as %e2 ⟨Hfd, Hs⟩
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
    ihave Herr := dataErrTC γ γc db f fd p mp hwm base len γm m6 (H6 ++ (F6 ++ T6))
      m2.size _ _
      ⟨by show m6.maps = _; rw [hm6]; exact hm5', by show m6.size ≤ len; rw [hs6, hs5']; exact Hsz,
        Hbase, Hl41, h2, by show _ ≤ m6.size; rw [hs6, hs5']; exact hin, hok6⟩
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
  imod cs_freeze dbCrashN p R γ.ino γc Good dbOk M7 B7 8192 (4096 * hwm) 8192 (4096 * (hwm + 1)) ⊤
      (fun _ _ => CoPset.mem_full) (Nat.le_trans h8 (Nat.mul_le_mul_left _ (Nat.le_succ _))) hfb7
      (fun _ => ⟨Nat.le_refl _, Nat.mul_le_mul_left _ (Nat.le_succ _)⟩) hok7' $$ Hci Hcs
    with ⟨Hcs, Hfr⟩
  ihave Hpg := frozen_page γ.ino B7 hwm h2 (by rw [hbl7]; exact hfb7) $$ Hfr
  rw [hpg7]
  imod pageIs_of γ.ino hwm DFrac.discard (dataPage mv.pgid' v) (dataPage_length _ _) $$ Hpg with #HBp
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hcs with ⟨Hv, ⟨Hm7, Hb7⟩, %Hwf7⟩
  have hb7 : M7.maps !! base = some len := by rw [hm7']; exact GMap.lookup_insert _ _ _
  iunfold pageIs at HBp
  icases HBp with ⟨-, #Hpg⟩
  iunfold cellsAny at Hpc
  icases Hpc with ⟨%vf, Hpc⟩
  have hplen : 4096 * hwm + ((dataPage mv.pgid' v).map durB).length ≤ len := by
    rw [List.length_map, dataPage_length]; exact Nat.le_trans hin Hsz
  iapply cellsR_agree _ rfl γ.ino _ M7 base len hb7 DFrac.discard (by simp) _
    ((dataPage mv.pgid' v).map durB) (4096 * hwm) vf hplen $$ Hos Hm7 Hpg [Hpc]
  · rw [List.length_map, dataPage_length]; iexact Hpc
  iintro Hm7 - Hpc
  rw [show ((dataPage mv.pgid' v).map durB).map Prod.fst = dataPage mv.pgid' v by
    rw [List.map_map]; exact List.map_id _]
  ihave Hcs := (csOwnF_idle (GF := GF) γ.ino γc ⟨M7, B7, 8192, 4096 * (hwm + 1), .idle⟩ rfl).2
    $$ [Hv Hm7 Hb7]
  · iframe Hv Hm7 Hb7; ipureintro; exact Hwf7
  imod pageIs_of γ.ino hwm DFrac.discard (dataPage mv.pgid' v) (dataPage_length _ _) $$ Hpg with #HBp
  -- publish: the meta pages, page `hwm` committed, the owner, the last txid, the transaction
  imod metas_publish γ γ.ino base len γm mp mp' hwm (dataPage mv.pgid' v)
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


end osfs_bboltfs
end EtcdGrove
end Perennial
