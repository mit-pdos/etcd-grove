/- Lean-first (no Rocq counterpart).

# bbolt's crash invariant: preservation by each file operation

For each operation bbolt does on its database file, `BDur` (`Crash/Dur.lean`) of the state before
gives `BDur` of every state the crash-aware `os` spec asks about (`Spec/os/CrashSt.lean`: `WReach`'s
states for a `WriteAt`, idle and with the next attempt in flight; `TReach`'s for a growing
`Truncate`; `csSynced` for `fdatasync`/`fsync`; a mapping's change), with the abstract state's move
where the operation is a phase boundary (minibolt's `commitClean_okS`/`commitMeta_okS`/
`initMid_okS` in `.../osfs/bboltfs/CrashKc.lean` are the model):

| operation (Go) | lemma | phase |
|---|---|---|
| `Tx.write`'s `pwrite`s of dirty pages, `commitFreelist`'s page (`tx.go`) | `bDur_write_idle` | idle |
| `fdatasync`/`fsync` | `bDur_sync_idle` | idle |
| `DB.grow`'s `Truncate` (`db.go`), start and finish | `bDur_trunc_idle` | idle |
| the commit point (`Tx.Commit`, before `writeMeta`'s `pwrite`) | `bDur_commit_point` | idle → committing |
| `writeMeta`'s one 4096-byte `pwrite` (`tx.go:613`), in flight and landed | `bDur_write_meta` | committing |
| `writeMeta`'s `fdatasync` (`tx.go:621`) | `bDur_sync_commit` | committing → idle |
| `DB.init`'s two `pwrite`s (`db.go:713`, `:722`) | `bDur_write_init` | init |
| `DB.init`'s first `fdatasync` (`db.go:717`) | `bDur_sync_init` | init |
| `DB.init`'s second `fdatasync` (`db.go:726`) | `bDur_init_done` | init → idle |
| `mmap`/`munmap` | `bDur_maps` | any |
-/
module

public import Proof.go_etcd_io.bbolt.Crash.Trans
public import Proof.go_etcd_io.bbolt.Crash.Ok

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs
open go_etcd_io.bbolt.internal.common

section phases
variable [GooseExts]

theorem bDur_idle_iff {a : BAbs} {s : CSt} (ha : a.phase = .idle) :
    BDur a s ↔ BWf s ∧ IdleOk a.cur a.xcur s := by
  unfold BDur; rw [ha]

theorem bDur_commit_iff {a : BAbs} {s : CSt} (ha : a.phase = .committing) :
    BDur a s ↔ BWf s ∧ CommitOk a.cur a.prev a.xcur a.xprev s := by
  unfold BDur; rw [ha]

theorem bDur_init_iff {a : BAbs} {s : CSt} (ha : a.phase = .init) :
    BDur a s ↔ BWf s ∧ InitOk s := by
  unfold BDur; rw [ha]

theorem crashCands_lt (s : CSt) (hb0 : s.busy = .idle) (b : Nat) (hb : b < s.m.size) :
    crashCands s b = (s.bs[b]?).map Prod.snd := by
  unfold crashCands; rw [hb0]
  show baseCands s b = _
  unfold baseCands; rw [if_pos hb]

omit [GooseExts] in
theorem getD_mem' {α : Type} (l : List α) (n : Nat) (d : α) (h : n < l.length) : l.getD n d ∈ l := by
  rw [getD_eq_getElem' _ _ _ h]; exact List.getElem_mem h

/-! ## Mappings -/

/-- `BDur` reads of a state only its bytes, change in flight, size and bounds, what a crash picks
from, and `vmeta`'s bounds. -/
theorem bDur_congr {a : BAbs} {s s' : CSt} (h : BDur a s) (hbs : s'.bs = s.bs)
    (hb : s'.busy = s.busy) (hsz : s'.m.size = s.m.size) (hlo : s'.m.lo = s.m.lo)
    (hhi : s'.m.hi = s.m.hi) (hcc : crashCands s' = crashCands s)
    (hvlo : s'.vmeta.lo = s.vmeta.lo) (hvhi : s'.vmeta.hi = s.vmeta.hi) (hxs : s'.m.xs = s.m.xs) :
    BDur a s' := by
  unfold BDur BWf BusyIn IdleOk CommitOk InitOk PSync WrIn XsAl at *
  simp only [hbs, hb, hsz, hlo, hhi, hcc, hvlo, hvhi, hxs]
  exact h

/-- **A mapping's change keeps `BDur`** (it changes only the `OsMeta`'s mappings). -/
theorem bDur_maps (a : BAbs) (m : OsMeta) (bs : List ByteG) (fa fb : Nat) (busy : CBusy)
    (mp : GMap Loc Nat) (h : BDur a ⟨m, bs, fa, fb, busy⟩) :
    BDur a ⟨{ m with maps := mp }, bs, fa, fb, busy⟩ := by
  refine bDur_congr h rfl rfl rfl rfl rfl ?_ ?_ ?_ rfl
  · funext b; cases busy <;> rfl
  · cases busy <;> rfl
  · cases busy <;> rfl

/-! ## The idle facts, monotone -/

/-- `IdleOk` of a state whose protected bytes keep their synced values, with no write on them,
and whose smallest size since the last sync has not gone down. -/
theorem idleOk_mono {C : CommitSt} {X : List w8} {s s' : CSt} (hI : IdleOk C X s)
    (hbs : ∀ b v, (b < 8192 ∨ protData X C b) → s.bs[b]? = some (durB v) →
      s'.bs[b]? = some (durB v))
    (hnw : ∀ b, (b < 8192 ∨ protData X C b) → ∀ t off data n, s'.busy = .write t off data n →
      b < off ∨ off + data.length ≤ b)
    (hlo : s.m.lo ≤ s'.m.lo) (hsz : s'.m.size % 4096 = 0) (hwr : WrIn s') (hxa : XsAl s') :
    IdleOk C X s' := by
  obtain ⟨hR, hm, hd, hh, -, -⟩ := hI
  exact ⟨hR, fun b hb => ⟨hbs b _ (.inl hb) (hm b hb).1, hnw b (.inl hb)⟩,
    fun b hb => ⟨hbs b _ (.inr hb) (hd b hb).1, hnw b (.inr hb)⟩, by omega, hsz, hwr, hxa⟩

/-- A synced state's crash sizes: its size alone. -/
theorem csSynced_xsAl (m : OsMeta) (H F T : List ByteG) (fa fb : Nat) (hal : m.size % 4096 = 0) :
    XsAl (csSynced m H F T fa fb) :=
  ⟨[m.size], rfl, fun x hx => by simp only [List.mem_singleton] at hx; rw [hx]; exact hal,
    (fun _ _ _ h => by cases h), (fun _ _ _ _ h => by cases h)⟩

/-- A synced `OsMeta`'s crash sizes are its size alone. -/
theorem xsOne_synced (m : OsMeta) : XsOne m.synced := fun l hl x hx => by
  have e : m.synced.xs = some [m.size] := rfl
  rw [e, Option.some.injEq] at hl; subst hl
  simp only [List.mem_singleton] at hx; exact hx

/-- An announce keeps the crash sizes the size alone (a failed truncate). -/
theorem xsOne_announce {m : OsMeta} (h : XsOne m) (lo hi tg : Nat) : XsOne (m.announce lo hi tg) := by
  intro l hl x hx
  rw [OsMeta.announce_xs] at hl; rw [announce_size]; exact h l hl x hx

/-! ## A sync -/

theorem csSynced_bwf (m : OsMeta) (H F T : List ByteG) (fa fb : Nat)
    (hl : (H ++ (F ++ T)).length = m.size) : BWf (csSynced m H F T fa fb) := by
  refine ⟨?_, trivial, ?_, ?_⟩
  · show (H.map _ ++ (F ++ T.map _)).length = m.size
    simp only [List.length_append, List.length_map] at hl ⊢; omega
  · show m.size ≤ m.size; omega
  · show m.size ≤ m.size; omega

/-- **A sync keeps the idle facts.** -/
theorem bDur_sync_idle (a : BAbs) (ha : a.phase = .idle) (m : OsMeta) (H F T : List ByteG)
    (fa fb : Nat) (hF : ∀ y ∈ F, y = durB y.1) (h : BDur a ⟨m, H ++ (F ++ T), fa, fb, .idle⟩) :
    BDur a (csSynced m H F T fa fb) := by
  rw [bDur_idle_iff ha] at h ⊢
  obtain ⟨hW, hI⟩ := h
  have hl : (H ++ (F ++ T)).length = m.size := hW.1
  have hlo : m.lo ≤ m.size := hW.2.2.1
  have hal : m.size % 4096 = 0 := hI.2.2.2.2.1
  refine ⟨csSynced_bwf m H F T fa fb hl, idleOk_mono hI (fun b v _ hb => ?_)
    (fun _ _ _ _ _ _ h => by cases h) ?_ ?_ (fun _ _ _ _ h => by cases h)
    (csSynced_xsAl m H F T fa fb hal)⟩
  · have hb' : (H ++ (F ++ T))[b]? = some (durB v) := hb
    rw [csSynced_bs m H F T fa fb hF, hb']; rfl
  · show m.lo ≤ m.size; exact hlo
  · show m.size % 4096 = 0; exact hal

/-! ## A growing truncate -/

theorem rsPost_size (m : OsMeta) (sz : Nat) : (rsPost true m sz sz).size = sz := rfl
theorem rsPost_lo (m : OsMeta) (sz : Nat) : (rsPost true m sz sz).lo = min m.lo sz := rfl
theorem rsPost_hi (m : OsMeta) (sz : Nat) : (rsPost true m sz sz).hi = max m.hi sz := rfl

/-- **A growing truncate to a whole number of pages keeps the idle facts**, in each state it may
pass through (`TReach`), idle and with the truncate in flight. -/
theorem bDur_trunc_idle (a : BAbs) (ha : a.phase = .idle) (m : OsMeta) (bs : List ByteG)
    (fa fb sz : Nat) (h : BDur a ⟨m, bs, fa, fb, .idle⟩) (hsz : m.size ≤ sz)
    (hal : sz % 4096 = 0) (m' : OsMeta) (bs' : List ByteG) (hR : TReach m bs sz m' bs') :
    BDur a ⟨m', bs', fa, fb, .idle⟩ ∧ ∀ t n, BDur a ⟨m', bs', fa, fb, .trunc t sz n⟩ := by
  simp only [bDur_idle_iff ha] at h ⊢
  obtain ⟨hW, hI⟩ := h
  have hl : bs.length = m.size := hW.1
  have hlo : m.lo ≤ m.size := hW.2.2.1
  have hhi : m.size ≤ m.hi := hW.2.2.2
  have hal0 : m.size % 4096 = 0 := hI.2.2.2.2.1
  obtain ⟨l, hxl, hla, -, -⟩ : XsAl ⟨m, bs, fa, fb, .idle⟩ := hI.2.2.2.2.2.2
  -- the reached state: its size, bounds, bytes and crash sizes
  have key : m'.lo = m.lo ∧ m.size ≤ m'.size ∧ m'.size ≤ m'.hi ∧ m'.size ≤ sz ∧
      m'.size % 4096 = 0 ∧ bs'.length = m'.size ∧ (∀ b, b < m.size → bs'[b]? = bs[b]?) ∧
      ∃ l', m'.xs = some l' ∧ ∀ x ∈ l', x % 4096 = 0 := by
    cases hR with
    | refl => exact ⟨rfl, Nat.le_refl _, hhi, hsz, hal0, hl, fun _ _ => rfl, l, hxl, hla⟩
    | ann =>
      rw [announce_lo, announce_hi, announce_size, OsMeta.announce_xs]
      exact ⟨by omega, Nat.le_refl _, by omega, hsz, hal0, hl, fun _ _ => rfl, l, hxl, hla⟩
    | grown n zs hzs =>
      rw [rsPost_lo, rsPost_size, rsPost_hi]
      refine ⟨by omega, hsz, by omega, Nat.le_refl _, hal, ?_, fun b hb => ?_, l.insert sz, ?_,
        fun x hx => ?_⟩
      · simp only [List.length_append, List.length_map]; omega
      · rw [List.getElem?_append_left (by omega)]
      · have hxl0 : m.xs = some l := hxl
        show rsXs true m sz = _
        simp only [rsXs, if_true, hxl0, Option.map_some]
      · rcases List.mem_insert_iff.1 hx with rfl | hx
        · exact hal
        · exact hla x hx
  obtain ⟨hlo', hs1, hs2, hs3, hal', hl', hbs, l', hxl', hla'⟩ := key
  have hmono : ∀ busy : CBusy, (∀ t off data n, busy ≠ .write t off data n) →
      (∀ t sz' n, busy = .trunc t sz' n → sz' % 4096 = 0) →
      IdleOk a.cur a.xcur ⟨m', bs', fa, fb, busy⟩ := by
    intro busy hnw htr
    refine idleOk_mono hI (fun b v _ hb => ?_) (fun _ _ t off data n h => absurd h (hnw t off data n))
      (by show m.lo ≤ m'.lo; omega) hal' (fun t off data n h => absurd h (hnw t off data n))
      ⟨l', hxl', hla', htr, fun t off data n h => absurd h (hnw t off data n)⟩
    have hb' : bs[b]? = some (durB v) := hb
    show bs'[b]? = _
    have : b < m.size := by have := (List.getElem?_eq_some_iff.1 hb').1; omega
    rw [hbs b this]; exact hb'
  refine ⟨⟨⟨hl', trivial, by show m'.lo ≤ m'.size; omega, hs2⟩, hmono .idle (fun _ _ _ _ h => by
    cases h) (fun _ _ _ h => by cases h)⟩, fun t n => ⟨⟨hl', hs3, by show m'.lo ≤ m'.size; omega, hs2⟩,
    hmono _ (fun _ _ _ _ h => by cases h) (fun _ _ _ h => by cases h; exact hal)⟩⟩

/-! ## A write inside the file -/

/-- The states a write inside the file reaches keep its size and bounds, and the bytes out of its
range. -/
theorem wreach_inside {m : OsMeta} {bs : List ByteG} {off : Nat} {data : List w8} {nn : Nat}
    {m' : OsMeta} {bs' : List ByteG} (hR : WReach m bs off data nn m' bs')
    (hin : off + data.length ≤ m.size) (hl : bs.length = m.size) (hlo : m.lo ≤ m.size)
    (hhi : m.size ≤ m.hi) :
    m'.size = m.size ∧ m'.lo = m.lo ∧ m'.hi = m.hi ∧ bs'.length = m.size ∧ nn ≤ data.length ∧
      (∀ b, (b < off ∨ off + data.length ≤ b) → bs'[b]? = bs[b]?) ∧ m'.xs = m.xs := by
  induction hR with
  | refl => exact ⟨rfl, rfl, rfl, hl, Nat.zero_le _, fun _ _ => rfl, rfl⟩
  | @step nn0 m0 bs0 k nn' n zs _ hnn hk hnn' _ _ _ ih =>
    obtain ⟨hs, hlo0, hhi0, hl0, -, hout, hxs0⟩ := ih
    have hd : (data.drop nn0).length = data.length - nn0 := List.length_drop
    have hpw : pwSize m0.size (off + nn0) k = m0.size := by unfold pwSize; split <;> omega
    refine ⟨by rw [pwPostK_size, hpw, hs], ?_, ?_, ?_, by omega, fun b hb => ?_,
      by rw [pwPostK_xs, if_pos (by rw [hd]; omega), hxs0]⟩
    · rw [pwPostK_lo, hd, hlo0, hs]; omega
    · rw [pwPostK_hi, hd, hhi0, hs]; omega
    · rw [finBytes_length (by omega) (by omega) (by omega), hpw, hs]
    · by_cases hbs : b < m.size
      · rw [finBytes_out (by omega) (by omega) (by omega) b (by omega) (by omega)]
        exact hout b hb
      · have hfl : (finBytes m0 bs0 (off + nn0) (data.drop nn0) k n zs).length = m0.size := by
          rw [finBytes_length (by omega) (by omega) (by omega), hpw]
        rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- **A write of unprotected bytes inside the file keeps the idle facts** (`Tx.write`'s dirty pages,
`commitFreelist`'s page: pages free for the committed state, not a meta slot), the crash sizes the
size alone (`XsOne`: `DB.grow` syncs its truncate first), in every state of `WReach`, idle and with
the next attempt in flight. -/
theorem bDur_write_idle (a : BAbs) (ha : a.phase = .idle) (m : OsMeta) (bs : List ByteG)
    (fa fb off : Nat) (data : List w8) (h : BDur a ⟨m, bs, fa, fb, .idle⟩)
    (hin : off + data.length ≤ m.size)
    (hun : ∀ b, off ≤ b → b < off + data.length → 8192 ≤ b ∧ ¬ protData a.xcur a.cur b)
    (hone : XsOne m)
    (nn : Nat) (m' : OsMeta) (bs' : List ByteG) (hR : WReach m bs off data nn m' bs') :
    BDur a ⟨m', bs', fa, fb, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off + nn) (data.drop nn) n →
      BDur a ⟨m', bs', fa, fb, .write t (off + nn) (data.drop nn) n⟩) := by
  simp only [bDur_idle_iff ha] at h ⊢
  obtain ⟨hW, hI⟩ := h
  have hl : bs.length = m.size := hW.1
  have hlo : m.lo ≤ m.size := hW.2.2.1
  have hhi : m.size ≤ m.hi := hW.2.2.2
  obtain ⟨hs, hlo', hhi', hl', hnn, hout, hxs'⟩ := wreach_inside hR hin hl hlo hhi
  have hal : m.size % 4096 = 0 := hI.2.2.2.2.1
  obtain ⟨l, hxl, hla, -, -⟩ : XsAl ⟨m, bs, fa, fb, .idle⟩ := hI.2.2.2.2.2.2
  have hxl0 : m.xs = some l := hxl
  have hxa : ∀ busy : CBusy, (∀ t sz n, busy ≠ .trunc t sz n) →
      XsAl ⟨m', bs', fa, fb, busy⟩ := fun busy hnt =>
    ⟨l, by show m'.xs = _; rw [hxs']; exact hxl, hla, fun t sz n h => absurd h (hnt t sz n),
      fun _ _ _ _ _ x hx => by show x = m'.size; rw [hs]; exact hone l hxl0 x hx⟩
  have hprot : ∀ b, (b < 8192 ∨ protData a.xcur a.cur b) → b < off ∨ off + data.length ≤ b := by
    intro b hb
    apply Classical.byContradiction; intro hc
    have := hun b (by omega) (by omega)
    rcases hb with hb | hb
    · omega
    · exact this.2 hb
  have hbs : ∀ b v, (b < 8192 ∨ protData a.xcur a.cur b) → bs[b]? = some (durB v) →
      bs'[b]? = some (durB v) := fun b v hb h => by
    have h' : bs[b]? = some (durB v) := h
    rw [hout b (hprot b hb)]; exact h'
  have hd : (data.drop nn).length = data.length - nn := List.length_drop
  refine ⟨⟨⟨by show bs'.length = m'.size; rw [hs]; exact hl', trivial, by show m'.lo ≤ m'.size; omega,
      by show m'.size ≤ m'.hi; omega⟩,
    idleOk_mono hI (fun b v hb h => hbs b v hb h) (fun _ _ _ _ _ _ h => by cases h)
      (by show m.lo ≤ m'.lo; omega)
      (by show m'.size % 4096 = 0; rw [hs]; exact hal) (fun _ _ _ _ h => by cases h)
      (hxa _ (fun _ _ _ h => by cases h))⟩,
    fun hlt t n _ => ⟨⟨by show bs'.length = m'.size; rw [hs]; exact hl', by show off + nn ≤ m'.size; omega,
      by show m'.lo ≤ m'.size; omega, by show m'.size ≤ m'.hi; omega⟩,
    idleOk_mono hI (fun b v hb h => hbs b v hb h) (fun b hb t' off' data' n' he => by
        cases he; have := hprot b hb; rw [hd]; omega)
      (by show m.lo ≤ m'.lo; omega) (by show m'.size % 4096 = 0; rw [hs]; exact hal)
      (fun t' off' data' n' he => by
        cases he; show off + nn + (data.drop nn).length ≤ m'.size; rw [hd]; omega)
      (hxa _ (fun _ _ _ h => by cases h))⟩⟩

/-! ## The commit point -/

/-- **The commit point** (`Tx.Commit`, before `writeMeta`'s `pwrite`, with `metalock`): from the
idle facts of `prev` (`a`), with the new committed state `C` (reference image `Xc`, txid one more,
the other slot `prev`'s current one) whose protected data bytes are synced (the first `fdatasync`)
and whose high-water mark is inside the smallest size since the last sync (`grow`), and the size
not moved since the last sync: the committing facts of `C` over `prev`. -/
theorem bDur_commit_point (a : BAbs) (ha : a.phase = .idle) (s : CSt) (hb : s.busy = .idle)
    (h : BDur a s) (C : CommitSt) (Xc : List w8) (hRc : RefImg Xc C)
    (htx : C.txid = a.cur.txid + 1) (hsl : C.slot (C.txid + 1) = a.cur.slot a.cur.txid)
    (hdc : ∀ b, protData Xc C b → PSync s b (xb Xc b)) (hhc : C.hwm * 4096 ≤ s.m.lo)
    (hlo : s.m.lo = s.m.size) (hhi : s.m.hi = s.m.size) :
    BDur { cur := C, prev := a.cur, xcur := Xc, xprev := a.xcur, phase := .committing } s := by
  rw [bDur_idle_iff ha] at h
  rw [bDur_commit_iff rfl]
  obtain ⟨hW, hR, hm, hd, hh, hal, hwr, -⟩ := h
  have hvm : s.vmeta = s.m := by unfold CSt.vmeta; rw [hb]
  refine ⟨hW, hR, hRc, htx, hsl, fun k hk => hm _ (by omega), ⟨none, fun k hk => ?_⟩, hd, hdc,
    hh, hhc, hal, by rw [hvm, hlo], by rw [hvm, hhi], hwr⟩
  obtain ⟨hc, -⟩ := psync_cands hW (hm (4096 * (C.txid % 2) + k) (by omega))
  exact ⟨_, hc, [], rfl, by simp, rfl⟩

/-! ## The meta write -/

/-- A slot byte's candidates with the new value appended by a fresh change. -/
theorem candOV_snoc {c : Cands} {o v : w8} {N : Option Nat} (h : CandOV c o v N) {n : Nat}
    (hf : ∀ q ∈ c, q.2 < n) : CandOV (c ++ [(v, n)]) o v (some (N.getD n)) := by
  obtain ⟨L, rfl, hv, hN⟩ := h
  refine ⟨L ++ [(v, n)], by simp, fun q hq => ?_, ?_⟩
  · rcases List.mem_append.1 hq with hq | hq
    · exact hv q hq
    · simp only [List.mem_singleton] at hq; rw [hq]
  · cases N with
    | none =>
      dsimp only at hN ⊢; subst hN
      exact ⟨by simp, fun q hq => by
        simp only [List.nil_append, List.mem_singleton] at hq; rw [hq]; exact Nat.le_refl n⟩
    | some N0 =>
      obtain ⟨hmem, hge⟩ := hN
      dsimp only
      refine ⟨List.mem_append_left _ hmem, fun q hq => ?_⟩
      rcases List.mem_append.1 hq with hq | hq
      · exact hge q hq
      · simp only [List.mem_singleton] at hq; rw [hq]
        exact Nat.le_of_lt (hf _ (List.mem_cons_of_mem _ hmem))

/-- The slot byte `k` of a reached state of the meta write, from the state before the attempt. -/
theorem metaSlot_step {m0 : OsMeta} {bs0 : List ByteG} {off nn0 k n : Nat} {data : List w8}
    {zs : List Cands} {o v : Nat → w8} {N : Option Nat} (hl0 : bs0.length = m0.size)
    (hlen : data.length = 4096) (hin : off + 4096 ≤ m0.size) (hnn : nn0 < 4096)
    (hk : k ≤ data.length - nn0)
    (hdat : ∀ j < 4096, data.getD j 0 = v j) (hN : N = none → nn0 = 0)
    (hPF : PwFresh m0 bs0 (off + nn0) (data.drop nn0) n)
    (hsl : ∀ j < 4096, ∃ x, bs0[off + j]? = some x ∧ CandOV x.2 (o j) (v j) N) :
    ∀ j < 4096, ∃ x, (finBytes m0 bs0 (off + nn0) (data.drop nn0) k n zs)[off + j]? = some x ∧
      CandOV x.2 (o j) (v j) (some (N.getD n)) := by
  intro j hj
  obtain ⟨x, hx, hov⟩ := hsl j hj
  have hd : (data.drop nn0).length = 4096 - nn0 := by simp [hlen]
  have hpw : pwSize m0.size (off + nn0) k = m0.size := by
    unfold pwSize; split <;> rw [hlen] at hk <;> omega
  by_cases hjn : j < nn0
  · refine ⟨x, ?_, ?_⟩
    · rw [finBytes_getElem? hl0 (by omega), if_pos (by omega)]; exact hx
    · cases N with
      | none => exact absurd (hN rfl) (by omega)
      | some N0 => exact hov
  · have hxr : (cfRange m0 bs0 (off + nn0) (data.drop nn0).length).getD (j - nn0) (0, []) = x := by
      rw [cfRange_getD hl0 (by omega) (by rw [hd]; omega)]
      rw [List.getElem?_eq_getElem (by omega)] at hx
      simp only [Option.some.injEq] at hx
      simp only [show off + nn0 + (j - nn0) = off + j by omega]
      exact hx
    rw [finBytes_getElem? hl0 (by omega), if_neg (by omega), if_pos (by rw [hd, hpw]; omega),
      show off + j - (off + nn0) = j - nn0 by omega,
      pwBytes_getElem?' _ _ _ _ _ _ _ _ (by rw [hd, hpw]; omega)]
    refine ⟨_, rfl, ?_⟩
    dsimp only
    rw [if_pos (by rw [cfRange_length hl0 (by omega), hd]; omega), hxr]
    have hv : (data.drop nn0).getD (j - nn0) 0 = v j := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_drop, show nn0 + (j - nn0) = j by omega,
        ← List.getD_eq_getElem?_getD, hdat j hj]
    rw [hv]
    refine candOV_snoc hov (fun q hq => hPF.1 x ?_ q hq)
    rw [← hxr]
    exact getD_mem' _ _ _ (by rw [cfRange_length hl0 (by omega), hd]; omega)

/-- **`writeMeta`'s `pwrite` keeps the committing facts**: the one 4096-byte write of the new meta
page (`C.slot C.txid`) at slot `C.txid % 2`, in every state of `WReach`, idle and with the next
attempt in flight. -/
theorem bDur_write_meta (a : BAbs) (ha : a.phase = .committing) (m : OsMeta) (bs : List ByteG)
    (fa fb : Nat) (h : BDur a ⟨m, bs, fa, fb, .idle⟩) (nn : Nat) (m' : OsMeta) (bs' : List ByteG)
    (hR : WReach m bs (4096 * (a.cur.txid % 2)) (a.cur.slot a.cur.txid) nn m' bs') :
    BDur a ⟨m', bs', fa, fb, .idle⟩ ∧ (nn < (a.cur.slot a.cur.txid).length → ∀ t n,
      PwFresh m' bs' (4096 * (a.cur.txid % 2) + nn) ((a.cur.slot a.cur.txid).drop nn) n →
      BDur a ⟨m', bs', fa, fb, .write t (4096 * (a.cur.txid % 2) + nn)
        ((a.cur.slot a.cur.txid).drop nn) n⟩) := by
  simp only [bDur_commit_iff ha] at h ⊢
  generalize a.cur = C at h hR ⊢
  generalize a.prev = P at h ⊢
  generalize a.xcur = Xc at h ⊢
  generalize a.xprev = Xp at h ⊢
  obtain ⟨hW, hRp, hRc, htx, hsl, hslotp, ⟨N, hfl⟩, hdp, hdc, hhp, hhc, hal, hvlo, hvhi, -⟩ := h
  have hl : bs.length = m.size := hW.1
  have hlo : m.lo ≤ m.size := hW.2.2.1
  have hhi : m.size ≤ m.hi := hW.2.2.2
  have hvlo' : m.lo = m.size := hvlo
  have hvhi' : m.hi = m.size := hvhi
  have hhp' : P.hwm * 4096 ≤ m.lo := hhp
  have hhc' : C.hwm * 4096 ≤ m.lo := hhc
  have hal' : m.size % 4096 = 0 := hal
  have h3 := refImg_hwm hRc
  have hlen : (C.slot C.txid).length = 4096 := by
    unfold CommitSt.slot; split
    · exact hRc.mok.1
    · exact hRc.mok.2.1
  have hj2 : C.txid % 2 < 2 := Nat.mod_lt _ (by omega)
  have hin : 4096 * (C.txid % 2) + (C.slot C.txid).length ≤ m.size := by
    rw [hlen]; have := Nat.mul_le_mul_right 4096 h3; omega
  obtain ⟨hs, hlo', hhi', hl', hnn, hout, hxs'⟩ := wreach_inside hR hin hl hlo hhi
  -- the new meta's bytes
  have hdat : ∀ k < 4096, (C.slot C.txid).getD k 0 = xb Xc (4096 * (C.txid % 2) + k) := by
    intro k hk
    rw [refImg_slot hRc]; exact bytesAt_getD _ _ _ hk (by have := hRc.len; omega)
  -- the bytes out of slot `C.txid % 2`
  have hprot : ∀ b, (protData Xp P b ∨ protData Xc C b ∨
      (4096 * (P.txid % 2) ≤ b ∧ b < 4096 * (P.txid % 2) + 4096)) →
      b < 4096 * (C.txid % 2) ∨ 4096 * (C.txid % 2) + (C.slot C.txid).length ≤ b := by
    intro b hb
    rw [hlen]
    rcases hb with hb | hb | hb
    · have := (protData_range hRp hb).1; omega
    · have := (protData_range hRc hb).1; omega
    · omega
  have hpsync : ∀ b v, (protData Xp P b ∨ protData Xc C b ∨
      (4096 * (P.txid % 2) ≤ b ∧ b < 4096 * (P.txid % 2) + 4096)) →
      PSync ⟨m, bs, fa, fb, .idle⟩ b v → ∀ busy : CBusy,
      (∀ t off data n, busy = .write t off data n →
        4096 * (C.txid % 2) ≤ off ∧ off + data.length ≤ 4096 * (C.txid % 2) + 4096) →
      PSync ⟨m', bs', fa, fb, busy⟩ b v := by
    intro b v hb hps busy hbusy
    refine ⟨?_, fun t off data n he => ?_⟩
    · have h1 : bs[b]? = some (durB v) := hps.1
      show bs'[b]? = _; rw [hout b (hprot b hb)]; exact h1
    · have := hprot b hb; have := hbusy t off data n he; omega
  -- the slot's bytes in the reached state
  have hslot : ∃ N' : Option Nat, (N' = none → nn = 0) ∧ ∀ k < 4096, ∃ x,
      bs'[4096 * (C.txid % 2) + k]? = some x ∧
      CandOV x.2 (xb Xp (4096 * (C.txid % 2) + k)) (xb Xc (4096 * (C.txid % 2) + k)) N' := by
    clear hpsync hout hs hlo' hhi' hl' hnn hxs'
    induction hR with
    | refl =>
      refine ⟨N, fun _ => rfl, fun k hk => ?_⟩
      obtain ⟨c, hc, hov⟩ := hfl k hk
      rw [crashCands_lt ⟨m, bs, fa, fb, .idle⟩ rfl _ (by show _ < m.size; omega)] at hc
      obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.1 hc
      exact ⟨x, hx, hov⟩
    | @step nn0 m0 bs0 k nn' n zs hW0 hnn hk hnn' hzs hZ hPF ih =>
      obtain ⟨N', hN', hsl'⟩ := ih
      obtain ⟨hs0, -, -, hl0, -, -, -⟩ := wreach_inside hW0 hin hl hlo hhi
      exact ⟨some (N'.getD n), (fun h => by cases h),
        metaSlot_step (o := fun j => xb Xp (4096 * (C.txid % 2) + j))
          (v := fun j => xb Xc (4096 * (C.txid % 2) + j)) (by omega) hlen (by omega)
          (by rw [hlen] at hnn; exact hnn) hk hdat hN' hPF hsl'⟩
  obtain ⟨N', hN', hsl'⟩ := hslot
  have hd : ((C.slot C.txid).drop nn).length = 4096 - nn := by simp [hlen]
  refine ⟨⟨⟨by show bs'.length = m'.size; rw [hs]; exact hl', trivial, by show m'.lo ≤ m'.size; omega,
      by show m'.size ≤ m'.hi; omega⟩, hRp, hRc, htx, hsl,
    fun k hk => hpsync _ _ (.inr (.inr ⟨by omega, by omega⟩)) (hslotp k hk) _
      (fun _ _ _ _ h => by cases h),
    ⟨N', fun k hk => ?_⟩,
    fun b hb => hpsync _ _ (.inl hb) (hdp b hb) _ (fun _ _ _ _ h => by cases h),
    fun b hb => hpsync _ _ (.inr (.inl hb)) (hdc b hb) _ (fun _ _ _ _ h => by cases h),
    Nat.le_trans hhp' (Nat.le_of_eq hlo'.symm), Nat.le_trans hhc' (Nat.le_of_eq hlo'.symm),
    by show m'.size % 4096 = 0; rw [hs]; exact hal',
    by show m'.lo = m'.size; omega, by show m'.hi = m'.size; omega, fun _ _ _ _ h => by cases h⟩,
    fun hlt t n hPF => ⟨⟨by show bs'.length = m'.size; rw [hs]; exact hl', by show _ ≤ m'.size; omega,
      by show m'.lo ≤ m'.size; omega, by show m'.size ≤ m'.hi; omega⟩, hRp, hRc, htx, hsl,
    fun k hk => hpsync _ _ (.inr (.inr ⟨by omega, by omega⟩)) (hslotp k hk) _
      (fun _ _ _ _ he => by cases he; rw [hd]; omega),
    ⟨some (N'.getD n), fun k hk => ?_⟩,
    fun b hb => hpsync _ _ (.inl hb) (hdp b hb) _ (fun _ _ _ _ he => by cases he; rw [hd]; omega),
    fun b hb => hpsync _ _ (.inr (.inl hb)) (hdc b hb) _
      (fun _ _ _ _ he => by cases he; rw [hd]; omega),
    Nat.le_trans hhp' (Nat.le_of_eq hlo'.symm), Nat.le_trans hhc' (Nat.le_of_eq hlo'.symm),
    by show m'.size % 4096 = 0; rw [hs]; exact hal',
    by show (cfMeta m' _ _).lo = m'.size; rw [cfMeta_lo, hd]; omega,
    by show (cfMeta m' _ _).hi = m'.size; rw [cfMeta_hi, hd]; omega,
    fun t' off' data' n' he => by
      cases he; show _ + ((C.slot C.txid).drop nn).length ≤ m'.size; rw [hd]; omega⟩⟩
  · obtain ⟨x, hx, hov⟩ := hsl' k hk
    refine ⟨x.2, ?_, hov⟩
    rw [crashCands_lt ⟨m', bs', fa, fb, .idle⟩ rfl _ (by show _ < m'.size; omega)]
    show (bs'[_]?).map Prod.snd = _
    rw [hx]; rfl
  · obtain ⟨x, hx, hov⟩ := hsl' k hk
    have hbase : crashCands ⟨m', bs', fa, fb, .idle⟩ (4096 * (C.txid % 2) + k) = some x.2 := by
      rw [crashCands_lt ⟨m', bs', fa, fb, .idle⟩ rfl _ (by show _ < m'.size; omega)]
      show (bs'[_]?).map Prod.snd = _
      rw [hx]; rfl
    rw [crashCands_write, hbase]
    by_cases hkn : nn ≤ k
    · rw [if_pos (by
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
        rw [Nat.min_eq_left (by omega), hd]; omega), if_pos (by omega)]
      refine ⟨_, rfl, ?_⟩
      have hv : ((C.slot C.txid).drop nn).getD (4096 * (C.txid % 2) + k -
          (4096 * (C.txid % 2) + nn)) 0 = xb Xc (4096 * (C.txid % 2) + k) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
          show nn + (4096 * (C.txid % 2) + k - (4096 * (C.txid % 2) + nn)) = k by omega,
          ← List.getD_eq_getElem?_getD, hdat k hk]
      rw [hv]
      have hxr : (cfRange m' bs' (4096 * (C.txid % 2) + nn)
          ((C.slot C.txid).drop nn).length).getD (k - nn) (0, []) = x := by
        rw [cfRange_getD (by omega) (by omega) (by rw [hd]; omega)]
        rw [List.getElem?_eq_getElem (by omega)] at hx
        simp only [Option.some.injEq] at hx
        simp only [show 4096 * (C.txid % 2) + nn + (k - nn) = 4096 * (C.txid % 2) + k by omega]
        exact hx
      refine candOV_snoc hov (fun q hq => hPF.1 x ?_ q hq)
      rw [← hxr]
      exact getD_mem' _ _ _ (by rw [cfRange_length (by omega) (by omega), hd]; omega)
    · rw [if_neg (by
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
        rw [Nat.min_eq_left (by omega)]; omega)]
      refine ⟨x.2, rfl, ?_⟩
      cases N' with
      | none => exact absurd (hN' rfl) (by omega)
      | some N0 => exact hov

/-! ## The second sync of a commit -/

/-- **`writeMeta`'s `fdatasync` ends the commit** (`tx.go:621`): from the committing facts, the
new meta page written whole (its page-cache bytes the new slot's), a sync gives the idle facts of
the new committed state. -/
theorem bDur_sync_commit (a : BAbs) (ha : a.phase = .committing) (m : OsMeta) (H F T : List ByteG)
    (fa fb : Nat) (hF : ∀ y ∈ F, y = durB y.1) (h : BDur a ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)
    (hw : ∀ k < 4096, ((H ++ (F ++ T))[4096 * (a.cur.txid % 2) + k]?).map Prod.fst =
      some (xb a.xcur (4096 * (a.cur.txid % 2) + k))) :
    BDur { cur := a.cur, prev := a.prev, xcur := a.xcur, xprev := a.xprev, phase := .idle }
      (csSynced m H F T fa fb) := by
  rw [bDur_commit_iff ha] at h
  rw [bDur_idle_iff rfl]
  show BWf _ ∧ IdleOk a.cur a.xcur _
  generalize a.cur = C at h hw ⊢
  generalize a.prev = P at h ⊢
  generalize a.xcur = Xc at h hw ⊢
  generalize a.xprev = Xp at h ⊢
  obtain ⟨hW, hRp, hRc, htx, hsl, hslotp, -, hdp, hdc, hhp, hhc, hal, hvlo, hvhi, -⟩ := h
  have hl : (H ++ (F ++ T)).length = m.size := hW.1
  have hvlo' : m.lo = m.size := hvlo
  have hhc' : C.hwm * 4096 ≤ m.lo := hhc
  have hal' : m.size % 4096 = 0 := hal
  have h3 := refImg_hwm hRc
  have hP3 := refImg_hwm hRp
  have hXcl := hRc.len
  have hXpl := hRp.len
  have hpj : (C.txid + 1) % 2 = P.txid % 2 := by rw [htx]; omega
  have hsb := csSynced_bs m H F T fa fb hF
  -- `prev`'s slot is `cur`'s other slot
  have hslx : ∀ b, 4096 * (P.txid % 2) ≤ b → b < 4096 * (P.txid % 2) + 4096 → xb Xp b = xb Xc b := by
    intro b h1 h2
    have e := hsl
    rw [refImg_slot hRc, refImg_slot hRp, hpj] at e
    have e1 := bytesAt_getD Xp (4096 * (P.txid % 2)) (b - 4096 * (P.txid % 2)) (by omega) (by omega)
    have e2 := bytesAt_getD Xc (4096 * (P.txid % 2)) (b - 4096 * (P.txid % 2)) (by omega) (by omega)
    rw [show 4096 * (P.txid % 2) + (b - 4096 * (P.txid % 2)) = b by omega] at e1 e2
    rw [← e1, ← e2, e]
  refine ⟨csSynced_bwf m H F T fa fb hl, hRc, fun b hb => ⟨?_, fun _ _ _ _ h => by cases h⟩,
    fun b hb => ⟨?_, fun _ _ _ _ h => by cases h⟩, Nat.le_trans hhc' (Nat.le_of_eq hvlo'), hal',
    (fun _ _ _ _ h => by cases h), csSynced_xsAl m H F T fa fb hal'⟩
  · rw [hsb]
    rcases (show (4096 * (P.txid % 2) ≤ b ∧ b < 4096 * (P.txid % 2) + 4096) ∨
        (4096 * (C.txid % 2) ≤ b ∧ b < 4096 * (C.txid % 2) + 4096) by omega) with hb' | hb'
    · have hx : (H ++ (F ++ T))[b]? = some (durB (xb Xp b)) := by
        have := (hslotp (b - 4096 * (P.txid % 2)) (by omega)).1
        rw [show 4096 * (P.txid % 2) + (b - 4096 * (P.txid % 2)) = b by omega] at this
        exact this
      rw [hx, hslx b hb'.1 hb'.2]; rfl
    · have := hw (b - 4096 * (C.txid % 2)) (by omega)
      rw [show 4096 * (C.txid % 2) + (b - 4096 * (C.txid % 2)) = b by omega] at this
      obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.1 this
      rw [hx]; simp only [Option.map_some, hx1]
  · have hx : (H ++ (F ++ T))[b]? = some (durB (xb Xc b)) := (hdc b hb).1
    rw [hsb, hx]; rfl

/-! ## `init` -/

/-- The attempt in flight of an `init` write keeps the init facts. -/
theorem initOk_inflight {m0 : OsMeta} {bs0 : List ByteG} {fa fb off nn0 t n : Nat}
    {data : List w8} (hend : off + data.length ≤ 16384)
    (hdata : ∀ b, off ≤ b → data.getD (b - off) 0 = 0 ∨ data.getD (b - off) 0 = initByte b)
    (hnn : nn0 ≤ data.length) (hon : off + nn0 ≤ m0.size)
    (hW : BWf ⟨m0, bs0, fa, fb, .idle⟩) (hI : InitOk ⟨m0, bs0, fa, fb, .idle⟩) :
    BWf ⟨m0, bs0, fa, fb, .write t (off + nn0) (data.drop nn0) n⟩ ∧
      InitOk ⟨m0, bs0, fa, fb, .write t (off + nn0) (data.drop nn0) n⟩ := by
  obtain ⟨hc, hcache, hvhi⟩ := hI
  have hmhi : m0.hi ≤ 16384 := hvhi
  have hhi0 : m0.size ≤ m0.hi := hW.2.2.2
  have hd : (data.drop nn0).length = data.length - nn0 := List.length_drop
  refine ⟨⟨hW.1, hon, hW.2.2.1, hW.2.2.2⟩, fun b hb => ?_, hcache, ?_⟩
  · obtain ⟨c, hcb, hq⟩ := hc b hb
    rw [crashCands_write, hcb]
    by_cases hr : inRange (min (off + nn0) m0.size) (off + nn0 + (data.drop nn0).length) b = true
    · rw [if_pos hr]
      by_cases hle : off + nn0 ≤ b
      · refine ⟨c ++ [((data.drop nn0).getD (b - (off + nn0)) 0, n)], by rw [if_pos hle]; rfl,
          fun q hq' => ?_⟩
        rcases List.mem_append.1 hq' with hq' | hq'
        · exact hq q hq'
        · simp only [List.mem_singleton] at hq'
          rw [hq']
          show (data.drop nn0).getD (b - (off + nn0)) 0 = 0 ∨ _
          rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
            show nn0 + (b - (off + nn0)) = b - off by omega, ← List.getD_eq_getElem?_getD]
          exact hdata b (by omega)
      · refine ⟨c ++ [(0, n)], by rw [if_neg hle]; rfl, fun q hq' => ?_⟩
        rcases List.mem_append.1 hq' with hq' | hq'
        · exact hq q hq'
        · simp only [List.mem_singleton] at hq'
          rw [hq']; exact .inl rfl
    · rw [if_neg hr]; exact ⟨c, rfl, hq⟩
  · show (cfMeta m0 _ _).hi ≤ 16384
    rw [cfMeta_hi, hd]; omega

/-- **`init`'s writes keep the init facts** (`db.go:713`, `:722`): a write from `off`, inside the
first four pages, of bytes each zero or `init`'s, in every state of `WReach`. -/
theorem bDur_write_init (a : BAbs) (ha : a.phase = .init) (m : OsMeta) (bs : List ByteG)
    (fa fb off : Nat) (data : List w8) (h : BDur a ⟨m, bs, fa, fb, .idle⟩) (hoff : off ≤ m.size)
    (hend : off + data.length ≤ 16384)
    (hdata : ∀ b, off ≤ b → data.getD (b - off) 0 = 0 ∨ data.getD (b - off) 0 = initByte b)
    (nn : Nat) (m' : OsMeta) (bs' : List ByteG) (hR : WReach m bs off data nn m' bs') :
    BDur a ⟨m', bs', fa, fb, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off + nn) (data.drop nn) n →
      BDur a ⟨m', bs', fa, fb, .write t (off + nn) (data.drop nn) n⟩) := by
  simp only [bDur_init_iff ha] at h ⊢
  -- the reached states
  have hreach : BWf ⟨m', bs', fa, fb, .idle⟩ ∧ InitOk ⟨m', bs', fa, fb, .idle⟩ ∧
      off + nn ≤ m'.size ∧ nn ≤ data.length := by
    induction hR with
    | refl => exact ⟨h.1, h.2, hoff, Nat.zero_le _⟩
    | @step nn0 m0 bs0 k nn' n zs _ hnn hk hnn' hzs hZ _ ih =>
      obtain ⟨hW0, hI0, hon, -⟩ := ih
      obtain ⟨-, hIf⟩ := initOk_inflight (t := 0) (n := n) hend hdata (by omega) hon hW0 hI0
      have hl : bs0.length = m0.size := hW0.1
      have hlo : m0.lo ≤ m0.size := hW0.2.2.1
      have hhi : m0.size ≤ m0.hi := hW0.2.2.2
      have hmhi : m0.hi ≤ 16384 := hI0.2.2
      have hd : (data.drop nn0).length = data.length - nn0 := List.length_drop
      have hpw1 : m0.size ≤ pwSize m0.size (off + nn0) k := by unfold pwSize; split <;> omega
      have hpw2 : pwSize m0.size (off + nn0) k ≤ max m0.size (off + nn0 + (data.length - nn0)) := by
        unfold pwSize; split <;> omega
      have hpw3 : off + nn' ≤ pwSize m0.size (off + nn0) k := by
        unfold pwSize; split <;> omega
      refine ⟨⟨?_, trivial, ?_, ?_⟩, ⟨fun b hb => ?_, fun b x hx => ?_, ?_⟩, ?_, by omega⟩
      · show (finBytes _ _ _ _ _ _ _).length = (pwPostK true _ _ _ _ _).size
        rw [finBytes_length hl hon (by omega), pwPostK_size]
      · show (pwPostK true _ _ _ _ _).lo ≤ (pwPostK true _ _ _ _ _).size
        rw [pwPostK_lo, pwPostK_size]; omega
      · show (pwPostK true _ _ _ _ _).size ≤ (pwPostK true _ _ _ _ _).hi
        rw [pwPostK_hi, pwPostK_size, hd]; omega
      · obtain ⟨c, hc, hq⟩ := hIf.1 b hb
        exact ⟨c, cands_landed hl hon (by omega) hzs hZ b c hc, hq⟩
      · rcases finBytes_val hl hon (by omega) b x hx with ⟨y, hy, hxy⟩ | ⟨hle, hxv⟩ | h0
        · rw [hxy]; exact hI0.2.1 b y hy
        · rw [hxv, List.getD_eq_getElem?_getD, List.getElem?_drop,
            show nn0 + (b - (off + nn0)) = b - off by omega, ← List.getD_eq_getElem?_getD]
          exact hdata b (by omega)
        · exact .inl h0
      · show (pwPostK true _ _ _ _ _).hi ≤ 16384
        rw [pwPostK_hi, hd]; omega
      · show off + nn' ≤ (pwPostK true _ _ _ _ _).size
        rw [pwPostK_size]; exact hpw3
  obtain ⟨hW', hI', hon', hnn'⟩ := hreach
  exact ⟨⟨hW', hI'⟩, fun hlt t n _ => initOk_inflight hend hdata hnn' hon' hW' hI'⟩

/-- **`init`'s first `fdatasync` keeps the init facts** (`db.go:717`), the file being four pages. -/
theorem bDur_sync_init (a : BAbs) (ha : a.phase = .init) (m : OsMeta) (H F T : List ByteG)
    (fa fb : Nat) (hF : ∀ y ∈ F, y = durB y.1) (h : BDur a ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)
    (hsz : m.size = 16384) : BDur a (csSynced m H F T fa fb) := by
  rw [bDur_init_iff ha] at h ⊢
  obtain ⟨hW, -, hcache, -⟩ := h
  have hl : (H ++ (F ++ T)).length = m.size := hW.1
  have hcache' : ∀ b x, (H ++ (F ++ T))[b]? = some x → x.1 = 0 ∨ x.1 = initByte b := hcache
  have hsb := csSynced_bs m H F T fa fb hF
  refine ⟨csSynced_bwf m H F T fa fb hl, fun b hb => ?_, fun b x hx => ?_, ?_⟩
  · have hbl : b < (H ++ (F ++ T)).length := by omega
    obtain ⟨y, hy⟩ : ∃ y, (H ++ (F ++ T))[b]? = some y := ⟨_, List.getElem?_eq_getElem hbl⟩
    refine ⟨[(y.1, 0)], ?_, fun q hq => ?_⟩
    · rw [crashCands_lt (csSynced m H F T fa fb) rfl _ (by show b < m.size; omega), hsb, hy]; rfl
    · simp only [List.mem_singleton] at hq; rw [hq]; exact hcache' b y hy
  · rw [hsb] at hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.1 hx
    exact hcache' b y hy
  · show m.size ≤ 16384; omega

/-- **`init`'s second `fdatasync` ends it** (`db.go:726`): the file being `init`'s image in the page
cache, a sync gives the idle facts of `init`'s committed state `initC`. -/
theorem bDur_init_done (a : BAbs) (ha : a.phase = .init) (m : OsMeta) (H F T : List ByteG)
    (fa fb : Nat) (hF : ∀ y ∈ F, y = durB y.1) (h : BDur a ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)
    (hsz : m.size = 16384)
    (himg : ∀ b < 16384, ((H ++ (F ++ T))[b]?).map Prod.fst = some (initByte b)) :
    BDur { cur := initC, prev := initC, xcur := initImg, xprev := initImg, phase := .idle }
      (csSynced m H F T fa fb) := by
  rw [bDur_init_iff ha] at h
  rw [bDur_idle_iff rfl]
  obtain ⟨hW, -⟩ := h
  have hl : (H ++ (F ++ T)).length = m.size := hW.1
  have hsb := csSynced_bs m H F T fa fb hF
  obtain ⟨hi, hm, ht, hfl, hh, h1, h2, -⟩ := initImg_ok
  have hR : RefImg initImg initC := ⟨hi, hm, ht, hfl, hh, h1, h2, initImg_tails⟩
  have hhwm : initC.hwm * 4096 ≤ m.size := by
    have h4 : initC.hwm = 4 := rfl
    rw [h4, hsz]; decide
  have hbyte : ∀ b < 16384, PSync (csSynced m H F T fa fb) b (xb initImg b) := by
    intro b hb
    refine ⟨?_, fun _ _ _ _ h => by cases h⟩
    rw [hsb]
    obtain ⟨x, hx, hx1⟩ := Option.map_eq_some_iff.1 (himg b hb)
    rw [hx]; simp only [Option.map_some, hx1]; rfl
  exact ⟨csSynced_bwf m H F T fa fb hl, hR, fun b hb => hbyte b (by omega),
    fun b hb => hbyte b (by
      have := (protData_range hR hb).2; rw [show initC.hwm = 4 from rfl] at this; omega),
    hhwm, by show m.size % 4096 = 0; simp [hsz], (fun _ _ _ _ h => by cases h),
    csSynced_xsAl m H F T fa fb (by simp [hsz])⟩

end phases

end bbolt
end EtcdGrove
end Perennial
