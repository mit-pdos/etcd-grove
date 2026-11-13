/- Lean-first (no Rocq counterpart). minibolt's crash obligations on the per-byte model:
`FileOkS P1 Good i s` for a state `s` of the database file (`Proof/os/CrashSt.lean`), reduced to a
statement on the file a crash leaves (`CrashImg`).

**What a crash leaves.** Each byte of the file comes back as one of its candidates, or zero at or
past the smallest size since the last sync (`CrashFile`), which the client knows exactly (`CSt.kc`): below the size the bytes it holds (`bs`, with their
candidates), past it those the `OsMeta` knows (`tc`: the bytes past the size in its last page as a
crash left them on disk, and those a write left there), each with the change in flight's
announced value over its range (`kc_cand`). P1 (`BootP1.lean`) adds that a meta slot that
validates is the slot as of one change: each of its bytes the value of its candidates as of one
stamp (`valAt`). Nothing else is assumed: a slot that mixes two states is the case P1 excludes.
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs.BootP1
public import LinuxFs.Proof.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace osfs_bboltfs

open Iris Fs github_com.mit_pdos.etcd_grove.examples.osfs.bboltfs

/-- The meta slot of page `i` of the bytes `l`: 64 bytes at offset 16. -/
def metaSlot (l : List w8) (i : Nat) : List w8 := ((l.drop (4096 * i)).drop 16).take 64

/-- The client's change in flight starts inside the file (a write; a truncate grows it). -/
def BusyOk (s : CSt) : Prop :=
  match s.busy with
  | .write _ off _ _ => off ≤ s.m.size
  | _ => True

/-- The candidates of byte `b` of the state `s` before its change in flight: its own below the
size, the `OsMeta`'s past it. -/
def _root_.Perennial.CSt.baseC (s : CSt) (b : Nat) : Option Cands :=
  if b < s.m.size then (s.bs[b]?).map Prod.snd else s.m.pc b

/-- **The candidates of byte `b` a crash of the state `s` picks from**, as far as the client knows
them: `baseC`, with the value the change in flight announced over its range, stamped with its
number. -/
def _root_.Perennial.CSt.kc (s : CSt) (b : Nat) : Option Cands :=
  match s.busy with
  | .idle => s.baseC b
  | .write _ off data n =>
    if inRange (min off s.m.size) (off + data.length) b then
      (s.baseC b).map (· ++ [(if off ≤ b then data.getD (b - off) 0 else 0, n)])
    else s.baseC b
  | .trunc _ sz n =>
    if inRange (min s.m.size sz) (rsHi true s.m.size sz) b then (s.baseC b).map (· ++ [((0 : w8), n)])
    else s.baseC b

section pure
variable [GooseExts]

theorem _root_.Perennial.CSt.vmeta_size (s : CSt) : s.vmeta.size = s.m.size := by
  unfold CSt.vmeta; split <;> simp [cfMeta]

/-- An announce does not change what `pc` knows past the range it announces. -/
theorem announce_pc_out (m : OsMeta) (lo hi tg b : Nat) (c : Cands)
    (hr : ¬ (inRange lo hi b = true)) (hlo : lo ≤ b) (h : m.pc b = some c) :
    (m.announce lo hi tg).pc b = some c := by
  have hb : hi ≤ b := by simp only [inRange, Bool.and_eq_true, decide_eq_true_eq] at hr; omega
  unfold OsMeta.pc at h ⊢
  rw [announce_tc, if_neg hr]
  cases ht : m.tc !! b with
  | some c' => rw [ht] at h; exact h
  | none =>
    rw [ht] at h
    simp only [announce_zf]
    cases hz : m.zf with
    | none => rw [hz] at h; cases h
    | some z =>
      rw [hz] at h
      simp only [Option.map_some]
      dsimp only at h ⊢
      by_cases hzb : z ≤ b
      · rw [if_pos hzb] at h
        rw [if_pos (by split <;> omega)]; exact h
      · rw [if_neg hzb] at h; cases h

/-- A byte below the size that no write in flight took, from the runs. -/
theorem _root_.Perennial.CSt.runs_mem (s : CSt) (b : Nat) (hb : b < s.bs.length) (ht : s.taken b = false) :
    (b, s.frac b, [s.bs[b]]) ∈ s.vruns := by
  obtain ⟨r, hr, e⟩ := s.runs_getElem b hb
  rw [ht] at e; simp only [Bool.false_eq_true, if_false] at e
  subst e
  unfold CSt.vruns; split <;> simp [hr]

/-- **The candidates the client knows are the file's**, at the crash `CrashSeenR` records. -/
theorem kc_cand {Q : OsState → OsState → Prop} {i : Ino} {s : CSt} {fo : Option OsFile}
    (hwf : s.Wf) (hcut0 : s.m.cut = none) (hbz : BusyOk s)
    (h : CrashSeenR Q i s.vmeta s.vruns (s.toks i) fo) :
    ∃ (st st' : OsState) (f : OsFile), OsCrash st st' ∧ Q st st' ∧ st'.fs.files !! i = fo ∧
      st.fs.files !! i = some f ∧ s.vmeta.lo ≤ f.sizeLo ∧
      ∀ b c, s.kc b = some c → f.cand b = c := by
  obtain ⟨st, st', Γb, Γm, Γf, Γt, hwfs, hcoh, hcr, hQ, hfo, hm, hrs, -, hts⟩ := h
  obtain ⟨f, hf, hmo⟩ := hcoh.meta_some i _ hm
  refine ⟨st, st', f, hcr, hQ, hfo, hf, hmo.lo, ?_⟩
  have hl : s.bs.length = s.m.size := hwf.1
  have hsz : f.size = s.m.size := by rw [← hmo.size, CSt.vmeta_size]
  -- a byte a run holds
  have hrun : ∀ r ∈ s.vruns, ∀ k (hk : k < r.2.2.length), f.cand (r.1 + k) = (r.2.2[k]).2 := by
    intro r hr k hk
    have hcut : cutOf Γm i = none := by
      simp only [cutOf, hm, Option.bind_some]; exact s.vmeta_cut ▸ hcut0
    obtain ⟨f1, hf1, -, hx⟩ := coh_byte_exact hcoh hcut (hrs r hr k hk)
    have : f1 = f := by
      have h1 : st.fs.files !! i = some f1 := hf1
      rw [hf] at h1; cases h1; rfl
    subst this; rw [hx]
  -- a byte below the size no write took
  have hown : ∀ b, b < s.m.size → s.taken b = false → ∀ c, s.baseC b = some c → f.cand b = c := by
    intro b hb ht c hc
    have hbl : b < s.bs.length := by omega
    have := hrun _ (s.runs_mem b hbl ht) 0 (by simp)
    simp only [Nat.add_zero, List.getElem_cons_zero] at this
    rw [this]
    unfold CSt.baseC at hc
    rw [if_pos hb, List.getElem?_eq_getElem hbl] at hc
    simp only [Option.map_some, Option.some.injEq] at hc
    exact hc
  -- a byte past the size, out of the change in flight's range
  have hpast : ∀ b, s.m.size ≤ b → ∀ c, s.vmeta.pc b = some c → f.cand b = c := by
    intro b hb c hc
    exact hmo.pc_cand b c (by omega) hc
  -- the change in flight's token
  have htok : ∀ t ti, (t, ti) ∈ s.toks i → ∃ f1, st.fs.files !! ti.ino = some f1 ∧
      ∀ b, inRange ti.lo ti.hi b = true → ∃ c0, f1.cand b = c0 ++ [(ti.val b, ti.n)] ∧
        ∀ c, ti.m0.size ≤ b → ti.m0.pc b = some c → c0 = c := by
    intro t ti hti
    obtain ⟨f1, hf1, hc⟩ := hcoh.tok_cand t ti (hts _ hti)
    exact ⟨f1, hf1, fun b hb => by
      obtain ⟨c0, h1, h2, h3⟩ := hc b hb
      refine ⟨c0, h1, fun c hb' hpc => ?_⟩
      rcases OsMeta.pc_some hpc with ht | ⟨z, hz, hzb, rfl⟩
      · exact h3 c hb' ht
      · exact h2 z hz hzb⟩
  intro b c hc
  rcases hbs : s.busy with _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩ <;> simp only [CSt.kc, hbs] at hc
  · -- idle
    have ht : s.taken b = false := by simp [CSt.taken, hbs]
    by_cases hb : b < s.m.size
    · exact hown b hb ht c hc
    · unfold CSt.baseC at hc; rw [if_neg hb] at hc
      exact hpast b (by omega) c (by simp only [CSt.vmeta, hbs]; exact hc)
  · -- a write
    have hoff : off ≤ s.m.size := by unfold BusyOk at hbz; rw [hbs] at hbz; exact hbz
    have hmin : min off s.m.size = off := Nat.min_eq_left hoff
    split at hc
    · rename_i hr
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hmin] at hr
      obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.1 hc
      by_cases hb : b < s.m.size
      · -- taken: the write's run
        have hrun0 := hrun (cfLo s.m off, DFrac.own 1, pwAnn data n (cfRange s.m s.bs off data.length))
          (by simp [CSt.vruns, hbs]) (b - off)
          (by simp only [pwAnn_length, cfRange, cfLo, cfHi, List.length_take, List.length_drop]; omega)
        simp only [cfLo, hmin, show off + (b - off) = b by omega] at hrun0
        rw [hrun0, pwAnn_getElem]
        unfold CSt.baseC at hc1
        rw [if_pos hb, List.getElem?_eq_getElem (by omega)] at hc1
        simp only [Option.map_some, Option.some.injEq] at hc1
        simp only [cfRange, cfLo, hmin, List.getElem_take, List.getElem_drop,
          show off + (b - off) = b by omega, hc1, if_pos hr.1]
      · -- past the size: the token
        obtain ⟨f1, hf1, hcand⟩ := htok t
          ⟨i, .write off data, n, s.m, pwAnn data n (cfRange s.m s.bs off data.length)⟩
          (by simp [CSt.toks, hbs])
        simp only at hf1
        rw [hf] at hf1; cases hf1
        obtain ⟨c0, h1, h2⟩ := hcand b (by
          simp only [TokInfo.lo, TokInfo.hi, inRange, Bool.and_eq_true, decide_eq_true_eq, hmin]
          exact ⟨hr.1, decide_eq_true hr.2⟩)
        unfold CSt.baseC at hc1; rw [if_neg hb] at hc1
        rw [h1, h2 c1 (by simp only; omega) hc1]
        simp only [TokInfo.val]
    · rename_i hr
      by_cases hb : b < s.m.size
      · refine hown b hb ?_ c hc
        simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, hmin] at hr
        unfold CSt.taken; rw [hbs]; simp only [cfLo, cfHi]
        exact decide_eq_false (by omega)
      · unfold CSt.baseC at hc; rw [if_neg hb] at hc
        refine hpast b (by omega) c ?_
        simp only [CSt.vmeta, hbs, cfMeta]
        exact announce_pc_out _ _ _ _ _ _ hr (by omega) hc
  · -- a growing truncate
    have hgrow : s.m.size ≤ sz := by have := hwf.2.2.2; simp only [hbs] at this; exact this
    split at hc
    · rename_i hr
      simp only [inRange, Bool.and_eq_true, decide_eq_true_eq, Nat.min_eq_left hgrow] at hr
      obtain ⟨c1, hc1, rfl⟩ := Option.map_eq_some_iff.1 hc
      obtain ⟨f1, hf1, hcand⟩ := htok t ⟨i, rsKind true sz, n, s.m, rsAnn n []⟩
        (by simp [CSt.toks, hbs])
      simp only at hf1
      rw [hf] at hf1; cases hf1
      obtain ⟨c0, h1, h2⟩ := hcand b (by
        simp only [rsKind_lo, rsKind_hi, inRange, Bool.and_eq_true, decide_eq_true_eq,
          Nat.min_eq_left hgrow]; omega)
      unfold CSt.baseC at hc1; rw [if_neg (by omega)] at hc1
      rw [h1, h2 c1 (by simp only; omega) hc1]
      simp only [rsKind_val]
    · rename_i hr
      by_cases hb : b < s.m.size
      · exact hown b hb (by simp [CSt.taken, hbs]) c hc
      · unfold CSt.baseC at hc; rw [if_neg hb] at hc
        refine hpast b (by omega) c ?_
        simp only [CSt.vmeta, hbs]
        exact announce_pc_out _ _ _ _ _ _ hr (by omega) hc

/-- **What a crash of the state `s` leaves** (`f`): a file on disk, within the size bounds, each
byte in a page that holds one of the file (the size's last page included) one of its known
candidates or, at or past the bounds' smallest size, zero (writeback's zeroing), and each meta slot that validates, whose bytes' candidates are known, the slot as of
one stamp (P1). -/
structure CrashImg (s : CSt) (f : OsFile) : Prop where
  disk : ∃ img, f = OsFile.ofDisk img f.size
  lo : s.vmeta.lo ≤ f.size
  hi : f.size ≤ s.vmeta.hi
  byte : ∀ b c, pageIn f.size b = true → s.kc b = some c →
    (∃ q, (f.cache b, q) ∈ c) ∨ (s.vmeta.lo ≤ b ∧ f.cache b = 0)
  slot : ∀ j < 2, 4096 * j < f.size → metaValid (decode (rawSlot f j) : Meta) →
    (∀ k < 64, (s.kc (4096 * j + 16 + k)).isSome) →
    ∃ n, ∀ k < 64, ∀ c, s.kc (4096 * j + 16 + k) = some c → f.cache (4096 * j + 16 + k) = valAt c n

/-- A crash's file, as `CrashImg` says it. -/
theorem crashImg_of {i : Ino} {s : CSt} {f : OsFile} (hwf : s.Wf) (hcut : s.m.cut = none)
    (hbz : BusyOk s)
    (hfc : FileCrashedR s.vmeta s.vruns (some f))
    (h : CrashSeenR P1 i s.vmeta s.vruns (s.toks i) (some f)) : CrashImg s f := by
  obtain ⟨hdisk, hlo, hhi, -, -⟩ := hfc f rfl
  obtain ⟨st, st', f0, hcr, hQ, hfo, hf0, hlo0, hkc⟩ := kc_cand hwf hcut hbz h
  -- the crash's file
  have hn : Named st'.fs.treeDur i := by
    apply Classical.byContradiction; intro hn
    rw [(hcr.2.2.2.2.2.2.2 i).2 hn] at hfo; cases hfo
  obtain ⟨f1, f2, hf1, ⟨sz, img, -, hcand, rfl⟩, hf2⟩ := (hcr.2.2.2.2.2.2.2 i).1 hn
  rw [hf0] at hf1; cases hf1
  rw [hfo] at hf2; cases hf2
  refine ⟨hdisk, hlo, hhi, fun b c hpg hc => ?_, fun j hj hsz hv _ => ?_⟩
  · simp only [OsFile.ofDisk, diskByte] at hpg ⊢
    rw [if_pos hpg]
    rcases hcand b with ⟨q, hq⟩ | ⟨hl, h0⟩
    · exact .inl ⟨q, by rw [← hkc b c hc]; exact hq⟩
    · exact .inr ⟨Nat.le_trans hlo0 hl, h0⟩
  · obtain ⟨n, hn⟩ := hQ i f0 _ hf0 hfo j hj hsz hv
    exact ⟨n, fun k hk c hc => by rw [hn k hk, hkc _ c hc]⟩

/-- **The obligation of a state, from its crashes' files** (see the file header): every crash of
the state `s` is `Good` if every file `CrashImg` allows is (`Good` of a file on disk). -/
theorem fileOkS_of {i : Ino} (s : CSt) (hwf : s.Wf) (hbz : BusyOk s)
    (H : ∀ f, CrashImg s f → goodImg f.contents ∧ RawOk f) : FileOkS P1 Good i s :=
  fun hcut f hfc hseen =>
    let hI := crashImg_of hwf hcut hbz hfc hseen
    let h := H f hI
    ⟨h.1, h.2, let ⟨img, he⟩ := hI.disk; ⟨img, f.size, he⟩⟩

end pure

end osfs_bboltfs
end EtcdGrove
end Perennial

end
