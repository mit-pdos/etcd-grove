/-
The extension's operations over a file in the generic crash invariant (`Proof/os/CrashSt.lean`):
each opens the invariant around its one step (`fsOp_atomic`; `cs_open`, which closes it again
with a state of the same file, so the tree's part holds as it did), applies the extension-level
spec to the invariant's and the caller's parts put together, and closes it with the new state, of
which the caller shows `Ok`. The caller's part is of the file only (`csOwnF`), but for the create,
which needs the history (`csOwn`). Lean-first (no Rocq counterpart).

* `wp_osOpenCreate_cs`: no file at `p = d/b`, the create (the invariant's half of the history and
  the caller's make it whole), to the new file (`csNew`); on failure maybe.
* `wp_osPWriteStart_cs`/`wp_osPWriteFinish_cs`: idle to a write in flight (inside the file, and
  missing the frozen bytes), and back to idle, as the write of the first `k` bytes left it.
* `wp_osFtruncateStart_cs`/`wp_osFtruncateFinish_cs`: idle to a growing truncate in flight, and
  back to idle, grown (by bytes `zs`, zeros if the `OsMeta` says so) or (on failure) with the size
  bound widened and the versions known forgotten (`ftFail`).
* `wp_osFsync_cs`: idle to synced: the bytes after the frozen ones (`[fb, size)`), keeping the
  ones before them (`[0, fa)`, shown clean) in the durable bytes known (`OsMeta.syncedKeep`);
  or the ones before them (`hd`). On failure, `ok` is lost.
* `wp_osMmap_cs`/`wp_osMunmap_cs`: the mappings change.
* `cs_freeze`: more bytes frozen (a ghost step), the caller getting their discarded copies.
-/
module

public import LinuxFs.Proof.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-! ## Bytes -/

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem list_split3 {α : Type} (l : List α) (a b : Nat) (hab : a ≤ b) :
    l = l.take a ++ ((l.drop a).take (b - a) ++ l.drop b) := by
  have : l.drop b = (l.drop a).drop (b - a) := by rw [List.drop_drop]; congr 1; omega
  rw [this, List.take_append_drop, List.take_append_drop]

/-- Bytes in three segments, `[0, a)`, `[a, b)`, `[b, ...)`. -/
theorem cBytes_split3 (p : Ino) (d : Nat → DFrac) (c : Nat → Bool) (a b : Nat)
    (l : List ByteG) (hab : a ≤ b) (hbl : b ≤ l.length) :
    cBytes (L := L) p d c 0 l ⊣⊢ cBytes (L := L) p d c 0 (l.take a) ∗
      cBytes (L := L) p d c a ((l.drop a).take (b - a)) ∗ cBytes (L := L) p d c b (l.drop b) := by
  have A1 := cBytes_append (L := L) p d c 0 (l.take a) ((l.drop a).take (b - a) ++ l.drop b)
  rw [show 0 + (l.take a).length = a by simp only [List.length_take]; omega] at A1
  have A2 := cBytes_append (L := L) p d c a ((l.drop a).take (b - a)) (l.drop b)
  rw [show a + ((l.drop a).take (b - a)).length = b by
    simp only [List.length_take, List.length_drop]; omega] at A2
  conv => lhs; rw [list_split3 l a b hab]
  exact A1.trans (sep_congr .rfl A2)

/-- A range of bytes out of a set of them, at the fraction it has there. -/
theorem cBytes_takeRange (p : Ino) (d : Nat → DFrac) (c c' : Nat → Bool) (dq : DFrac)
    (lo hi : Nat) (l : List ByteG) (hlh : lo ≤ hi) (hhl : hi ≤ l.length)
    (hc : ∀ k, c' k = (c k && !decide (lo ≤ k ∧ k < hi)))
    (hR : ∀ k, lo ≤ k → k < hi → c k = true ∧ d k = dq) :
    cBytes (L := L) p d c 0 l ⊣⊢
      cBytes (L := L) p d c' 0 l ∗ osBytes (L := L) p lo dq ((l.drop lo).take (hi - lo)) := by
  refine (cBytes_split3 p d c lo hi l hlh hhl).trans (BiEntails.trans ?_
    (sep_congr (cBytes_split3 p d c' lo hi l hlh hhl).symm .rfl))
  have e1 : cBytes (L := L) p d c 0 (l.take lo) ⊣⊢ cBytes (L := L) p d c' 0 (l.take lo) :=
    cBytes_congr p d d c c' 0 _ fun k hk => by
      simp only [List.length_take] at hk
      refine ⟨?_, fun _ => rfl⟩
      rw [hc]; have : ¬ (lo ≤ k ∧ k < hi) := by omega
      simp [this]
  have e3 : cBytes (L := L) p d c hi (l.drop hi) ⊣⊢ cBytes (L := L) p d c' hi (l.drop hi) :=
    cBytes_congr p d d c c' hi _ fun k hk => by
      refine ⟨?_, fun _ => rfl⟩
      rw [hc]; have : ¬ (lo ≤ hi + k ∧ hi + k < hi) := by omega
      simp [this]
  have e2 : cBytes (L := L) p d c lo ((l.drop lo).take (hi - lo)) ⊣⊢
      osBytes (L := L) p lo dq ((l.drop lo).take (hi - lo)) :=
    cBytes_full p d c dq lo _ fun k hk => by
      simp only [List.length_take, List.length_drop] at hk
      exact hR _ (by omega) (by omega)
  have e2' : cBytes (L := L) p d c' lo ((l.drop lo).take (hi - lo)) ⊣⊢ emp :=
    cBytes_none p d c' lo _ fun k hk => by
      simp only [List.length_take, List.length_drop] at hk
      rw [hc]; have : lo ≤ lo + k ∧ lo + k < hi := by omega
      simp [this]
  refine (sep_congr e1 (sep_congr e2 e3)).trans ?_
  refine BiEntails.trans ?_ (sep_congr (sep_congr .rfl (sep_congr e2' .rfl)) .rfl).symm
  exact ⟨by iintro ⟨H1, H2, H3⟩; iframe, by iintro ⟨⟨H1, -, H3⟩, H2⟩; iframe⟩

/-- After a write: the bytes before and after its range as they were, and its range (which may
reach past the old end) at one fraction. -/
theorem cBytes_fin (p : Ino) (d d2 : Nat → DFrac) (c c2 : Nat → Bool) (dq : DFrac)
    (m : OsMeta) (bs : List ByteG) (off : Nat) (data : List w8) (k n : Nat) (zs : List Cands)
    (hl : bs.length = m.size)
    (hA : ∀ j < cfLo m off, c j = c2 j ∧ (c j = true → d j = d2 j))
    (hC : ∀ j, cfHi m off data.length ≤ j → c j = c2 j ∧ (c j = true → d j = d2 j))
    (hR : ∀ j, cfLo m off ≤ j → j < cfHi m off data.length → c j = false)
    (hP : ∀ j, cfLo m off ≤ j →
      j < cfLo m off + (pwBytes m.size off data k n (cfRange m bs off data.length) zs).length →
      c2 j = true ∧ d2 j = dq) :
    cBytes (L := L) p d c 0 bs ∗
      osBytes (L := L) p (cfLo m off) dq (pwBytes m.size off data k n (cfRange m bs off data.length) zs) ⊢
      cBytes (L := L) p d2 c2 0 (finBytes m bs off data k n zs) := by
  have hlh : cfLo m off ≤ cfHi m off data.length := by unfold cfLo cfHi; omega
  have hhs : cfHi m off data.length ≤ bs.length := by unfold cfHi; omega
  have hhi : cfLo m off + (pwBytes m.size off data k n (cfRange m bs off data.length) zs).length =
      cfHi m off data.length ∨ bs.drop (cfHi m off data.length) = [] := by
    rw [pwBytes_length]
    have := pwSize_ge3 m.size off k
    by_cases hs : off + data.length ≤ m.size
    · left; unfold cfHi cfLo pwSize; split <;> omega
    · right; apply List.drop_eq_nil_of_le; unfold cfHi; omega
  unfold finBytes
  generalize hpw : pwBytes m.size off data k n (cfRange m bs off data.length) zs = pw at hP hhi ⊢
  refine BIBase.Entails.trans (sep_mono (cBytes_split3 (L := L) p d c _ _ bs hlh hhs).1 .rfl) ?_
  refine BIBase.Entails.trans ?_ (cBytes_append (L := L) p d2 c2 0 _ _).2
  refine BIBase.Entails.trans ?_ (sep_mono (cBytes_append (L := L) p d2 c2 0 _ _).2 .rfl)
  have hla : 0 + (bs.take (cfLo m off)).length = cfLo m off := by
    simp only [List.length_take]; unfold cfLo; omega
  have hlb : 0 + (bs.take (cfLo m off) ++ pw).length = cfLo m off + pw.length := by
    simp only [List.length_append, List.length_take]; unfold cfLo; omega
  rw [hla, hlb]
  have eA := cBytes_congr (L := L) p d d2 c c2 0 (bs.take (cfLo m off)) fun j hj => by
    simp only [List.length_take] at hj; simp only [Nat.zero_add]; exact hA j (by omega)
  have eR := cBytes_none (L := L) p d c (cfLo m off)
    ((bs.drop (cfLo m off)).take (cfHi m off data.length - cfLo m off)) fun j hj => by
      simp only [List.length_take, List.length_drop] at hj; exact hR _ (by omega) (by omega)
  have eP := cBytes_full (L := L) p d2 c2 dq (cfLo m off) pw fun j hj => hP _ (by omega) (by omega)
  have eC : cBytes (L := L) p d c (cfHi m off data.length) (bs.drop (cfHi m off data.length)) ⊢
      cBytes (L := L) p d2 c2 (cfLo m off + pw.length) (bs.drop (cfHi m off data.length)) := by
    rcases hhi with h | h
    · rw [h]; exact (cBytes_congr (L := L) p d d2 c c2 _ _ fun j _ => hC _ (by omega)).1
    · rw [h]; exact .rfl
  iintro ⟨⟨HA, HR, HC⟩, HP⟩
  ihave HA := eA.1 $$ HA
  ihave HC := eC $$ HC
  ihave HP := eP.2 $$ HP
  iframe

theorem bigSepL_bupd {A : Type} {Φ : Nat → A → IProp GF} :
    ∀ (l : List A), ([∗list] k ↦ x ∈ l, |==> Φ k x) ⊢ |==> [∗list] k ↦ x ∈ l, Φ k x
  | [] => by iintro -; imodintro; iapply BigSepL.bigSepL_nil.2; iempintro
  | x :: l => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H2⟩
    imod H1 with H1
    imod bigSepL_bupd (Φ := fun k x => Φ (k + 1) x) l $$ H2 with H2
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe

/-- Byte `k` is not frozen: a byte in `[lo, hi)`, with `[lo, hi)` before `fa` or from `fb` on. -/
theorem not_frozen {fa fb lo hi k : Nat} (h : hi ≤ fa ∨ fb ≤ lo) (h1 : lo ≤ k) (h2 : k < hi) :
    decide (fa ≤ k ∧ k < fb) = false := by
  simp only [decide_eq_false_iff_not]; omega

/-- An idle state's bytes, in three segments: before the frozen ones, frozen, after. -/
theorem idle_invBytes (p : Ino) (m : OsMeta) (H F T : List ByteG) (fa fb : Nat)
    (hH : H.length = fa) (hF : fa + F.length = fb) :
    invBytes (L := L) p ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ ⊣⊢
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) H ∗ osBytes (L := L) p fa DFrac.discard F ∗
      osBytes (L := L) p fb (DFrac.own (1 : Qp).half) T := by
  unfold invBytes
  refine (cBytes_append (L := L) p _ _ 0 H (F ++ T)).trans (sep_congr ?_ ?_)
  · exact cBytes_full p _ _ _ 0 H fun k hk => ⟨rfl, CSt.frac_out _ _ (by dsimp only; omega)⟩
  · rw [show 0 + H.length = fa by omega]
    refine (cBytes_append (L := L) p _ _ fa F T).trans (sep_congr ?_ ?_)
    · exact cBytes_full p _ _ _ fa F fun k hk =>
        ⟨rfl, CSt.frac_in _ _ (by dsimp only; omega) (by dsimp only; omega)⟩
    · rw [hF]
      exact cBytes_full p _ _ _ fb T fun k hk => ⟨rfl, CSt.frac_out _ _ (by dsimp only; omega)⟩

theorem idle_thrBytes (p : Ino) (m : OsMeta) (H F T : List ByteG) (fa fb : Nat)
    (hH : H.length = fa) (hF : fa + F.length = fb) :
    thrBytes (L := L) p ⟨m, H ++ (F ++ T), fa, fb, .idle⟩ ⊣⊢
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) H ∗
      osBytes (L := L) p fb (DFrac.own (1 : Qp).half) T := by
  unfold thrBytes
  refine (cBytes_append (L := L) p _ _ 0 H (F ++ T)).trans ?_
  rw [show 0 + H.length = fa by omega]
  refine (sep_congr .rfl (cBytes_append (L := L) p _ _ fa F T)).trans ?_
  rw [hF]
  refine (sep_congr ?_ (sep_congr ?_ ?_)).trans
    (⟨by iintro ⟨H1, -, H3⟩; iframe, by iintro ⟨H1, H3⟩; iframe⟩ :
      osBytes (L := L) p 0 (DFrac.own (1 : Qp).half) H ∗ (emp ∗
        osBytes (L := L) p fb (DFrac.own (1 : Qp).half) T) ⊣⊢ _)
  · exact cBytes_full p _ _ _ 0 H fun k hk =>
      ⟨by rw [CSt.frozen_out _ _ (by dsimp only; omega)]; rfl, rfl⟩
  · exact cBytes_none p _ _ fa F fun k hk => by
      rw [CSt.frozen_in _ _ (by dsimp only; omega) (by dsimp only; omega)]; simp
  · exact cBytes_full p _ _ _ fb T fun k hk =>
      ⟨by rw [CSt.frozen_out _ _ (by dsimp only; omega)]; rfl, rfl⟩

/-- A write's range out of an idle state's bytes (it misses the frozen ones): the invariant's
half... -/
theorem write_invBytes (p : Ino) (m : OsMeta) (bs : List ByteG) (fa fb t off : Nat)
    (data : List w8) (n : Nat) (hl : bs.length = m.size) (hfb : fb ≤ m.size)
    (hfz : off + data.length ≤ fa ∨ fb ≤ off) :
    invBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ ⊣⊢
      invBytes (L := L) p ⟨m, bs, fa, fb, .write t off data n⟩ ∗
      osBytes (L := L) p (cfLo m off) (DFrac.own (1 : Qp).half) (cfRange m bs off data.length) := by
  unfold invBytes
  refine cBytes_takeRange p _ _ _ _ _ _ bs (by unfold cfLo cfHi; omega) (by unfold cfHi; omega)
    (fun k => by simp [CSt.taken]) (fun k h1 h2 =>
      ⟨rfl, CSt.frac_out _ _ (by dsimp only; simp only [cfLo, cfHi] at h1 h2; omega)⟩)

/-- ... and the caller's. -/
theorem write_thrBytes (p : Ino) (m : OsMeta) (bs : List ByteG) (fa fb t off : Nat)
    (data : List w8) (n : Nat) (hl : bs.length = m.size) (hfb : fb ≤ m.size)
    (hfz : off + data.length ≤ fa ∨ fb ≤ off) :
    thrBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ ⊣⊢
      thrBytes (L := L) p ⟨m, bs, fa, fb, .write t off data n⟩ ∗
      osBytes (L := L) p (cfLo m off) (DFrac.own (1 : Qp).half) (cfRange m bs off data.length) := by
  unfold thrBytes
  refine cBytes_takeRange p _ _ _ _ _ _ bs (by unfold cfLo cfHi; omega) (by unfold cfHi; omega)
    (fun k => by simp only [CSt.taken, Bool.not_false, Bool.true_and]; rw [Bool.and_comm]; rfl)
    (fun k h1 h2 =>
      ⟨by rw [CSt.frozen_out _ _ (by dsimp only; simp only [cfLo, cfHi] at h1 h2; omega)]; rfl, rfl⟩)

end bytes

/-! ## The operations -/

/-- The state of a file just created, of inode `i`: empty, idle, nothing frozen. -/
def csNew (i : Ino) : CState := some (i, ⟨newMeta, [], 0, 0, .idle⟩)

/-- The state of the file at `d/b` and the history after an `open(O_CREAT)` of it succeeds, from
the state `s` and the history `V`, the file being `i`: created (`d` being the directory `j`) if `s`
has none, unchanged otherwise. -/
def csOpenSt (j : Ino) (b : GoString) (V : Hist) (i : Ino) : CState → CState × Hist
  | none => (csNew i, V.push ⟨.create j b i, V.2.length⟩)
  | some x => (some x, V)

/-- The state after a successful sync of an idle state `H ++ (F ++ T)` (`F` frozen, durable): every
byte durable. -/
def csSynced (m : OsMeta) (H F T : List ByteG) (fa fb : Nat) : CSt :=
  ⟨m.synced, H.map (fun x => durB x.1) ++ (F ++ T.map (fun x => durB x.1)), fa, fb, .idle⟩

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem csOwnF_idle (p : Ino) (γ : GName) (s : CSt) (hb : s.busy = .idle) :
    csOwnF (L := L) γ (some (p, s)) ⊣⊢ ghostVar γ (1 : Qp).half (some (p, s) : CState) ∗
      (osMeta (L := L) p (DFrac.own (1 : Qp).half) s.m ∗ thrBytes (L := L) p s) ∗ ⌜s.Wf⌝ := by
  obtain ⟨m, bs, fa, fb, busy⟩ := s
  dsimp only at hb; subst hb; exact .rfl

theorem csOwnF_busy (p : Ino) (γ : GName) (s : CSt) (hb : s.busy ≠ .idle) :
    csOwnF (L := L) γ (some (p, s)) ⊣⊢ ghostVar γ (1 : Qp).half (some (p, s) : CState) ∗
      thrBytes (L := L) p s ∗ ⌜s.Wf⌝ := by
  obtain ⟨m, bs, fa, fb, _ | ⟨t, off, data, n⟩ | ⟨t, sz, n⟩⟩ := s
  · exact absurd rfl hb
  all_goals exact sep_congr .rfl (sep_congr emp_sep .rfl)

theorem invResS_idle (p : Ino) (s : CSt) (hb : s.busy = .idle) :
    invResS (L := L) (some (p, s)) ⊣⊢
      osMeta (L := L) p (DFrac.own (1 : Qp).half) s.m ∗ invBytes (L := L) p s := by
  obtain ⟨m, bs, fa, fb, busy⟩ := s
  dsimp only at hb; subst hb; exact .rfl

/-- The invariant's state, from the caller's: they agree. The invariant closes again with a state
of the same file (its tree's part, `TreeOkI`, depends on the inode only). -/
theorem cs_open (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (s : CState) (E : CoPset) (hE : ↑N ⊆ E) :
    ⊢ csInv (L := L) N P R γ Good Ok -∗ ghostVar γ (1 : Qp).half s ={E, E \ ↑N}=∗
      ghostVar γ (1 : Qp).half s ∗ invResS (L := L) s ∗ ghostVar γ (1 : Qp).half s ∗ ⌜Ok s ∧ CsCut s⌝ ∗
      (▷ (∃ s', ghostVar γ (1 : Qp).half s' ∗ invResS (L := L) s' ∗ ⌜Ok s' ∧ sIno s' = sIno s ∧ CsCut s'⌝)
        ={E \ ↑N, E}=∗ True) := by
  iintro #Hinv Hv
  unfold csInv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', %V, >Hv', >Hr, >Ht, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  imodintro
  iframe Hv Hr Hv'
  isplitr
  · ipureintro; exact ⟨Hok'.1, Hok'.2.2⟩
  iintro H
  icases H with ⟨%s2, >Hv2, >Hr2, >%Hok2⟩
  iapply Hclose
  inext
  iexists s2, V
  iframe
  ipureintro
  exact ⟨Hok2.1, by rw [Hok2.2.1]; exact Hok'.2.1, Hok2.2.2⟩

/-- `pwrite`'s first step on a file in a crash invariant, idle: the write (which misses the
frozen bytes, starts inside the file and is not empty) is in flight, which the caller shows `Ok`
(for any token and change number). -/
theorem wp_osPWriteStart_cs (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta) (bs : List ByteG)
    (fa fb : Nat) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hgap : off.toNat ≤ m.size) (hd : data ≠ []) (hfz : off.toNat + data.length ≤ fa ∨ fb ≤ off.toNat)
    (hok : ∀ t n, PwFresh m bs off.toNat data n →
      Ok (some (d.ino, ⟨m, bs, fa, fb, .write t off.toNat data n⟩))) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N P R γ Good Ok -∗ osFd (L := L) fd dq d -∗
      csOwnF (L := L) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)) -∗
      mcellsAny (L := L) m.maps (cfLo m off.toNat) (off.toNat + data.length) -∗
      (∀ t : Nat, ∀ n : Nat, ⌜PwFresh m bs off.toNat data n⌝ -∗ osFd (L := L) fd dq d -∗
        csOwnF (L := L) γ (some (d.ino, ⟨m, bs, fa, fb, .write t off.toNat data n⟩)) -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown Hc HΦ
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  have hlo : cfLo m off.toNat = off.toNat := Nat.min_eq_left hgap
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_open N P R γ Good Ok _ ⊤ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv
    with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (write_invBytes d.ino m bs fa fb 0 off.toNat data 0 hl hfb hfz).1 $$ Hb2 with ⟨Hb2, Hr2⟩
  icases (write_thrBytes d.ino m bs fa fb 0 off.toNat data 0 hl hfb hfz).1 $$ Hb1 with ⟨Hb1, Hr1⟩
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hr1 Hr2]
  · iframe
  ihave Hrg := (show osBytes (L := L) d.ino (cfLo m off.toNat) (DFrac.own 1)
      (cfRange m bs off.toNat data.length) ⊢ osBytes (L := L) d.ino off.toNat
      (DFrac.own 1) (cfRange m bs off.toNat data.length) by rw [hlo]) $$ Hrg
  imodintro
  ihave Hc := (show mcellsAny (L := L) m.maps (cfLo m off.toNat) (off.toNat + data.length) ⊢
      mcellsAny (L := L) m.maps off.toNat (off.toNat + data.length) by rw [hlo]) $$ Hc
  iapply wp_osPWriteStart fd off data dq d m (cfRange m bs off.toNat data.length) hN hwr hoff
    hgap hd (by unfold cfRange cfLo cfHi; simp only [List.length_take, List.length_drop]; omega)
    $$ Hos Hfd Hm Hrg Hc
  iintro %t %n %hfr Hfd Ht
  imod ghostVar_update_halves (some (d.ino, ⟨m, bs, fa, fb, .write t off.toNat data n⟩) : CState) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Ht Hb2] with -
  · inext; iexists (some (d.ino, ⟨m, bs, fa, fb, .write t off.toNat data n⟩)); iframe Hv'; isplitl
    · dsimp only [invResS, metaRes]; isplitl [Ht]
      · iexact Ht
      · iapply (show invBytes (L := L) d.ino ⟨m, bs, fa, fb, .write 0 off.toNat data 0⟩ ⊢
          invBytes (L := L) d.ino ⟨m, bs, fa, fb, .write t off.toNat data n⟩ from .rfl)
        iexact Hb2
    ipureintro; exact ⟨hok t n hfr, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
  imodintro
  iapply HΦ $$ %t %n %hfr Hfd
  iapply (csOwnF_busy _ _ _ (by simp)).2
  isplitl [Hv]
  · iexact Hv
  isplitl [Hb1]
  · iapply (show thrBytes (L := L) d.ino ⟨m, bs, fa, fb, .write 0 off.toNat data 0⟩ ⊢
      thrBytes (L := L) d.ino ⟨m, bs, fa, fb, .write t off.toNat data n⟩ from .rfl)
    iexact Hb1
  ipureintro; exact ⟨hl, hab, hfb, hfz⟩

/-- `pwrite`'s second step on a file in a crash invariant: idle again, as the write of the first
`k` bytes left it (`finBytes`: the bytes it reached past the old end with the candidates `zs`),
which the caller shows `Ok`. -/
theorem wp_osPWriteFinish_cs (t : Nat) (p : Ino) (off : Nat) (data : List w8) (n : Nat)
    (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta) (bs : List ByteG)
    (fa fb : Nat) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : ∀ k (zs : List Cands), k ≤ data.length → off ≤ m.size →
      zs.length = pwSize m.size off k - m.size → ZsOk m zs →
      Ok (some (p, ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩)))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N P R γ Good Ok -∗
      csOwnF (L := L) γ (some (p, ⟨m, bs, fa, fb, .write t off data n⟩)) -∗
      (∀ (k : Nat) (e : w64) (zs : List Cands),
        ⌜k ≤ data.length ∧ ((k = data.length ∨ 0 < k) ∧ e = 0 ∨ e ≠ 0) ∧ off ≤ m.size ∧
          zs.length = pwSize m.size off k - m.size ∧ ZsOk m zs⌝ -∗
        csOwnF (L := L) γ (some (p, ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb,
          .idle⟩)) -∗
        mcells (L := L) m.maps (cfLo m off) (off + data.length)
          (pwCell m.size off data k (cfRange m bs off data.length)) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp fsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hos #Hinv Hown HΦ
  icases (csOwnF_busy _ _ _ (by simp)).1 $$ Hown with ⟨Hv, Hb1, %Hwf⟩
  obtain ⟨hl, hab, hfb, hfz⟩ := Hwf
  dsimp only at hl hab hfb hfz
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_open N P R γ Good Ok _ ⊤ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv
    with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  dsimp only [invResS, metaRes]
  icases Hr with ⟨Ht, Hb2⟩
  unfold pwTok
  icases Ht with ⟨Ht, %hpw⟩
  obtain ⟨hgap, hd, hxl⟩ := hpw
  have hlo : cfLo m off = off := Nat.min_eq_left hgap
  imodintro
  iapply wp_osPWriteFinishK true t p off data m (cfRange m bs off data.length) n hN $$ Hos [Ht]
  · unfold pwTok; iframe; ipureintro; exact ⟨hgap, hd, hxl⟩
  iintro %k %e %zs %hke %hzt %- Hm Hrg Hc
  have hk := hke.1
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  ihave Hr1 := (show osBytes (L := L) p off (DFrac.own (1 : Qp).half)
      (pwBytes m.size off data k n (cfRange m bs off data.length) zs) ⊢
      osBytes (L := L) p (cfLo m off) (DFrac.own (1 : Qp).half)
      (pwBytes m.size off data k n (cfRange m bs off data.length) zs) by rw [hlo]) $$ Hr1
  ihave Hr2 := (show osBytes (L := L) p off (DFrac.own (1 : Qp).half)
      (pwBytes m.size off data k n (cfRange m bs off data.length) zs) ⊢
      osBytes (L := L) p (cfLo m off) (DFrac.own (1 : Qp).half)
      (pwBytes m.size off data k n (cfRange m bs off data.length) zs) by rw [hlo]) $$ Hr2
  have hlo2 : fb ≤ off → fb ≤ cfLo m off := fun h => by unfold cfLo; omega
  have hout : ∀ j, (j < cfLo m off ∨ cfHi m off data.length ≤ j) →
      CSt.taken ⟨m, bs, fa, fb, .write t off data n⟩ j = false := fun j hj =>
    CSt.taken_out _ j (fun t' o d' n' h => by cases h; omega)
  have hpl : cfLo m off + (pwBytes m.size off data k n (cfRange m bs off data.length) zs).length ≤
      off + data.length := by
    rw [pwBytes_length]; unfold cfLo; omega
  ihave Hb2 := (show invBytes (L := L) p ⟨m, bs, fa, fb, .write t off data n⟩ ⊢
      cBytes (L := L) p (CSt.frac ⟨m, bs, fa, fb, .write t off data n⟩)
      (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data n⟩ j) 0 bs from .rfl) $$ Hb2
  ihave Hb2 := cBytes_fin (L := L) p (CSt.frac ⟨m, bs, fa, fb, .write t off data n⟩)
    (CSt.frac ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩)
    (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data n⟩ j)
    (fun j => !CSt.taken ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ j)
    (DFrac.own (1 : Qp).half) m bs off data k n zs hl
    (fun j hj => ⟨by rw [hout j (.inl hj)]; rfl, fun _ => rfl⟩)
    (fun j hj => ⟨by rw [hout j (.inr hj)]; rfl, fun _ => rfl⟩)
    (fun j h1 h2 => by rw [CSt.taken_in _ j t off data n rfl h1 h2]; rfl)
    (fun j h1 h2 => ⟨rfl, CSt.frac_out _ _ (by dsimp only; have := hlo2; omega)⟩) $$ [Hb2 Hr2]
  · iframe
  ihave Hb2 := (show cBytes (L := L) p
      (CSt.frac ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩)
      (fun j => !CSt.taken ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ j) 0
      (finBytes m bs off data k n zs) ⊢
      invBytes (L := L) p ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩
      from .rfl) $$ Hb2
  ihave Hb1 := (show thrBytes (L := L) p ⟨m, bs, fa, fb, .write t off data n⟩ ⊢
      cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half)
      (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data n⟩ j &&
        !CSt.frozen ⟨m, bs, fa, fb, .write t off data n⟩ j) 0 bs from .rfl) $$ Hb1
  ihave Hb1 := cBytes_fin (L := L) p (fun _ => DFrac.own (1 : Qp).half) (fun _ => DFrac.own (1 : Qp).half)
    (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data n⟩ j &&
      !CSt.frozen ⟨m, bs, fa, fb, .write t off data n⟩ j)
    (fun j => !CSt.taken ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ j &&
      !CSt.frozen ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ j)
    (DFrac.own (1 : Qp).half) m bs off data k n zs hl
    (fun j hj => ⟨by rw [hout j (.inl hj)]; rfl, fun _ => rfl⟩)
    (fun j hj => ⟨by rw [hout j (.inr hj)]; rfl, fun _ => rfl⟩)
    (fun j h1 h2 => by rw [CSt.taken_in _ j t off data n rfl h1 h2]; rfl)
    (fun j h1 h2 => ⟨by rw [CSt.frozen_out _ _ (by dsimp only; have := hlo2; omega)]; rfl,
      rfl⟩) $$ [Hb1 Hr1]
  · iframe
  ihave Hb1 := (show cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half)
      (fun j => !CSt.taken ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ j &&
        !CSt.frozen ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩ j) 0
      (finBytes m bs off data k n zs) ⊢
      thrBytes (L := L) p ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩
      from .rfl) $$ Hb1
  imod ghostVar_update_halves
    (some (p, ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩) : CState) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hm2 Hb2] with -
  · inext; iexists (some (p, ⟨pwPostK true m off data k n, finBytes m bs off data k n zs, fa, fb, .idle⟩))
    iframe Hv'; isplitl
    · dsimp only; iframe
    ipureintro; exact ⟨hok k zs hk hgap hke.2.2.1 hzt, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
  imodintro
  ihave Hc := (show mcells (L := L) m.maps off (off + data.length)
      (pwCell m.size off data k (cfRange m bs off data.length)) ⊢ mcells (L := L) m.maps (cfLo m off)
      (off + data.length) (pwCell m.size off data k (cfRange m bs off data.length)) by rw [hlo]) $$ Hc
  iapply HΦ $$ %k %e %zs %(⟨hk, hke.2.1, hgap, hke.2.2.1, hzt⟩) [Hv Hm1 Hb1] Hc
  iapply (csOwnF_idle _ _ _ rfl).2
  iframe
  ipureintro
  refine ⟨finBytes_length hl hgap hk, hab, ?_, trivial⟩
  show fb ≤ pwSize m.size off k
  have := pwSize_ge3 m.size off k; omega

/-! ### Truncate -/

/-- Grown bytes: the old ones and the new ones (`zb`). -/
theorem grow_bytes (p : Ino) (m m' : OsMeta) (bs : List ByteG) (fa fb t sz n : Nat)
    (zb : List ByteG) (hfb : fb ≤ bs.length) :
    osBytes (L := L) p bs.length (DFrac.own 1) (zb) ∗
      invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ ∗ thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ ⊢
    invBytes (L := L) p ⟨m', bs ++ zb, fa, fb, .idle⟩ ∗ thrBytes (L := L) p ⟨m', bs ++ zb, fa, fb, .idle⟩ := by
  iintro ⟨Hz, Hi, Ht⟩
  icases (osBytes_halves (L := L) p _ _).1 $$ Hz with ⟨Hz1, Hz2⟩
  ihave Hi := (show invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ ⊢ cBytes (L := L) p (CSt.frac (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt))
    (fun k => !CSt.taken (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt) k) 0 bs from .rfl) $$ Hi
  ihave Ht := (show thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ ⊢ cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half)
    (fun k => !CSt.taken (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt) k && !CSt.frozen (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt) k) 0 bs from .rfl) $$ Ht
  ihave Hz1 := (cBytes_full (L := L) p (CSt.frac (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt)) (fun k => !CSt.taken (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt) k) _
    bs.length _ fun k hk => ⟨rfl, CSt.frac_out _ _ (by dsimp only; omega)⟩).2 $$ Hz1
  ihave Hz2 := (cBytes_full (L := L) p (fun _ => DFrac.own (1 : Qp).half)
    (fun k => !CSt.taken (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt) k && !CSt.frozen (⟨m', bs ++ zb, fa, fb, .idle⟩ : CSt) k) _ bs.length _ fun k hk =>
      ⟨by rw [CSt.frozen_out _ _ (by dsimp only; omega)]; rfl, rfl⟩).2 $$ Hz2
  unfold invBytes thrBytes
  isplitl [Hz1 Hi]
  · iapply (cBytes_append (L := L) p _ _ 0 bs _).2; rw [Nat.zero_add]; iframe
  · iapply (cBytes_append (L := L) p _ _ 0 bs _).2; rw [Nat.zero_add]; iframe

/-- A growing truncate's first step on a file in a crash invariant, idle, with the client's halves
of the mapped cells of the bytes it grows the file over: the truncate is in flight, which the
caller shows `Ok` (for any token and change number). -/
theorem wp_osFtruncateStart_cs (fd sz : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (P : GoString)
    (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (Ok : CState → Prop) (m : OsMeta) (bs : List ByteG) (fa fb : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt)
    (hgrow : m.size ≤ sz.toNat)
    (hok : ∀ t n, Ok (some (d.ino, ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩))) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N P R γ Good Ok -∗ osFd (L := L) fd dq d -∗
      csOwnF (L := L) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)) -∗
      mcellsAny (L := L) m.maps m.size (rsHi true m.size sz.toNat) -∗
      (∀ t : Nat, ∀ n : Nat, osFd (L := L) fd dq d -∗
        csOwnF (L := L) γ (some (d.ino, ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩)) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown Hc HΦ
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  have hmin : min m.size sz.toNat = m.size := Nat.min_eq_left hgrow
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_open N P R γ Good Ok _ ⊤ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv
    with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply wp_osFtruncateStart fd sz dq d m [] hN hwr hsz0 (by simp; omega) $$ Hos Hfd Hm [] [Hc]
  · unfold osBytes; iapply (bytesG_nil _ _ _ _).2; iempintro
  · rw [hmin]; iexact Hc
  iintro %t %n %- Hfd Ht
  imod ghostVar_update_halves (some (d.ino, ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩) : CState) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Ht Hb2] with -
  · inext; iexists (some (d.ino, ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩)); iframe Hv'; isplitl
    · dsimp only [invResS, metaRes]; isplitl [Ht]
      · iexact Ht
      · iapply (show invBytes (L := L) d.ino ⟨m, bs, fa, fb, .idle⟩ ⊢
          invBytes (L := L) d.ino ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩ from .rfl)
        iexact Hb2
    ipureintro; exact ⟨hok t n, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
  imodintro
  iapply HΦ $$ %t %n Hfd
  iapply (csOwnF_busy _ _ _ (by simp)).2
  isplitl [Hv]
  · iexact Hv
  isplitl [Hb1]
  · iapply (show thrBytes (L := L) d.ino ⟨m, bs, fa, fb, .idle⟩ ⊢
      thrBytes (L := L) d.ino ⟨m, bs, fa, fb, .trunc t sz.toNat n⟩ from .rfl)
    iexact Hb1
  ipureintro; exact ⟨hl, hab, hfb, hgrow⟩

/-- The caller's part after a truncate grew the file (`rsDone`): the file, its new bytes (zeros,
with the candidates `zs` they had, then the zero the truncate announced), and the mapped cells of
the new bytes. -/
def csGrownOwn (p : Ino) (γ : GName) (m : OsMeta) (bs : List ByteG) (fa fb sz n : Nat) :
    IProp GF :=
  iprop(∃ zs : List Cands, ⌜zs.length = sz - m.size ∧
      ∀ j z, m.zf = some z → z ≤ m.size + j → j < zs.length → zs[j]? = some [(0, 0)]⌝ ∗
    csOwnF (L := L) γ (some (p, ⟨rsPost true m sz sz,
      bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])), fa, fb, .idle⟩)) ∗
    mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsCell sz))

/-- A growing truncate's second step on a file in a crash invariant: grown, or, on failure, maybe
not (its `OsMeta` as the first step announced it), each of which the caller shows `Ok`. -/
theorem wp_osFtruncateFinish_cs (t : Nat) (p : Ino) (sz n : Nat) (N : Namespace) (P : GoString)
    (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (Ok : CState → Prop) (m : OsMeta) (bs : List ByteG) (fa fb : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hokG : ∀ zs : List Cands, zs.length = sz - m.size →
      Ok (some (p, ⟨rsPost true m sz sz, bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])), fa, fb,
        .idle⟩)))
    (hokF : Ok (some (p, ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb, .idle⟩)))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N P R γ Good Ok -∗
      csOwnF (L := L) γ (some (p, ⟨m, bs, fa, fb, .trunc t sz n⟩)) -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csGrownOwn (L := L) p γ m bs fa fb sz n) ∨
         (⌜e ≠ 0⌝ ∗ (csGrownOwn (L := L) p γ m bs fa fb sz n ∨
           (csOwnF (L := L) γ (some (p, ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb,
              .idle⟩)) ∗
             mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsOld m.size m.size []))))) -∗
        Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hos #Hinv Hown HΦ
  icases (csOwnF_busy _ _ _ (by simp)).1 $$ Hown with ⟨Hv, Hb1, %Hwf⟩
  obtain ⟨hl, hab, hfb, hgrow⟩ := Hwf
  dsimp only at hl hab hfb hgrow
  have hmin : min m.size sz = m.size := Nat.min_eq_left hgrow
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_open N P R γ Good Ok _ ⊤ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv
    with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  icases (show invResS (L := L) (some (p, ⟨m, bs, fa, fb, .trunc t sz n⟩)) ⊢ rsTok (L := L) true t p sz m [] n ∗
    invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ from .rfl) $$ Hr with ⟨Ht, Hb2⟩
  imodintro
  iapply wp_osFtruncateFinish t p sz m [] n hN $$ Hos Ht
  iintro %e Hres
  -- the two outcomes, as states
  have hG : ∀ (Q : IProp GF), (csGrownOwn (L := L) p γ m bs fa fb sz n -∗ Q) ⊢
      ghostVar γ (1 : Qp).half (some (p, ⟨m, bs, fa, fb, .trunc t sz n⟩) : CState) -∗
      ghostVar γ (1 : Qp).half (some (p, ⟨m, bs, fa, fb, .trunc t sz n⟩) : CState) -∗
      invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ -∗ thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ -∗
      rsDone (L := L) true p sz sz m n -∗
      (▷ (∃ s', ghostVar γ (1 : Qp).half s' ∗ invResS (L := L) s' ∗
        ⌜Ok s' ∧ sIno s' = sIno (some (p, ⟨m, bs, fa, fb, .trunc t sz n⟩)) ∧ CsCut s'⌝) ={(⊤ : CoPset) \ ↑N, ⊤}=∗ True) -∗
      |={(⊤ : CoPset) \ ↑N, ⊤}=> Q := by
    intro Q
    iintro HQ Hv Hv' Hb2 Hb1 Hg Hclose
    unfold rsDone
    icases Hg with ⟨%zs, %hzs, Hm, Hz, Hc⟩
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    ihave Hz := (show osBytes (L := L) p m.size (DFrac.own 1)
        (zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) ⊢
      osBytes (L := L) p bs.length (DFrac.own 1) (zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)]))) by
        rw [hl]) $$ Hz
    icases grow_bytes (L := L) p m (rsPost true m sz sz) bs fa fb t sz n _ (by omega) $$ [Hz Hb2 Hb1]
      with ⟨Hb2, Hb1⟩
    · iframe
    imod ghostVar_update_halves
      (some (p, ⟨rsPost true m sz sz, bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])), fa, fb, .idle⟩) :
        CState) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some (p, ⟨rsPost true m sz sz, bs ++ zs.map (fun c0 => ((0 : w8), c0 ++ [(0, n)])),
        fa, fb, .idle⟩))
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe
      ipureintro; exact ⟨hokG zs hzs.1, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
    imodintro
    iapply HQ
    unfold csGrownOwn
    iexists zs
    ihave Hc := (show mcells (L := L) m.maps (min m.size sz) (rsHi true m.size sz) (rsCell sz) ⊢
      mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsCell sz) by rw [hmin]) $$ Hc
    iframe Hc
    isplitr
    · ipureintro; exact hzs
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe
    ipureintro
    refine ⟨by simp only [List.length_append, List.length_map, hl, hzs.1]; show _ = sz; omega, hab,
      by show fb ≤ sz; omega, trivial⟩
  unfold rsUndone
  icases Hres with (⟨%he, Hg⟩ | ⟨%he, (Hg | ⟨Hm, -, Hc⟩)⟩)
  · iapply (hG _) $$ [HΦ] Hv Hv' Hb2 Hb1 Hg Hclose
    iintro H; iapply HΦ; ileft; iframe; ipureintro; exact he
  · iapply (hG _) $$ [HΦ] Hv Hv' Hb2 Hb1 Hg Hclose
    iintro H; iapply HΦ; iright; isplitr; · ipureintro; exact he
    ileft; iexact H
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves
      (some (p, ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb, .idle⟩) : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some (p, ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb, .idle⟩))
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe Hm2
        iapply (show invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ ⊢
          invBytes (L := L) p ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb, .idle⟩
          from .rfl)
        iexact Hb2
      ipureintro; exact ⟨hokF, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
    imodintro
    iapply HΦ; iright; isplitr; · ipureintro; exact he
    iright
    ihave Hc := (show mcells (L := L) m.maps (min m.size sz) (rsHi true m.size sz)
        (rsOld m.size (min m.size sz) []) ⊢
      mcells (L := L) m.maps m.size (rsHi true m.size sz) (rsOld m.size m.size []) by rw [hmin]) $$ Hc
    iframe Hc
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe Hv Hm1
    isplitl
    · iapply (show thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz n⟩ ⊢
        thrBytes (L := L) p ⟨m.announce (min m.size sz) (rsHi true m.size sz) sz, bs, fa, fb, .idle⟩
        from .rfl)
      iexact Hb1
    ipureintro; exact ⟨by rw [announce_size]; exact hl, hab, by rw [announce_size]; exact hfb, trivial⟩

/-! ### Sync -/

/-- `fsync`/`fdatasync` of a file in a crash invariant, idle (`H ++ (F ++ T)`, `F` frozen and
durable): on success every byte is durable (`csSynced`), which the caller shows `Ok`; on failure
nothing changes. -/
theorem wp_osFsync_cs (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop)
    (Ok : CState → Prop) (m : OsMeta) (H F T : List ByteG) (fa fb : Nat)
    (hH : H.length = fa) (hF : fa + F.length = fb) (hFd : ∀ y ∈ F, y = durB y.1)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : Ok (some (d.ino, csSynced m H F T fa fb))) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N P R γ Good Ok -∗ osFd (L := L) fd dq d -∗
      csOwnF (L := L) γ (some (d.ino, ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)) -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwnF (L := L) γ (some (d.ino, csSynced m H F T fa fb))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗
           csOwnF (L := L) γ (some (d.ino, ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)))) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown HΦ
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_open N P R γ Good Ok _ ⊤ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv
    with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (idle_invBytes d.ino m H F T fa fb hH hF).1 $$ Hb2 with ⟨HH2, HF, HT2⟩
  icases (idle_thrBytes d.ino m H F T fa fb hH hF).1 $$ Hb1 with ⟨HH1, HT1⟩
  ihave HH := (osBytes_halves _ _ _).2 $$ [HH1 HH2]
  · iframe
  ihave HT := (osBytes_halves _ _ _).2 $$ [HT1 HT2]
  · iframe
  -- the bytes back, as a state
  have hback : ∀ (m' : OsMeta) (H' T' : List ByteG), H'.length = fa →
      osMeta (L := L) d.ino (DFrac.own 1) (m') ∗ osBytes (L := L) d.ino 0 (DFrac.own 1) H' ∗
        osBytes (L := L) d.ino fa DFrac.discard F ∗ osBytes (L := L) d.ino fb (DFrac.own 1) T' ⊢
      (osMeta (L := L) d.ino (DFrac.own (1 : Qp).half) (m') ∗
        invBytes (L := L) d.ino ⟨m', H' ++ (F ++ T'), fa, fb, .idle⟩) ∗
      (osMeta (L := L) d.ino (DFrac.own (1 : Qp).half) (m') ∗
        thrBytes (L := L) d.ino ⟨m', H' ++ (F ++ T'), fa, fb, .idle⟩) := by
    intro m' H' T' hH'
    iintro ⟨Hm, HH, HF, HT⟩
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ HH with ⟨HH1, HH2⟩
    icases (osBytes_halves _ _ _).1 $$ HT with ⟨HT1, HT2⟩
    iframe Hm1 Hm2
    isplitl [HH1 HF HT1]
    · iapply (idle_invBytes d.ino m' H' F T' fa fb hH' (by omega)).2; iframe
    · iapply (idle_thrBytes d.ino m' H' F T' fa fb hH' (by omega)).2; iframe
  imodintro
  have hlen : H.length + (F.length + T.length) = m.size := by
    simpa [List.length_append] using hl
  iapply wp_osFsync2 fd dq d m 0 H fb T [(fa, DFrac.discard, F)]
    (fun r hr y hy => by rw [List.mem_singleton] at hr; subst hr; exact hFd y hy)
    (fun b hb _ _ => by
      by_cases h1 : b < fa
      · exact .inl ⟨Nat.zero_le _, by omega⟩
      · by_cases h2 : b < fb
        · exact .inr (.inr ⟨_, List.mem_singleton_self _, by simp only; omega, by simp only; omega⟩)
        · exact .inr (.inl ⟨by omega, by omega⟩)) hN
    $$ Hos Hfd Hm HH HT [HF]
  · iapply BigSepL.bigSepL_singleton.2; iexact HF
  iintro %e Hres Hfd HF
  icases BigSepL.bigSepL_singleton.1 $$ HF with HF
  icases Hres with (⟨%he, Hm, HH, HT⟩ | ⟨%he, Hm, HH, HT⟩)
  · icases hback _ (H.map (fun x => durB x.1)) (T.map (fun x => durB x.1)) (by rw [List.length_map]; exact hH)
      $$ [Hm HH HF HT] with ⟨Hi, Ht⟩
    · iframe
    imod ghostVar_update_halves (some (d.ino, ⟨m.synced, H.map (fun x => durB x.1) ++ (F ++ T.map (fun x => durB x.1)), fa, fb, .idle⟩) : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hi] with -
    · inext; iexists (some (d.ino, ⟨m.synced, H.map (fun x => durB x.1) ++ (F ++ T.map (fun x => durB x.1)), fa, fb, .idle⟩)); iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iexact Hi
      ipureintro; exact ⟨hok, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
    imodintro
    iapply HΦ $$ %e [Hv Ht] Hfd
    ileft; isplitr; · ipureintro; exact he
    iapply (show csOwnF (L := L) γ (some (d.ino, ⟨m.synced, H.map (fun x => durB x.1) ++ (F ++ T.map (fun x => durB x.1)), fa, fb, .idle⟩)) ⊢
      csOwnF (L := L) γ (some (d.ino, csSynced m H F T fa fb)) from .rfl)
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe
    ipureintro
    refine ⟨?_, hab, ?_, trivial⟩ <;> simp only [OsMeta.synced, List.length_append, List.length_map]
    · omega
    · omega
  · icases hback m H T hH $$ [Hm HH HF HT] with ⟨Hi, Ht⟩
    · iframe
    imod ghostVar_update_halves (some (d.ino, ⟨m, H ++ (F ++ T), fa, fb, .idle⟩) : CState)
      γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hi] with -
    · inext; iexists (some (d.ino, ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)); iframe Hv'
      isplitl
      · iapply (invResS_idle _ _ rfl).2; iexact Hi
      ipureintro; exact ⟨Hok'.1, rfl, Hok'.2⟩
    imodintro
    iapply HΦ $$ %e [Hv Ht] Hfd
    iright; isplitr; · ipureintro; exact he
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩

/-! ### Mappings -/

/-- `mmap` of a file in a crash invariant, idle: on success, a new mapping (`Ok` shown by the
caller for any base), the file's bytes otherwise unchanged. -/
theorem wp_osMmap_cs (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace)
    (P : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta) (bs : List ByteG) (fa fb : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hrd : d.readable = true) (hoff : off = 0)
    (hlen : 0 < len.toInt) (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE)
    (hok : ∀ base : Loc, Ok (some (d.ino, ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩)))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N P R γ Good Ok -∗ osFd (L := L) fd dq d -∗
      csOwnF (L := L) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)) -∗
      (∀ base : Loc, ∀ e : w64,
        ((⌜e = 0 ∧ 0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ ∗
            csOwnF (L := L) γ
              (some (d.ino, ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩)) ∗
            ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
         (⌜e ≠ 0 ∧ base = null⌝ ∗ csOwnF (L := L) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)))) -∗
        osFd (L := L) fd dq d -∗ Φ (PairV (#base) (#e))) -∗
      WP (ExternalOp fsExt.name "Mmap"
        (Val (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown HΦ
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_open N P R γ Good Ok _ ⊤ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv
    with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply wp_osMmap fd off len prot fl dq d m hN hrd hoff hlen hprot hfl $$ Hos Hfd Hm
  iintro %base %e Hres Hfd
  icases Hres with (⟨%he, Hm, Hc⟩ | ⟨%he, Hm⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves
      (some (d.ino, ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩) : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some (d.ino, ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩))
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe Hm2
        iapply (show invBytes (L := L) d.ino ⟨m, bs, fa, fb, .idle⟩ ⊢ invBytes (L := L) d.ino
          ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ from .rfl)
        iexact Hb2
      ipureintro; exact ⟨hok base, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
    imodintro
    iapply HΦ $$ %base %e [Hv Hm1 Hb1 Hc] Hfd
    ileft
    isplitr; · ipureintro; exact he
    iframe Hc
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe Hv Hm1
    isplitl
    · iapply (show thrBytes (L := L) d.ino ⟨m, bs, fa, fb, .idle⟩ ⊢ thrBytes (L := L) d.ino
        ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ from .rfl)
      iexact Hb1
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)); iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe
      ipureintro; exact ⟨Hok'.1, rfl, Hok'.2⟩
    imodintro
    iapply HΦ $$ %base %e [Hv Hm1 Hb1] Hfd
    iright
    isplitr; · ipureintro; exact he
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩

/-- `munmap` of a mapping of a file in a crash invariant, idle: the mapping is gone, or (on
failure) maybe not, each of which the caller shows `Ok`. -/
theorem wp_osMunmap_cs (base : Loc) (len cap : w64) (p : Ino) (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop)
    (Ok : CState → Prop) (m : OsMeta) (bs : List ByteG) (fa fb n : Nat) (vf : Nat → val)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hb : m.maps !! base = some n) (hlen : len.toNat = n)
    (hcap : cap.toNat = n)
    (hok : Ok (some (p, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N P R γ Good Ok -∗
      csOwnF (L := L) γ (some (p, ⟨m, bs, fa, fb, .idle⟩)) -∗ cellsR base 0 n vf -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwnF (L := L) γ
            (some (p, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩))) ∨
         (⌜e ≠ 0⌝ ∗
           (csOwnF (L := L) γ (some (p, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)) ∨
            (csOwnF (L := L) γ (some (p, ⟨m, bs, fa, fb, .idle⟩)) ∗ cellsR base 0 n vf)))) -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "Munmap" (Val (PairV (#base) (PairV (#len) (#cap))))) {{ Φ }} := by
  iintro #Hos #Hinv Hown Hc HΦ
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_open N P R γ Good Ok _ ⊤ (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv Hv
    with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply wp_osMunmap base len cap p m n vf hN hb hlen hcap $$ Hos Hm Hc
  iintro %e Hres
  -- the mapping gone
  have hD : ∀ (Q : IProp GF),
      (csOwnF (L := L) γ (some (p, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)) -∗ Q) ⊢
      ghostVar γ (1 : Qp).half (some (p, ⟨m, bs, fa, fb, .idle⟩) : CState) -∗
      ghostVar γ (1 : Qp).half (some (p, ⟨m, bs, fa, fb, .idle⟩) : CState) -∗
      invBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ -∗ thrBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ -∗
      osMeta (L := L) p (DFrac.own 1) ({ m with maps := GMap.delete base m.maps }) -∗
      (▷ (∃ s', ghostVar γ (1 : Qp).half s' ∗ invResS (L := L) s' ∗
        ⌜Ok s' ∧ sIno s' = sIno (some (p, ⟨m, bs, fa, fb, .idle⟩)) ∧ CsCut s'⌝) ={(⊤ : CoPset) \ ↑N, ⊤}=∗ True) -∗
      |={(⊤ : CoPset) \ ↑N, ⊤}=> Q := by
    intro Q
    iintro HQ Hv Hv' Hb2 Hb1 Hm Hclose
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves
      (some (p, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩) : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some (p, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩))
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe Hm2
        iapply (show invBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ ⊢ invBytes (L := L) p
          ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ from .rfl)
        iexact Hb2
      ipureintro; exact ⟨hok, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
    imodintro
    iapply HQ
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe Hv Hm1
    isplitl
    · iapply (show thrBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ ⊢ thrBytes (L := L) p
        ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ from .rfl)
      iexact Hb1
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩
  icases Hres with (⟨%he, Hm⟩ | ⟨%he, (Hm | ⟨Hm, Hc⟩)⟩)
  · iapply (hD _) $$ [HΦ] Hv Hv' Hb2 Hb1 Hm Hclose
    iintro H; iapply HΦ; ileft; iframe; ipureintro; exact he
  · iapply (hD _) $$ [HΦ] Hv Hv' Hb2 Hb1 Hm Hclose
    iintro H; iapply HΦ; iright; isplitr; · ipureintro; exact he
    ileft; iexact H
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some (p, ⟨m, bs, fa, fb, .idle⟩)); iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe
      ipureintro; exact ⟨Hok'.1, rfl, Hok'.2⟩
    imodintro
    iapply HΦ; iright; isplitr; · ipureintro; exact he
    iright; iframe Hc
    iapply (csOwnF_idle _ _ _ rfl).2
    iframe
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩


/-! ### Open -/

/-- The invariant's state and its half of the history, from the caller's: they agree. -/
theorem cs_openT (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (s : CState) (V : Hist) (dq : DFrac) :
    ⊢ csInv (L := L) N P R γ Good Ok -∗ ghostVar γ (1 : Qp).half s -∗
      osTree (L := L) dq R V ={⊤, ⊤ \ ↑N}=∗
      ghostVar γ (1 : Qp).half s ∗ osTree (L := L) dq R V ∗ invResS (L := L) s ∗
        osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ghostVar γ (1 : Qp).half s ∗
        ⌜Ok s ∧ TreeOkI Good P R (sIno s) V ∧ CsCut s⌝ ∗
        (∀ (s' : CState) (V' : Hist), ghostVar γ (1 : Qp).half s' -∗ invResS (L := L) s' -∗
          osTree (L := L) (DFrac.own (1 : Qp).half) R V' -∗ ⌜Ok s' ∧ TreeOkI Good P R (sIno s') V' ∧ CsCut s'⌝
          ={⊤ \ ↑N, ⊤}=∗ True) := by
  iintro #Hinv Hv Ht
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', %V', >Hv', >Hr, >Ht', >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases osTree_agree _ _ _ _ _ _ $$ Ht Ht' with %Heq
  obtain ⟨-, rfl⟩ := Heq
  imodintro
  iframe Hv Ht Hr Ht' Hv'
  isplitr
  · ipureintro; exact Hok'
  iintro %s2 %V2 Hv2 Hr2 Ht2 %Hok2
  iapply Hclose
  inext; iexists s2, V2; iframe; ipureintro; exact Hok2

/-- `open(2)` with `O_RDWR | O_CREAT` of `p = d/b`, no file there, in a crash invariant: the
invariant's half of the history and the caller's (with the call's) make it whole, so the create
can happen; on success the new file (`csNew`), which the caller shows `Ok`; on failure it may have
been created. -/
theorem wp_osOpenCreate_cs (d b : GoString) (N : Namespace) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (V : Hist) (j : Ino) (k s0 : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hb : NameOk b) (hd : lookupH R V d = some (.dir j))
    (hn : lookupH R V (child d b) = none) (hok : ∀ i, Ok (csNew i)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N (child d b) R γ Good Ok -∗
      ghostVar γ (1 : Qp).half (none : CState) -∗
      osTree (L := L) (DFrac.own (1 : Qp).half.half) R V -∗ osCall (L := L) k s0 (1 : Qp).half.half -∗
      (∀ fd : w64, ∀ e : w64,
        ((∃ i, ⌜e = 0 ∧ 0 ≤ fd.toInt⌝ ∗
            csOwn (L := L) (child d b) R γ (csNew i) (V.push ⟨.create j b i, V.2.length⟩) ∗
            osFd (L := L) fd (DFrac.own 1) ⟨i, true, true⟩) ∨
         (⌜e ≠ 0 ∧ fd = -1⌝ ∗ (csOwn (L := L) (child d b) R γ none V ∨ ∃ i,
            csOwn (L := L) (child d b) R γ (csNew i) (V.push ⟨.create j b i, V.2.length⟩)))) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp fsExt.name "Open" (Val (PairV (osTokV k) (PairV (#(child d b)) (#flCreat)))))
        {{ Φ }} := by
  iintro #Hos #Hinv Hv Ht Hk HΦ
  have hnm : newMeta.size = 0 := by simp [initMeta, newFile, OsFile.ofBytes, OsFile.ofDisk]
  have hwf : ∀ i, CsWf (csNew i) := fun i =>
    ⟨by show 0 = newMeta.size; exact hnm.symm, Nat.le_refl _, Nat.zero_le _, trivial⟩
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  imod cs_openT N (child d b) R γ Good Ok _ V _ $$ Hinv Hv Ht
    with ⟨Hv, Ht, -, Hti, Hv', %Hok', Hclose⟩
  ihave Hh := (osTree_split (1 : Qp).half (1 : Qp).half.half R V).2 $$ [Hti Ht]
  · iframe
  imodintro
  iapply wp_osOpenCreate d b R V _ _ k s0 j hb hd hn qp_three hN $$ Hos Hh Hk
  iintro %fd %e %hr Hres
  have hpush : ∀ i, Ok (csNew i) ∧ TreeOkI Good (child d b) R (sIno (csNew i))
      (V.push ⟨.create j b i, V.2.length⟩) ∧ CsCut (csNew i) :=
    fun i => ⟨hok i, treeOk_create (i := i) hr hd hb hn Hok'.2.1 (newMeta, [], none), rfl⟩
  have hpath : ∀ i, SPathOk (child d b) R (csNew i) (V.push ⟨.create j b i, V.2.length⟩) :=
    fun i => EtcdGrove.lookupH_create V.2.length hr hd hb hn
  -- the new file's resources, as the invariant's part and the caller's
  have hnew : ∀ i, osMeta (L := L) i (DFrac.own 1) newMeta ⊢
      invResS (L := L) (csNew i) ∗ thrResS (L := L) (csNew i) := fun i => by
    iintro Hm
    icases (osMeta_halves i newMeta).1 $$ Hm with ⟨Hm1, Hm2⟩
    dsimp only [csNew, invResS, thrResS, metaRes]
    iframe Hm1 Hm2
    unfold invBytes thrBytes
    isplitl <;> iapply (cBytes_nil _ _ _ _).2 <;> iempintro
  icases Hres with (⟨%he, %i, Ht, Hm, Hfd⟩ | ⟨%he, (Ht | ⟨%i, Ht, Hm⟩)⟩)
  · icases (osTree_halves R _).1 $$ Ht with ⟨Ht1, Ht2⟩
    icases hnew i $$ Hm with ⟨Hi, Hth⟩
    imod ghostVar_update_halves (csNew i) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ %_ %_ Hv' Hi Ht1 %(hpush i) with -
    imodintro
    iapply HΦ
    ileft
    iexists i
    iframe Hfd
    isplitr
    · ipureintro; exact he
    unfold csOwn csOwnF
    iframe Hv Hth Ht2
    ipureintro; exact ⟨hwf i, hpath i⟩
  · icases (osTree_halves R _).1 $$ Ht with ⟨Ht1, Ht2⟩
    imod Hclose $$ %none %V Hv' [] Ht1 %Hok' with -
    · dsimp only [invResS]; iempintro
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    ileft
    unfold csOwn csOwnF
    dsimp only [thrResS]
    iframe Hv Ht2
    ipureintro; exact ⟨⟨trivial, trivial⟩, hn⟩
  · icases (osTree_halves R _).1 $$ Ht with ⟨Ht1, Ht2⟩
    icases hnew i $$ Hm with ⟨Hi, Hth⟩
    imod ghostVar_update_halves (csNew i) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ %_ %_ Hv' Hi Ht1 %(hpush i) with -
    imodintro
    iapply HΦ
    iright
    isplitr
    · ipureintro; exact he
    iright
    iexists i
    unfold csOwn csOwnF
    iframe Hv Hth Ht2
    ipureintro; exact ⟨hwf i, hpath i⟩


/-! ### The specs' loops -/

/-- What an `open(O_CREAT)` loop of the file at `d/b` may have made of the state `s` and the
history `V` so far: nothing, or `csOpenSt` of them (a failed attempt may have created the
file). -/
def CsOpenInv (j : Ino) (b : GoString) (V : Hist) (s s' : CState) (V' : Hist) : Prop :=
  (s' = s ∧ V' = V) ∨ ∃ i, (s', V') = csOpenSt j b V i s

/-- With a file at the path, it is idle, and it is what `csOpenSt` makes of `s`. -/
theorem csOpenInv_some {j : Ino} {b : GoString} {V V' : Hist} {s : CState} {i : Ino} {y : CSt}
    (hs : s = none ∨ ∃ i m bs fa fb, s = some (i, ⟨m, bs, fa, fb, .idle⟩))
    (h : CsOpenInv j b V s (some (i, y)) V') :
    (s = none ∨ sIno s = some i) ∧ (some (i, y), V') = csOpenSt j b V i s ∧ y.busy = .idle := by
  rcases h with ⟨h1, h2⟩ | ⟨i1, h⟩
  · subst h1 h2
    rcases hs with h | ⟨i0, m, bs, fa, fb, h⟩
    · cases h
    · cases h; exact ⟨.inr rfl, rfl, rfl⟩
  · cases s with
    | none =>
      simp only [csOpenSt, csNew, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact ⟨.inl rfl, rfl, rfl⟩
    | some x =>
      simp only [csOpenSt, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rcases hs with h | ⟨i0, m, bs, fa, fb, h⟩
      · cases h
      · cases h; exact ⟨.inr rfl, rfl, rfl⟩

theorem csOwnF_wf (γ : GName) (s : CState) : csOwnF (L := L) γ s ⊢ ⌜CsWf s⌝ := by
  unfold csOwnF; iintro ⟨-, -, %h⟩; ipureintro; exact h

/-- The caller's part of no file at `p`. -/
theorem csOwn_none (p : GoString) (R : Roots) (γ : GName) (V : Hist) :
    csOwn (L := L) p R γ none V ⊢ ghostVar γ (1 : Qp).half (none : CState) ∗
      osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗ ⌜lookupH R V p = none⌝ := by
  unfold csOwn csOwnF; dsimp only [thrResS]
  iintro ⟨⟨Hv, -, -⟩, Ht, %h⟩; iframe; ipureintro; exact h

/-- The caller's part of the file `i` at `p`: its half of the history, lent out. -/
theorem csOwn_tree (p : GoString) (R : Roots) (γ : GName) (i : Ino) (x : CSt) (V : Hist) :
    csOwn (L := L) p R γ (some (i, x)) V ⊢ osTree (L := L) (DFrac.own (1 : Qp).half) R V ∗
      ⌜lookupH R V p = some (.file i)⌝ ∗
      (osTree (L := L) (DFrac.own (1 : Qp).half) R V -∗ csOwn (L := L) p R γ (some (i, x)) V) := by
  unfold csOwn
  iintro ⟨Hf, Ht, %h⟩
  iframe Ht
  isplitr
  · ipureintro; exact h
  iintro Ht
  iframe
  ipureintro; exact h

/-! ### Freezing more bytes -/

instance osByte_discard_persistent (p : Ino) (k : Nat) (x : ByteG) :
    Persistent (osByte (L := L) p k DFrac.discard x) := by
  unfold osByte gElem; letI := (gooseOsGS (L := L)).osAllG; infer_instance

theorem osByte_persist (p : Ino) (k : Nat) (dq : DFrac) (x : ByteG) :
    osByte (L := L) p k dq x ⊢ |==> osByte (L := L) p k DFrac.discard x := by
  unfold osByte gElem; letI := (gooseOsGS (L := L)).osAllG
  exact wand_entails (ghostMapElem_persist _ _ dq x)

/-- **Freeze more bytes** of an idle file in a crash invariant (a superset of the frozen ones, at
most all of them), which the caller shows `Ok`: the caller gets their discarded copies. -/
theorem cs_freeze (N : Namespace) (P : GoString) (R : Roots) (p : Ino) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta)
    (bs : List ByteG) (fa fb fa' fb' : Nat) (E : CoPset) (hE : ↑N ⊆ E)
    (hab' : fa' ≤ fb') (hfb' : fb' ≤ m.size) (hsub : fa < fb → fa' ≤ fa ∧ fb ≤ fb')
    (hok : Ok (some (p, ⟨m, bs, fa', fb', .idle⟩))) :
    ⊢ csInv (L := L) N P R γ Good Ok -∗ csOwnF (L := L) γ (some (p, ⟨m, bs, fa, fb, .idle⟩)) ={E}=∗
      csOwnF (L := L) γ (some (p, ⟨m, bs, fa', fb', .idle⟩)) ∗
      osBytes (L := L) p fa' DFrac.discard ((bs.drop fa').take (fb' - fa')) := by
  iintro #Hinv Hown
  icases (csOwnF_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  imod cs_open N P R γ Good Ok _ E hE $$ Hinv Hv with ⟨Hv, Hr, Hv', %Hok', Hclose⟩
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  -- pointwise: the newly frozen bytes, whole, discarded
  have hpt1 : ∀ (k : Nat) (x : ByteG),
      cByte (L := L) p (CSt.frac (⟨m, bs, fa, fb, .idle⟩ : CSt)) (fun k => !CSt.taken (⟨m, bs, fa, fb, .idle⟩ : CSt) k) (0 + k) x ∗
        cByte (L := L) p (fun _ => DFrac.own (1 : Qp).half)
          (fun k => !CSt.taken (⟨m, bs, fa, fb, .idle⟩ : CSt) k && !CSt.frozen (⟨m, bs, fa, fb, .idle⟩ : CSt) k) (0 + k) x ⊢
      |==> (cByte (L := L) p (CSt.frac (⟨m, bs, fa', fb', .idle⟩ : CSt)) (fun k => !CSt.taken (⟨m, bs, fa', fb', .idle⟩ : CSt) k) (0 + k) x ∗
        (cByte (L := L) p (fun _ => DFrac.own (1 : Qp).half)
          (fun k => !CSt.taken (⟨m, bs, fa', fb', .idle⟩ : CSt) k && !CSt.frozen (⟨m, bs, fa', fb', .idle⟩ : CSt) k) (0 + k) x ∗
         cByte (L := L) p (fun _ => DFrac.discard) (fun k => decide (fa' ≤ k ∧ k < fb')) (0 + k) x)) := by
    intro k x
    unfold cByte
    simp only [Nat.zero_add, CSt.taken, Bool.not_false, Bool.true_and]
    by_cases h1 : fa ≤ k ∧ k < fb <;> by_cases h2 : fa' ≤ k ∧ k < fb'
    · rw [CSt.frac_in (⟨m, bs, fa, fb, .idle⟩ : CSt) k h1.1 h1.2, CSt.frac_in (⟨m, bs, fa', fb', .idle⟩ : CSt) k h2.1 h2.2, CSt.frozen_in (⟨m, bs, fa, fb, .idle⟩ : CSt) k h1.1 h1.2,
        CSt.frozen_in (⟨m, bs, fa', fb', .idle⟩ : CSt) k h2.1 h2.2, decide_eq_true h2]
      simp only [Bool.not_true, if_true, Bool.false_eq_true, if_false]
      iintro ⟨#H, -⟩; imodintro; isplitr; · iexact H
      isplitr; · iempintro
      iexact H
    · exfalso; have := hsub (by omega); omega
    · rw [CSt.frac_out (⟨m, bs, fa, fb, .idle⟩ : CSt) k (by dsimp only; omega), CSt.frac_in (⟨m, bs, fa', fb', .idle⟩ : CSt) k h2.1 h2.2,
        CSt.frozen_out (⟨m, bs, fa, fb, .idle⟩ : CSt) k (by dsimp only; omega), CSt.frozen_in (⟨m, bs, fa', fb', .idle⟩ : CSt) k h2.1 h2.2, decide_eq_true h2]
      simp only [Bool.not_true, Bool.not_false, if_true, Bool.false_eq_true, if_false]
      iintro ⟨H1, H2⟩
      ihave H := (osByte_halves (L := L) p k x).2 $$ [H1 H2]
      · iframe
      imod osByte_persist (L := L) p k _ x $$ H with #H
      imodintro; isplitr; · iexact H
      isplitr; · iempintro
      iexact H
    · rw [CSt.frac_out (⟨m, bs, fa, fb, .idle⟩ : CSt) k (by dsimp only; omega), CSt.frac_out (⟨m, bs, fa', fb', .idle⟩ : CSt) k (by dsimp only; omega),
        CSt.frozen_out (⟨m, bs, fa, fb, .idle⟩ : CSt) k (by dsimp only; omega), CSt.frozen_out (⟨m, bs, fa', fb', .idle⟩ : CSt) k (by dsimp only; omega),
        decide_eq_false h2]
      simp only [Bool.not_false, if_true, Bool.false_eq_true, if_false]
      iintro ⟨H1, H2⟩; imodintro; iframe
  have hpt : invBytes (L := L) p (⟨m, bs, fa, fb, .idle⟩ : CSt) ∗ thrBytes (L := L) p (⟨m, bs, fa, fb, .idle⟩ : CSt) ⊢
      |==> (invBytes (L := L) p (⟨m, bs, fa', fb', .idle⟩ : CSt) ∗ thrBytes (L := L) p (⟨m, bs, fa', fb', .idle⟩ : CSt) ∗
        cBytes (L := L) p (fun _ => DFrac.discard) (fun k => decide (fa' ≤ k ∧ k < fb')) 0 bs) := by
    unfold invBytes thrBytes cBytes
    iintro H
    ihave H := BigSepL.bigSepL_sep_eqv.2 $$ H
    ihave H := (BigSepL.bigSepL_mono_of_forall (fun {k x} => hpt1 k x)) $$ H
    imod bigSepL_bupd _ $$ H with H
    imodintro
    icases BigSepL.bigSepL_sep_eqv.1 $$ H with ⟨Hi, H⟩
    icases BigSepL.bigSepL_sep_eqv.1 $$ H with ⟨Ht, Hd⟩
    iframe
  imod hpt $$ [Hb2 Hb1] with ⟨Hb2, Hb1, Hd⟩
  · iframe
  imod ghostVar_update_halves (some (p, ⟨m, bs, fa', fb', .idle⟩) : CState) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hm2 Hb2] with -
  · inext; iexists (some (p, ⟨m, bs, fa', fb', .idle⟩)); iframe Hv'; isplitl
    · iapply (invResS_idle _ _ rfl).2; iframe
    ipureintro; exact ⟨hok, rfl, (by have hc := Hok'.2; simp only [CsCut] at hc ⊢; simp [hc, OsMeta.synced, OsMeta.announce, pwPostK, pwPost, rsPost])⟩
  imodintro
  isplitl [Hv Hm1 Hb1]
  · iapply (csOwnF_idle _ _ _ rfl).2
    iframe; ipureintro; exact ⟨hl, hab', hfb', trivial⟩
  icases (cBytes_split3 (L := L) p _ _ fa' fb' bs hab' (by omega)).1 $$ Hd with ⟨-, Hd, -⟩
  iapply (cBytes_full (L := L) p (fun _ => DFrac.discard) (fun k => decide (fa' ≤ k ∧ k < fb'))
    DFrac.discard fa' ((bs.drop fa').take (fb' - fa')) fun k hk => ⟨by
      simp only [List.length_take, List.length_drop] at hk
      simp only [decide_eq_true_eq]; omega, rfl⟩).1
  iexact Hd

end ops

end Perennial
