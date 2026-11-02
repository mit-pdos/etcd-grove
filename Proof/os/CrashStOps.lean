/-
The extension's operations over a file in the generic crash invariant (`Proof/os/CrashSt.lean`):
each opens the invariant around its one step (`osOp_atomic`), applies the extension-level spec to
the invariant's and the caller's parts put together, and closes it with the new state, of which
the caller shows `Ok`. Lean-first (no Rocq counterpart).

* `wp_osOpen_cs`: absent or idle to `csOpen s` (created, if absent), on failure maybe not.
* `wp_osPWriteStart_cs`/`wp_osPWriteFinish_cs`: idle to a write in flight (missing the frozen
  bytes), and back to idle, as the write of the first `k` bytes left it.
* `wp_osFtruncateStart_cs`/`wp_osFtruncateFinish_cs`: idle to a growing truncate in flight, and
  back to idle, grown or (on failure) with the size bound widened (`ftMeta`).
* `wp_osFsync_cs`: idle to synced: the bytes after the frozen ones (`[fb, size)`), keeping the
  ones before them (`[0, fa)`, shown clean) in the durable bytes known (`OsMeta.syncedKeep`);
  or the ones before them (`hd`). On failure, `ok` is lost.
* `wp_osMmap_cs`/`wp_osMunmap_cs`: the mappings change.
* `cs_freeze`: more bytes frozen (a ghost step), the caller getting their discarded copies.
-/
module

public import Proof.os.CrashSt

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

/-! ## Bytes -/

section bytes
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem list_split3 {α : Type} (l : List α) (a b : Nat) (hab : a ≤ b) :
    l = l.take a ++ ((l.drop a).take (b - a) ++ l.drop b) := by
  have : l.drop b = (l.drop a).drop (b - a) := by rw [List.drop_drop]; congr 1; omega
  rw [this, List.take_append_drop, List.take_append_drop]

/-- Bytes in three segments, `[0, a)`, `[a, b)`, `[b, ...)`. -/
theorem cBytes_split3 (p : GoString) (d : Nat → DFrac) (c : Nat → Bool) (a b : Nat)
    (l : List (w8 × Bool)) (hab : a ≤ b) (hbl : b ≤ l.length) :
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
theorem cBytes_takeRange (p : GoString) (d : Nat → DFrac) (c c' : Nat → Bool) (dq : DFrac)
    (lo hi : Nat) (l : List (w8 × Bool)) (hlh : lo ≤ hi) (hhl : hi ≤ l.length)
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
theorem cBytes_fin (p : GoString) (d d2 : Nat → DFrac) (c c2 : Nat → Bool) (dq : DFrac)
    (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat) (data : List w8) (k : Nat)
    (hl : bs.length = m.size)
    (hA : ∀ j < cfLo m off, c j = c2 j ∧ (c j = true → d j = d2 j))
    (hC : ∀ j, cfHi m off data.length ≤ j → c j = c2 j ∧ (c j = true → d j = d2 j))
    (hR : ∀ j, cfLo m off ≤ j → j < cfHi m off data.length → c j = false)
    (hP : ∀ j, cfLo m off ≤ j →
      j < cfLo m off + (pwBytes m.size off data k (cfRange m bs off data.length)).length →
      c2 j = true ∧ d2 j = dq) :
    cBytes (L := L) p d c 0 bs ∗
      osBytes (L := L) p (cfLo m off) dq (pwBytes m.size off data k (cfRange m bs off data.length)) ⊢
      cBytes (L := L) p d2 c2 0 (finBytes m bs off data k) := by
  have hlh : cfLo m off ≤ cfHi m off data.length := by unfold cfLo cfHi; omega
  have hhs : cfHi m off data.length ≤ bs.length := by unfold cfHi; omega
  have hhi : cfLo m off + (pwBytes m.size off data k (cfRange m bs off data.length)).length =
      cfHi m off data.length ∨ bs.drop (cfHi m off data.length) = [] := by
    rw [pwBytes_length]
    have := pwSize_ge m.size off k
    by_cases hs : off + data.length ≤ m.size
    · left; unfold cfHi cfLo pwSize; split <;> omega
    · right; apply List.drop_eq_nil_of_le; unfold cfHi; omega
  unfold finBytes
  generalize hpw : pwBytes m.size off data k (cfRange m bs off data.length) = pw at hP hhi ⊢
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
theorem idle_invBytes (p : GoString) (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat)
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

theorem idle_thrBytes (p : GoString) (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat)
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
theorem write_invBytes (p : GoString) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb t off : Nat)
    (data : List w8) (hl : bs.length = m.size) (hfb : fb ≤ m.size)
    (hfz : off + data.length ≤ fa ∨ fb ≤ off) :
    invBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ ⊣⊢
      invBytes (L := L) p ⟨m, bs, fa, fb, .write t off data⟩ ∗
      osBytes (L := L) p (cfLo m off) (DFrac.own (1 : Qp).half) (cfRange m bs off data.length) := by
  unfold invBytes
  refine cBytes_takeRange p _ _ _ _ _ _ bs (by unfold cfLo cfHi; omega) (by unfold cfHi; omega)
    (fun k => by simp [CSt.taken]) (fun k h1 h2 =>
      ⟨rfl, CSt.frac_out _ _ (by dsimp only; simp only [cfLo, cfHi] at h1 h2; omega)⟩)

/-- ... and the caller's. -/
theorem write_thrBytes (p : GoString) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb t off : Nat)
    (data : List w8) (hl : bs.length = m.size) (hfb : fb ≤ m.size)
    (hfz : off + data.length ≤ fa ∨ fb ≤ off) :
    thrBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ ⊣⊢
      thrBytes (L := L) p ⟨m, bs, fa, fb, .write t off data⟩ ∗
      osBytes (L := L) p (cfLo m off) (DFrac.own (1 : Qp).half) (cfRange m bs off data.length) := by
  unfold thrBytes
  refine cBytes_takeRange p _ _ _ _ _ _ bs (by unfold cfLo cfHi; omega) (by unfold cfHi; omega)
    (fun k => by simp only [CSt.taken, Bool.not_false, Bool.true_and]; rw [Bool.and_comm]; rfl)
    (fun k h1 h2 =>
      ⟨by rw [CSt.frozen_out _ _ (by dsimp only; simp only [cfLo, cfHi] at h1 h2; omega)]; rfl, rfl⟩)

end bytes

/-! ## The operations -/

/-- The state an open without `O_TRUNC` leaves: the file created, if absent. -/
def csOpen : CState → CState
  | none => some ⟨newMeta, [], 0, 0, .idle⟩
  | s => s

/-- The state after a successful sync of an idle state `H ++ (F ++ T)` (`F` frozen): of `T`,
keeping `H` (shown clean) in the durable bytes known; or (`hd`) of `H`. -/
def csSynced (hd : Bool) (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat) : CSt :=
  match hd with
  | true => ⟨m.synced 0 H, syncedBytes m H ++ (F ++ T), fa, fb, .idle⟩
  | false => ⟨m.syncedKeep fb T 0 H, H ++ (F ++ syncedBytes m T), fa, fb, .idle⟩

section ops
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt] [GoGlobalContext]
  [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

theorem csOwn_idle (p : GoString) (γ : GName) (s : CSt) (hb : s.busy = .idle) :
    csOwn (L := L) p γ (some s) ⊣⊢ ghostVar γ (1 : Qp).half (some s : CState) ∗
      (osMeta (L := L) p (DFrac.own (1 : Qp).half) (some s.m) ∗ thrBytes (L := L) p s) ∗ ⌜s.Wf⌝ := by
  obtain ⟨m, bs, fa, fb, busy⟩ := s
  dsimp only at hb; subst hb; exact .rfl

theorem csOwn_busy (p : GoString) (γ : GName) (s : CSt) (hb : s.busy ≠ .idle) :
    csOwn (L := L) p γ (some s) ⊣⊢ ghostVar γ (1 : Qp).half (some s : CState) ∗
      thrBytes (L := L) p s ∗ ⌜s.Wf⌝ := by
  obtain ⟨m, bs, fa, fb, _ | ⟨t, off, data⟩ | ⟨t, sz⟩⟩ := s
  · exact absurd rfl hb
  all_goals exact sep_congr .rfl (sep_congr emp_sep .rfl)

theorem invResS_idle (p : GoString) (s : CSt) (hb : s.busy = .idle) :
    invResS (L := L) p (some s) ⊣⊢
      osMeta (L := L) p (DFrac.own (1 : Qp).half) (some s.m) ∗ invBytes (L := L) p s := by
  obtain ⟨m, bs, fa, fb, busy⟩ := s
  dsimp only at hb; subst hb; exact .rfl

/-- `pwrite`'s first step on a file in a crash invariant, idle: the write (which misses the
frozen bytes) is in flight, which the caller shows `Ok`. -/
theorem wp_osPWriteStart_cs (fd off : w64) (data : List w8) (dq : DFrac) (d : OsFd)
    (N : Namespace) (γ : GName) (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool))
    (fa fb : Nat) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hfz : off.toNat + data.length ≤ fa ∨ fb ≤ off.toNat)
    (hok : ∀ t, Ok (some ⟨m, bs, fa, fb, .write t off.toNat data⟩)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N d.path γ Ok -∗ osFd (L := L) fd dq d -∗
      csOwn (L := L) d.path γ (some ⟨m, bs, fa, fb, .idle⟩) -∗
      mcellsAny (L := L) m.maps (cfLo m off.toNat) (off.toNat + data.length) -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗
        csOwn (L := L) d.path γ (some ⟨m, bs, fa, fb, .write t off.toNat data⟩) -∗
        Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "PWriteStart" (Val (PairV (#fd) (PairV (#off) (#data))))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown Hc HΦ
  icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (write_invBytes d.path m bs fa fb 0 off.toNat data hl hfb hfz).1 $$ Hb2 with ⟨Hb2, Hr2⟩
  icases (write_thrBytes d.path m bs fa fb 0 off.toNat data hl hfb hfz).1 $$ Hb1 with ⟨Hb1, Hr1⟩
  ihave Hrg := (osBytes_halves _ _ _).2 $$ [Hr1 Hr2]
  · iframe
  ihave Hrg := (show osBytes (L := L) d.path (cfLo m off.toNat) (DFrac.own 1)
      (cfRange m bs off.toNat data.length) ⊢ osBytes (L := L) d.path (min off.toNat m.size)
      (DFrac.own 1) (cfRange m bs off.toNat data.length) from .rfl) $$ Hrg
  imodintro
  ihave Hc := (show mcellsAny (L := L) m.maps (cfLo m off.toNat) (off.toNat + data.length) ⊢
      mcellsAny (L := L) m.maps (min off.toNat m.size) (off.toNat + data.length) from .rfl) $$ Hc
  iapply wp_osPWriteStart fd off data dq d 1 m (cfRange m bs off.toNat data.length) hN hwr hoff
    (by unfold cfRange cfLo cfHi; simp only [List.length_take, List.length_drop]; omega)
    (fun _ => rfl) $$ Hos Hfd Hm Hrg Hc
  iintro %t Hfd Ht
  imod ghostVar_update_halves (some ⟨m, bs, fa, fb, .write t off.toNat data⟩ : CState) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Ht Hb2] with -
  · inext; iexists (some ⟨m, bs, fa, fb, .write t off.toNat data⟩); iframe Hv'; isplitl
    · dsimp only [invResS, metaRes]; isplitl [Ht]
      · iexact Ht
      · iapply (show invBytes (L := L) d.path ⟨m, bs, fa, fb, .write 0 off.toNat data⟩ ⊢
          invBytes (L := L) d.path ⟨m, bs, fa, fb, .write t off.toNat data⟩ from .rfl)
        iexact Hb2
    ipureintro; exact hok t
  imodintro
  iapply HΦ $$ %t Hfd
  iapply (csOwn_busy _ _ _ (by simp)).2
  isplitl [Hv]
  · iexact Hv
  isplitl [Hb1]
  · iapply (show thrBytes (L := L) d.path ⟨m, bs, fa, fb, .write 0 off.toNat data⟩ ⊢
      thrBytes (L := L) d.path ⟨m, bs, fa, fb, .write t off.toNat data⟩ from .rfl)
    iexact Hb1
  ipureintro; exact ⟨hl, hab, hfb, hfz⟩

/-- `pwrite`'s second step on a file in a crash invariant: idle again, as the write of the first
`k` bytes left it, which the caller shows `Ok`. -/
theorem wp_osPWriteFinish_cs (t : Nat) (p : GoString) (off : Nat) (data : List w8)
    (N : Namespace) (γ : GName) (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool))
    (fa fb : Nat) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : ∀ k ≤ data.length,
      Ok (some ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N p γ Ok -∗
      csOwn (L := L) p γ (some ⟨m, bs, fa, fb, .write t off data⟩) -∗
      (∀ k : Nat, ∀ e : w64, ⌜k ≤ data.length ∧ (k = data.length ∧ e = 0 ∨ e ≠ 0)⌝ -∗
        csOwn (L := L) p γ (some ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩) -∗
        mcells (L := L) m.maps (cfLo m off) (off + data.length)
          (pwCell m.size off data k (cfRange m bs off data.length)) -∗
        Φ (PairV (#(W64 k)) (#e))) -∗
      WP (ExternalOp osFsExt.name "PWriteFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hos #Hinv Hown HΦ
  icases (csOwn_busy _ _ _ (by simp)).1 $$ Hown with ⟨Hv, Hb1, %Hwf⟩
  obtain ⟨hl, hab, hfb, hfz⟩ := Hwf
  dsimp only at hl hab hfb hfz
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  dsimp only [invResS, metaRes]
  icases Hr with ⟨Ht, Hb2⟩
  imodintro
  iapply wp_osPWriteFinish t p off data 1 m (cfRange m bs off data.length) hN $$ Hos Ht
  iintro %k %e %hke Hm Hrg Hc
  have hk := hke.1
  icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
  icases (osBytes_halves _ _ _).1 $$ Hrg with ⟨Hr1, Hr2⟩
  have hpl : cfLo m off + (pwBytes m.size off data k (cfRange m bs off data.length)).length ≤
      off + data.length := by
    rw [pwBytes_length]; unfold cfLo; omega
  have hlo : fb ≤ off → fb ≤ cfLo m off := fun h => by unfold cfLo; omega
  have hout : ∀ j, (j < cfLo m off ∨ cfHi m off data.length ≤ j) →
      CSt.taken ⟨m, bs, fa, fb, .write t off data⟩ j = false := fun j hj =>
    CSt.taken_out _ j (fun t' o d' h => by cases h; omega)
  ihave Hb2 := (show invBytes (L := L) p ⟨m, bs, fa, fb, .write t off data⟩ ⊢ cBytes (L := L) p (CSt.frac ⟨m, bs, fa, fb, .write t off data⟩)
      (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data⟩ j) 0 bs from .rfl) $$ Hb2
  ihave Hb2 := cBytes_fin (L := L) p (CSt.frac ⟨m, bs, fa, fb, .write t off data⟩) (CSt.frac ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩)
    (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data⟩ j) (fun j => !CSt.taken ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ j)
    (DFrac.own (1 : Qp).half) m bs off data k hl
    (fun j hj => ⟨by rw [hout j (.inl hj)]; rfl, fun _ => rfl⟩)
    (fun j hj => ⟨by rw [hout j (.inr hj)]; rfl, fun _ => rfl⟩)
    (fun j h1 h2 => by rw [CSt.taken_in _ j t off data rfl h1 h2]; rfl)
    (fun j h1 h2 => ⟨rfl, CSt.frac_out _ _ (by dsimp only; have := hlo; omega)⟩) $$ [Hb2 Hr2]
  · iframe
  ihave Hb2 := (show cBytes (L := L) p (CSt.frac ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩) (fun j => !CSt.taken ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ j) 0
      (finBytes m bs off data k) ⊢ invBytes (L := L) p ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ from .rfl) $$ Hb2
  ihave Hb1 := (show thrBytes (L := L) p ⟨m, bs, fa, fb, .write t off data⟩ ⊢ cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half)
      (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data⟩ j && !CSt.frozen ⟨m, bs, fa, fb, .write t off data⟩ j) 0 bs from .rfl) $$ Hb1
  ihave Hb1 := cBytes_fin (L := L) p (fun _ => DFrac.own (1 : Qp).half) (fun _ => DFrac.own (1 : Qp).half)
    (fun j => !CSt.taken ⟨m, bs, fa, fb, .write t off data⟩ j && !CSt.frozen ⟨m, bs, fa, fb, .write t off data⟩ j)
    (fun j => !CSt.taken ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ j && !CSt.frozen ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ j)
    (DFrac.own (1 : Qp).half) m bs off data k hl
    (fun j hj => ⟨by rw [hout j (.inl hj)]; rfl, fun _ => rfl⟩)
    (fun j hj => ⟨by rw [hout j (.inr hj)]; rfl, fun _ => rfl⟩)
    (fun j h1 h2 => by rw [CSt.taken_in _ j t off data rfl h1 h2]; rfl)
    (fun j h1 h2 => ⟨by rw [CSt.frozen_out _ _ (by dsimp only; have := hlo; omega)]; rfl,
      rfl⟩) $$ [Hb1 Hr1]
  · iframe
  ihave Hb1 := (show cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half)
      (fun j => !CSt.taken ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ j && !CSt.frozen ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ j) 0
      (finBytes m bs off data k) ⊢ thrBytes (L := L) p ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ from .rfl) $$ Hb1
  imod ghostVar_update_halves
    (some ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩ : CState) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hm2 Hb2] with -
  · inext; iexists (some ⟨finMeta m off data k, finBytes m bs off data k, fa, fb, .idle⟩)
    iframe Hv'; isplitl
    · dsimp only; iframe
    ipureintro; exact hok k hk
  imodintro
  ihave Hc := (show mcells (L := L) m.maps (min off m.size) (off + data.length)
      (pwCell m.size off data k (cfRange m bs off data.length)) ⊢ mcells (L := L) m.maps (cfLo m off)
      (off + data.length) (pwCell m.size off data k (cfRange m bs off data.length)) from .rfl) $$ Hc
  iapply HΦ $$ %k %e %hke [Hv Hm1 Hb1] Hc
  iapply (csOwn_idle _ _ _ rfl).2
  iframe
  ipureintro
  refine ⟨finBytes_length hl hk, hab, ?_, trivial⟩
  show fb ≤ pwSize m.size off k
  have := pwSize_ge m.size off k; omega

/-! ### Truncate -/

/-- Grown bytes: the old ones and the new zeros. -/
theorem grow_bytes (p : GoString) (m m' : OsMeta) (bs : List (w8 × Bool)) (fa fb t sz : Nat)
    (hfb : fb ≤ bs.length) :
    osBytes (L := L) p bs.length (DFrac.own 1) (List.replicate (sz - m.size) (0, false)) ∗
      invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ ∗ thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ ⊢
    invBytes (L := L) p ⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ ∗ thrBytes (L := L) p ⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ := by
  iintro ⟨Hz, Hi, Ht⟩
  icases (osBytes_halves (L := L) p _ _).1 $$ Hz with ⟨Hz1, Hz2⟩
  ihave Hi := (show invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ ⊢ cBytes (L := L) p (CSt.frac (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt))
    (fun k => !CSt.taken (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt) k) 0 bs from .rfl) $$ Hi
  ihave Ht := (show thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ ⊢ cBytes (L := L) p (fun _ => DFrac.own (1 : Qp).half)
    (fun k => !CSt.taken (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt) k && !CSt.frozen (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt) k) 0 bs from .rfl) $$ Ht
  ihave Hz1 := (cBytes_full (L := L) p (CSt.frac (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt)) (fun k => !CSt.taken (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt) k) _
    bs.length _ fun k hk => ⟨rfl, CSt.frac_out _ _ (by dsimp only; omega)⟩).2 $$ Hz1
  ihave Hz2 := (cBytes_full (L := L) p (fun _ => DFrac.own (1 : Qp).half)
    (fun k => !CSt.taken (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt) k && !CSt.frozen (⟨m', bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CSt) k) _ bs.length _ fun k hk =>
      ⟨by rw [CSt.frozen_out _ _ (by dsimp only; omega)]; rfl, rfl⟩).2 $$ Hz2
  unfold invBytes thrBytes
  isplitl [Hz1 Hi]
  · iapply (cBytes_append (L := L) p _ _ 0 bs _).2; rw [Nat.zero_add]; iframe
  · iapply (cBytes_append (L := L) p _ _ 0 bs _).2; rw [Nat.zero_add]; iframe

/-- A growing truncate's first step on a file in a crash invariant, idle: the truncate is in
flight, which the caller shows `Ok`. -/
theorem wp_osFtruncateStart_cs (fd sz : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName)
    (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb hi : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt)
    (hgrow : m.size ≤ sz.toNat) (hhi : MapsBelow m.maps hi)
    (hok : ∀ t, Ok (some ⟨m, bs, fa, fb, .trunc t sz.toNat⟩)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N d.path γ Ok -∗ osFd (L := L) fd dq d -∗
      csOwn (L := L) d.path γ (some ⟨m, bs, fa, fb, .idle⟩) -∗ mcellsAny (L := L) m.maps m.size hi -∗
      (∀ t : Nat, osFd (L := L) fd dq d -∗
        csOwn (L := L) d.path γ (some ⟨m, bs, fa, fb, .trunc t sz.toNat⟩) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp osFsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown Hc HΦ
  icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply wp_osFtruncateStart fd sz dq d m hi hN hwr hsz0 hgrow hhi $$ Hos Hfd Hm Hc
  iintro %t Hfd Ht
  imod ghostVar_update_halves (some ⟨m, bs, fa, fb, .trunc t sz.toNat⟩ : CState) γ _ _
    $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Ht Hb2] with -
  · inext; iexists (some ⟨m, bs, fa, fb, .trunc t sz.toNat⟩); iframe Hv'; isplitl
    · dsimp only [invResS, metaRes]; isplitl [Ht]
      · iexact Ht
      · iapply (show invBytes (L := L) d.path ⟨m, bs, fa, fb, .idle⟩ ⊢
          invBytes (L := L) d.path ⟨m, bs, fa, fb, .trunc t sz.toNat⟩ from .rfl)
        iexact Hb2
    ipureintro; exact hok t
  imodintro
  iapply HΦ $$ %t Hfd
  iapply (csOwn_busy _ _ _ (by simp)).2
  isplitl [Hv]
  · iexact Hv
  isplitl [Hb1]
  · iapply (show thrBytes (L := L) d.path ⟨m, bs, fa, fb, .idle⟩ ⊢
      thrBytes (L := L) d.path ⟨m, bs, fa, fb, .trunc t sz.toNat⟩ from .rfl)
    iexact Hb1
  ipureintro; exact ⟨hl, hab, hfb, hgrow⟩

/-- The caller's part after a truncate grew the file: the file, and the mapped cells of the
new bytes (zeros) and past them. -/
def csGrownOwn (p : GoString) (γ : GName) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb sz hi : Nat) :
    IProp GF :=
  iprop(csOwn (L := L) p γ (some ⟨m.grown sz, bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩) ∗
    mcells (L := L) m.maps m.size sz (fun _ => byteCell 0) ∗ mcellsAny (L := L) m.maps sz hi)

/-- A growing truncate's second step on a file in a crash invariant: grown, or, on failure,
maybe not (with the size bound widened), each of which the caller shows `Ok`. -/
theorem wp_osFtruncateFinish_cs (t : Nat) (p : GoString) (sz : Nat) (N : Namespace) (γ : GName)
    (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb hi : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hhi : MapsBelow m.maps hi)
    (hokG : Ok (some ⟨m.grown sz, bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩))
    (hokF : Ok (some ⟨ftMeta m sz, bs, fa, fb, .idle⟩)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N p γ Ok -∗
      csOwn (L := L) p γ (some ⟨m, bs, fa, fb, .trunc t sz⟩) -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csGrownOwn (L := L) p γ m bs fa fb sz hi) ∨
         (⌜e ≠ 0⌝ ∗ (csGrownOwn (L := L) p γ m bs fa fb sz hi ∨
           (csOwn (L := L) p γ (some ⟨ftMeta m sz, bs, fa, fb, .idle⟩) ∗
             mcellsAny (L := L) m.maps m.size hi)))) -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "FtruncateFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hos #Hinv Hown HΦ
  icases (csOwn_busy _ _ _ (by simp)).1 $$ Hown with ⟨Hv, Hb1, %Hwf⟩
  obtain ⟨hl, hab, hfb, hgrow⟩ := Hwf
  dsimp only at hl hab hfb hgrow
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (show invResS (L := L) p (some ⟨m, bs, fa, fb, .trunc t sz⟩) ⊢ ftTok (L := L) t p sz m ∗
    invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ from .rfl) $$ Hr with ⟨Ht, Hb2⟩
  imodintro
  iapply wp_osFtruncateFinish t p sz m hi hN hgrow hhi $$ Hos Ht
  iintro %e Hres
  -- the two outcomes, as states
  have hG : ∀ (Q : IProp GF), (csGrownOwn (L := L) p γ m bs fa fb sz hi -∗ Q) ⊢
      ghostVar γ (1 : Qp).half (some ⟨m, bs, fa, fb, .trunc t sz⟩ : CState) -∗
      ghostVar γ (1 : Qp).half (some ⟨m, bs, fa, fb, .trunc t sz⟩ : CState) -∗
      invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ -∗ thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ -∗
      osGrown (L := L) p m sz hi -∗
      (▷ (∃ s, ghostVar γ (1 : Qp).half s ∗ invResS (L := L) p s ∗ ⌜Ok s⌝) ={(⊤ : CoPset) \ ↑N, ⊤}=∗ True) -∗
      |={(⊤ : CoPset) \ ↑N, ⊤}=> Q := by
    intro Q
    iintro HQ Hv Hv' Hb2 Hb1 Hg Hclose
    unfold osGrown
    icases Hg with ⟨Hm, Hz, Hc1, Hc2⟩
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    ihave Hz := (show osBytes (L := L) p m.size (DFrac.own 1) (List.replicate (sz - m.size) (0, false)) ⊢
      osBytes (L := L) p bs.length (DFrac.own 1) (List.replicate (sz - m.size) (0, false)) by
        rw [hl]) $$ Hz
    icases grow_bytes (L := L) p m (m.grown sz) bs fa fb t sz (by omega) $$ [Hz Hb2 Hb1] with ⟨Hb2, Hb1⟩
    · iframe
    imod ghostVar_update_halves
      (some ⟨m.grown sz, bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩ : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some ⟨m.grown sz, bs ++ List.replicate (sz - m.size) (0, false), fa, fb, .idle⟩)
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe
      ipureintro; exact hokG
    imodintro
    iapply HQ
    unfold csGrownOwn
    iframe Hc1 Hc2
    iapply (csOwn_idle _ _ _ rfl).2
    iframe
    ipureintro
    refine ⟨by simp [OsMeta.grown, hl]; omega, hab, by simp only [OsMeta.grown]; omega, trivial⟩
  icases Hres with (⟨%he, Hg⟩ | ⟨%he, (Hg | ⟨Hm, Hc⟩)⟩)
  · iapply (hG _) $$ [HΦ] Hv Hv' Hb2 Hb1 Hg Hclose
    iintro H; iapply HΦ; ileft; iframe; ipureintro; exact he
  · iapply (hG _) $$ [HΦ] Hv Hv' Hb2 Hb1 Hg Hclose
    iintro H; iapply HΦ; iright; isplitr; · ipureintro; exact he
    ileft; iexact H
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves (some ⟨ftMeta m sz, bs, fa, fb, .idle⟩ : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some ⟨ftMeta m sz, bs, fa, fb, .idle⟩)
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe Hm2
        iapply (show invBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ ⊢
          invBytes (L := L) p ⟨ftMeta m sz, bs, fa, fb, .idle⟩ from .rfl)
        iexact Hb2
      ipureintro; exact hokF
    imodintro
    iapply HΦ; iright; isplitr; · ipureintro; exact he
    iright
    iframe Hc
    iapply (csOwn_idle _ _ _ rfl).2
    iframe Hv Hm1
    isplitl
    · iapply (show thrBytes (L := L) p ⟨m, bs, fa, fb, .trunc t sz⟩ ⊢
        thrBytes (L := L) p ⟨ftMeta m sz, bs, fa, fb, .idle⟩ from .rfl)
      iexact Hb1
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩

/-! ### Sync -/

/-- `fsync`/`fdatasync` of a file in a crash invariant, idle (`H ++ (F ++ T)`, `F` frozen): on
success `csSynced hd`, which the caller shows `Ok`; on failure, its `ok` is lost. -/
theorem wp_osFsync_cs (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (γ : GName)
    (Ok : CState → Prop) (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat)
    (hH : H.length = fa) (hF : fa + F.length = fb) (hd : Bool)
    (hc : hd = false → ∀ y ∈ H, y.2 = true) (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N)
    (hok : Ok (some (csSynced hd m H F T fa fb)))
    (hokF : Ok (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N d.path γ Ok -∗ osFd (L := L) fd dq d -∗
      csOwn (L := L) d.path γ (some ⟨m, H ++ (F ++ T), fa, fb, .idle⟩) -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwn (L := L) d.path γ (some (csSynced hd m H F T fa fb))) ∨
         (⌜e ≠ 0 ∧ e ≠ EINTR⌝ ∗
           csOwn (L := L) d.path γ (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩))) -∗
        osFd (L := L) fd dq d -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Fsync" (Val (#fd))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown HΦ
  icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  icases (idle_invBytes d.path m H F T fa fb hH hF).1 $$ Hb2 with ⟨HH2, HF, HT2⟩
  icases (idle_thrBytes d.path m H F T fa fb hH hF).1 $$ Hb1 with ⟨HH1, HT1⟩
  ihave HH := (osBytes_halves _ _ _).2 $$ [HH1 HH2]
  · iframe
  ihave HT := (osBytes_halves _ _ _).2 $$ [HT1 HT2]
  · iframe
  -- the bytes back, as a state
  have hback : ∀ (m' : OsMeta) (H' T' : List (w8 × Bool)), H'.length = fa →
      osMeta (L := L) d.path (DFrac.own 1) (some m') ∗ osBytes (L := L) d.path 0 (DFrac.own 1) H' ∗
        osBytes (L := L) d.path fa DFrac.discard F ∗ osBytes (L := L) d.path fb (DFrac.own 1) T' ⊢
      (osMeta (L := L) d.path (DFrac.own (1 : Qp).half) (some m') ∗
        invBytes (L := L) d.path ⟨m', H' ++ (F ++ T'), fa, fb, .idle⟩) ∗
      (osMeta (L := L) d.path (DFrac.own (1 : Qp).half) (some m') ∗
        thrBytes (L := L) d.path ⟨m', H' ++ (F ++ T'), fa, fb, .idle⟩) := by
    intro m' H' T' hH'
    iintro ⟨Hm, HH, HF, HT⟩
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    icases (osBytes_halves _ _ _).1 $$ HH with ⟨HH1, HH2⟩
    icases (osBytes_halves _ _ _).1 $$ HT with ⟨HT1, HT2⟩
    iframe Hm1 Hm2
    isplitl [HH1 HF HT1]
    · iapply (idle_invBytes d.path m' H' F T' fa fb hH' (by omega)).2; iframe
    · iapply (idle_thrBytes d.path m' H' F T' fa fb hH' (by omega)).2; iframe
  imodintro
  cases hd
  · iapply wp_osFsync_keep fd dq d m fb T 0 (DFrac.own 1) H (hc rfl) hN $$ Hos Hfd Hm HT HH
    iintro %e Hres HH Hfd
    icases Hres with (⟨%he, Hm, HT⟩ | ⟨%he, Hm, HT⟩)
    · icases hback _ H (syncedBytes m T) hH $$ [Hm HH HF HT] with ⟨Hi, Ht⟩
      · iframe
      imod ghostVar_update_halves (some ⟨m.syncedKeep fb T 0 H, H ++ (F ++ syncedBytes m T), fa, fb, .idle⟩ : CState) γ _ _
        $$ Hv Hv' with ⟨Hv, Hv'⟩
      imod Hclose $$ [Hv' Hi] with -
      · inext; iexists (some ⟨m.syncedKeep fb T 0 H, H ++ (F ++ syncedBytes m T), fa, fb, .idle⟩); iframe Hv'; isplitl
        · iapply (invResS_idle _ _ rfl).2; iexact Hi
        ipureintro; exact hok
      imodintro
      iapply HΦ $$ %e [Hv Ht] Hfd
      ileft; isplitr; · ipureintro; exact he
      iapply (show csOwn (L := L) d.path γ (some ⟨m.syncedKeep fb T 0 H, H ++ (F ++ syncedBytes m T), fa, fb, .idle⟩) ⊢
        csOwn (L := L) d.path γ (some (csSynced false m H F T fa fb)) from .rfl)
      iapply (csOwn_idle _ _ _ rfl).2
      iframe
      ipureintro
      refine ⟨?_, hab, ?_, trivial⟩ <;>
        simp only [csSynced, OsMeta.syncedKeep, OsMeta.synced, List.length_append, syncedBytes_length] at hl ⊢
      · exact hl
      · omega
    · icases hback { m with ok := false } H T hH $$ [Hm HH HF HT] with ⟨Hi, Ht⟩
      · iframe
      imod ghostVar_update_halves (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩ : CState)
        γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
      imod Hclose $$ [Hv' Hi] with -
      · inext; iexists (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩); iframe Hv'
        isplitl
        · iapply (invResS_idle _ _ rfl).2; iexact Hi
        ipureintro; exact hokF
      imodintro
      iapply HΦ $$ %e [Hv Ht] Hfd
      iright; isplitr; · ipureintro; exact he
      iapply (csOwn_idle _ _ _ rfl).2
      iframe
      ipureintro; exact ⟨hl, hab, hfb, trivial⟩
  · iapply wp_osFsync fd dq d m 0 H hN $$ Hos Hfd Hm HH
    iintro %e Hres Hfd
    icases Hres with (⟨%he, Hm, HH⟩ | ⟨%he, Hm, HH⟩)
    · icases hback _ (syncedBytes m H) T (by rw [syncedBytes_length]; exact hH) $$ [Hm HH HF HT]
        with ⟨Hi, Ht⟩
      · iframe
      imod ghostVar_update_halves (some ⟨m.synced 0 H, syncedBytes m H ++ (F ++ T), fa, fb, .idle⟩ : CState) γ _ _
        $$ Hv Hv' with ⟨Hv, Hv'⟩
      imod Hclose $$ [Hv' Hi] with -
      · inext; iexists (some ⟨m.synced 0 H, syncedBytes m H ++ (F ++ T), fa, fb, .idle⟩); iframe Hv'; isplitl
        · iapply (invResS_idle _ _ rfl).2; iexact Hi
        ipureintro; exact hok
      imodintro
      iapply HΦ $$ %e [Hv Ht] Hfd
      ileft; isplitr; · ipureintro; exact he
      iapply (show csOwn (L := L) d.path γ (some ⟨m.synced 0 H, syncedBytes m H ++ (F ++ T), fa, fb, .idle⟩) ⊢
        csOwn (L := L) d.path γ (some (csSynced true m H F T fa fb)) from .rfl)
      iapply (csOwn_idle _ _ _ rfl).2
      iframe
      ipureintro
      refine ⟨?_, hab, ?_, trivial⟩ <;>
        simp only [csSynced, OsMeta.synced, List.length_append, syncedBytes_length] at hl ⊢
      · exact hl
      · omega
    · icases hback { m with ok := false } H T hH $$ [Hm HH HF HT] with ⟨Hi, Ht⟩
      · iframe
      imod ghostVar_update_halves (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩ : CState)
        γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
      imod Hclose $$ [Hv' Hi] with -
      · inext; iexists (some ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩); iframe Hv'
        isplitl
        · iapply (invResS_idle _ _ rfl).2; iexact Hi
        ipureintro; exact hokF
      imodintro
      iapply HΦ $$ %e [Hv Ht] Hfd
      iright; isplitr; · ipureintro; exact he
      iapply (csOwn_idle _ _ _ rfl).2
      iframe
      ipureintro; exact ⟨hl, hab, hfb, trivial⟩

/-! ### Mappings -/

/-- `mmap` of a file in a crash invariant, idle: on success, a new mapping (`Ok` shown by the
caller for any base), the file's bytes otherwise unchanged. -/
theorem wp_osMmap_cs (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace)
    (γ : GName) (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb : Nat)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hrd : d.readable = true) (hoff : off = 0)
    (hlen : 0 < len.toInt) (hprot : prot.toNat = PROT_READ)
    (hfl : fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE)
    (hok : ∀ base : Loc, Ok (some ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N d.path γ Ok -∗ osFd (L := L) fd dq d -∗
      csOwn (L := L) d.path γ (some ⟨m, bs, fa, fb, .idle⟩) -∗
      (∀ base : Loc, ∀ e : w64,
        ((⌜e = 0 ∧ 0 < base.addr ∧ base.addr + len.toNat ≤ maxAddr⌝ ∗
            csOwn (L := L) d.path γ
              (some ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩) ∗
            ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
              cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
         (⌜e ≠ 0 ∧ base = null⌝ ∗ csOwn (L := L) d.path γ (some ⟨m, bs, fa, fb, .idle⟩))) -∗
        osFd (L := L) fd dq d -∗ Φ (PairV (#base) (#e))) -∗
      WP (ExternalOp osFsExt.name "Mmap"
        (Val (PairV (#fd) (PairV (#off) (PairV (#len) (PairV (#prot) (#fl))))))) {{ Φ }} := by
  iintro #Hos #Hinv Hfd Hown HΦ
  icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply wp_osMmap fd off len prot fl dq d m hN hrd hoff hlen hprot hfl $$ Hos Hfd Hm
  iintro %base %e Hres Hfd
  icases Hres with (⟨%he, Hm, Hc⟩ | ⟨%he, Hm⟩)
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves
      (some ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩)
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe Hm2
        iapply (show invBytes (L := L) d.path ⟨m, bs, fa, fb, .idle⟩ ⊢ invBytes (L := L) d.path
          ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ from .rfl)
        iexact Hb2
      ipureintro; exact hok base
    imodintro
    iapply HΦ $$ %base %e [Hv Hm1 Hb1 Hc] Hfd
    ileft
    isplitr; · ipureintro; exact he
    iframe Hc
    iapply (csOwn_idle _ _ _ rfl).2
    iframe Hv Hm1
    isplitl
    · iapply (show thrBytes (L := L) d.path ⟨m, bs, fa, fb, .idle⟩ ⊢ thrBytes (L := L) d.path
        ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩ from .rfl)
      iexact Hb1
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩
  · icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some ⟨m, bs, fa, fb, .idle⟩); iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe
      ipureintro; exact Hok'
    imodintro
    iapply HΦ $$ %base %e [Hv Hm1 Hb1] Hfd
    iright
    isplitr; · ipureintro; exact he
    iapply (csOwn_idle _ _ _ rfl).2
    iframe
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩

/-- `munmap` of a mapping of a file in a crash invariant, idle: the mapping is gone, or (on
failure) maybe not, each of which the caller shows `Ok`. -/
theorem wp_osMunmap_cs (base : Loc) (len cap : w64) (p : GoString) (N : Namespace) (γ : GName)
    (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb n : Nat) (vf : Nat → val)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hb : m.maps !! base = some n) (hlen : len.toNat = n)
    (hcap : cap.toNat = n)
    (hok : Ok (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩))
    (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N p γ Ok -∗
      csOwn (L := L) p γ (some ⟨m, bs, fa, fb, .idle⟩) -∗ cellsR base 0 n vf -∗
      (∀ e : w64,
        ((⌜e = 0⌝ ∗ csOwn (L := L) p γ
            (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)) ∨
         (⌜e ≠ 0⌝ ∗
           (csOwn (L := L) p γ (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩) ∨
            (csOwn (L := L) p γ (some ⟨m, bs, fa, fb, .idle⟩) ∗ cellsR base 0 n vf)))) -∗ Φ (#e)) -∗
      WP (ExternalOp osFsExt.name "Munmap" (Val (PairV (#base) (PairV (#len) (#cap))))) {{ Φ }} := by
  iintro #Hos #Hinv Hown Hc HΦ
  icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
  unfold csInv
  imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
    with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hm2]
  · iframe
  imodintro
  iapply wp_osMunmap base len cap p m n vf hN hb hlen hcap $$ Hos Hm Hc
  iintro %e Hres
  -- the mapping gone
  have hD : ∀ (Q : IProp GF),
      (csOwn (L := L) p γ (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩) -∗ Q) ⊢
      ghostVar γ (1 : Qp).half (some ⟨m, bs, fa, fb, .idle⟩ : CState) -∗
      ghostVar γ (1 : Qp).half (some ⟨m, bs, fa, fb, .idle⟩ : CState) -∗
      invBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ -∗ thrBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ -∗
      osMeta (L := L) p (DFrac.own 1) (some { m with maps := GMap.delete base m.maps }) -∗
      (▷ (∃ s, ghostVar γ (1 : Qp).half s ∗ invResS (L := L) p s ∗ ⌜Ok s⌝) ={(⊤ : CoPset) \ ↑N, ⊤}=∗ True) -∗
      |={(⊤ : CoPset) \ ↑N, ⊤}=> Q := by
    intro Q
    iintro HQ Hv Hv' Hb2 Hb1 Hm Hclose
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    imod ghostVar_update_halves
      (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ : CState) γ _ _
      $$ Hv Hv' with ⟨Hv, Hv'⟩
    imod Hclose $$ [Hv' Hm2 Hb2] with -
    · inext; iexists (some ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)
      iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe Hm2
        iapply (show invBytes (L := L) p ⟨m, bs, fa, fb, .idle⟩ ⊢ invBytes (L := L) p
          ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩ from .rfl)
        iexact Hb2
      ipureintro; exact hok
    imodintro
    iapply HQ
    iapply (csOwn_idle _ _ _ rfl).2
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
    · inext; iexists (some ⟨m, bs, fa, fb, .idle⟩); iframe Hv'; isplitl
      · iapply (invResS_idle _ _ rfl).2; iframe
      ipureintro; exact Hok'
    imodintro
    iapply HΦ; iright; isplitr; · ipureintro; exact he
    iright; iframe Hc
    iapply (csOwn_idle _ _ _ rfl).2
    iframe
    ipureintro; exact ⟨hl, hab, hfb, trivial⟩

/-! ### Open -/

/-- `open(p, fl)` (with `O_CREAT`, without `O_TRUNC`) of a file in a crash invariant, absent or
idle: on success `csOpen s` (created if absent, which the caller shows `Ok`); on failure maybe. -/
theorem wp_osOpen_cs (p : GoString) (fl : w64) (N : Namespace) (γ : GName) (Ok : CState → Prop)
    (s : CState) (hs : s = none ∨ ∃ m bs fa fb, s = some ⟨m, bs, fa, fb, .idle⟩)
    (hN : ↑osN ⊆ (⊤ : CoPset) \ ↑N) (hfl : OpenFlagsOk fl.toNat) (htr : fl.toNat / O_TRUNC % 2 = 0)
    (hcr : fl.toNat / O_CREAT % 2 = 1) (hok : Ok (csOpen s)) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ csInv (L := L) N p γ Ok -∗ csOwn (L := L) p γ s -∗
      (∀ fd : w64, ∀ e : w64, ∀ s' : CState,
        ⌜(e = 0 ∧ 0 ≤ fd.toInt ∧ s' = csOpen s) ∨ (e ≠ 0 ∧ fd = -1 ∧ (s' = s ∨ s' = csOpen s))⌝ -∗
        csOwn (L := L) p γ s' -∗
        (if e = 0 then osFd (L := L) fd (DFrac.own 1) (openFd p fl) else emp) -∗
        Φ (PairV (#fd) (#e))) -∗
      WP (ExternalOp osFsExt.name "Open" (Val (PairV (#p) (#fl)))) {{ Φ }} := by
  have hcr' : decide (fl.toNat / O_CREAT % 2 = 1) = true := decide_eq_true hcr
  rcases hs with rfl | ⟨m, bs, fa, fb, rfl⟩
  · iintro #Hos #Hinv Hown HΦ
    icases (show csOwn (L := L) p γ none ⊢ ghostVar γ (1 : Qp).half (none : CState) ∗
      osMeta (L := L) p (DFrac.own (1 : Qp).half) none ∗ ⌜True⌝ from .rfl) $$ Hown with ⟨Hv, Hm1, -⟩
    iapply (wp_atomic (E2 := (⊤ : CoPset) \ ↑N))
    unfold csInv
    imod inv_acc (E := ⊤) (show ↑N ⊆ (⊤ : CoPset) from CoPset.subseteq_top) $$ Hinv
      with ⟨Hi, Hclose⟩
    icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
    icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
    subst Heq
    ihave Hr := (show invResS (L := L) p none ⊢ osMeta (L := L) p (DFrac.own (1 : Qp).half) none
      from .rfl) $$ Hr
    ihave Hm := (osMeta_halves _ _).2 $$ [Hm1 Hr]
    · iframe
    imodintro
    iapply wp_osOpen p fl (DFrac.own 1) none hN hfl htr (fun _ => rfl) $$ Hos Hm
    iintro %fd %e %mo' %hres Hm Hfd
    rw [hcr'] at hres
    have hmo : mo' = none ∨ mo' = some newMeta := by
      rcases hres with ⟨-, -, h, -⟩ | ⟨-, -, h | h⟩
      · exact .inr h
      · exact .inl h
      · exact .inr h
    icases (osMeta_halves _ _).1 $$ Hm with ⟨Hm1, Hm2⟩
    rcases hmo with rfl | rfl
    · imod Hclose $$ [Hv' Hm2] with -
      · inext; iexists none; iframe Hv'; isplitl
        · iapply (show osMeta (L := L) p (DFrac.own (1 : Qp).half) none ⊢ invResS (L := L) p none
            from .rfl); iexact Hm2
        ipureintro; exact Hok'
      imodintro
      iapply HΦ $$ %fd %e %none [] [Hv Hm1] Hfd
      · ipureintro
        rcases hres with ⟨-, -, h, -⟩ | ⟨he, hfd, -⟩
        · cases h
        · exact .inr ⟨he, hfd, .inl rfl⟩
      iapply (show ghostVar γ (1 : Qp).half (none : CState) ∗
        osMeta (L := L) p (DFrac.own (1 : Qp).half) none ∗ ⌜True⌝ ⊢ csOwn (L := L) p γ none from .rfl)
      iframe
    · imod ghostVar_update_halves (some ⟨newMeta, [], 0, 0, .idle⟩ : CState) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
      imod Hclose $$ [Hv' Hm2] with -
      · inext; iexists (some ⟨newMeta, [], 0, 0, .idle⟩ : CState); iframe Hv'; isplitl
        · iapply (invResS_idle _ _ rfl).2; iframe Hm2
          iapply (show emp ⊢ invBytes (L := L) p ⟨newMeta, [], 0, 0, .idle⟩ from .rfl); iempintro
        ipureintro; exact hok
      imodintro
      iapply HΦ $$ %fd %e %(csOpen none) [] [Hv Hm1] Hfd
      · ipureintro
        rcases hres with ⟨he, hfd, -, -⟩ | ⟨he, hfd, -⟩
        · exact .inl ⟨he, hfd, rfl⟩
        · exact .inr ⟨he, hfd, .inr rfl⟩
      iapply (show csOwn (L := L) p γ (some ⟨newMeta, [], 0, 0, .idle⟩ : CState) ⊢ csOwn (L := L) p γ (csOpen none) from .rfl)
      iapply (csOwn_idle _ _ _ rfl).2
      iframe Hv Hm1
      isplitl
      · iapply (show emp ⊢ thrBytes (L := L) p ⟨newMeta, [], 0, 0, .idle⟩ from .rfl); iempintro
      ipureintro; exact ⟨rfl, Nat.le_refl _, Nat.le_refl _, trivial⟩
  · iintro #Hos #Hinv Hown HΦ
    icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
    iapply wp_osOpen p fl _ (some m) CoPset.subseteq_top hfl htr (fun h => by cases h) $$ Hos Hm1
    iintro %fd %e %mo' %hres Hm Hfd
    have hmo : mo' = some m := by
      rcases hres with ⟨-, -, h, -⟩ | ⟨-, -, h | h⟩ <;> rw [h] <;> rfl
    subst hmo
    iapply HΦ $$ %fd %e %(some ⟨m, bs, fa, fb, .idle⟩) [] [Hv Hm Hb1] Hfd
    · ipureintro
      rcases hres with ⟨he, hfd, -⟩ | ⟨he, hfd, -⟩
      · exact .inl ⟨he, hfd, rfl⟩
      · exact .inr ⟨he, hfd, .inl rfl⟩
    iapply (csOwn_idle _ _ _ rfl).2
    iframe; ipureintro; exact Hwf

/-! ### Freezing more bytes -/

instance osByte_discard_persistent (p : GoString) (k : Nat) (x : w8 × Bool) :
    Persistent (osByte (L := L) p k DFrac.discard x) := by
  unfold osByte gElem; letI := (gooseOsGS (L := L)).osAllG; infer_instance

theorem osByte_persist (p : GoString) (k : Nat) (dq : DFrac) (x : w8 × Bool) :
    osByte (L := L) p k dq x ⊢ |==> osByte (L := L) p k DFrac.discard x := by
  unfold osByte gElem; letI := (gooseOsGS (L := L)).osAllG
  exact wand_entails (ghostMapElem_persist _ _ dq x)

/-- **Freeze more bytes** of an idle file in a crash invariant (a superset of the frozen ones, at
most all of them), which the caller shows `Ok`: the caller gets their discarded copies. -/
theorem cs_freeze (N : Namespace) (p : GoString) (γ : GName) (Ok : CState → Prop) (m : OsMeta)
    (bs : List (w8 × Bool)) (fa fb fa' fb' : Nat) (E : CoPset) (hE : ↑N ⊆ E)
    (hab' : fa' ≤ fb') (hfb' : fb' ≤ m.size) (hsub : fa < fb → fa' ≤ fa ∧ fb ≤ fb')
    (hok : Ok (some ⟨m, bs, fa', fb', .idle⟩)) :
    ⊢ csInv (L := L) N p γ Ok -∗ csOwn (L := L) p γ (some ⟨m, bs, fa, fb, .idle⟩) ={E}=∗
      csOwn (L := L) p γ (some ⟨m, bs, fa', fb', .idle⟩) ∗
      osBytes (L := L) p fa' DFrac.discard ((bs.drop fa').take (fb' - fa')) := by
  iintro #Hinv Hown
  icases (csOwn_idle _ _ _ rfl).1 $$ Hown with ⟨Hv, ⟨Hm1, Hb1⟩, %Hwf⟩
  obtain ⟨hl, hab, hfb, -⟩ := Hwf
  dsimp only at hl hab hfb
  unfold csInv
  imod inv_acc (E := E) hE $$ Hinv with ⟨Hi, Hclose⟩
  icases Hi with ⟨%s', >Hv', >Hr, >%Hok'⟩
  icases ghostVar_agree _ _ _ _ _ $$ Hv Hv' with %Heq
  subst Heq
  icases (invResS_idle _ _ rfl).1 $$ Hr with ⟨Hm2, Hb2⟩
  -- pointwise: the newly frozen bytes, whole, discarded
  have hpt1 : ∀ (k : Nat) (x : w8 × Bool),
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
  imod ghostVar_update_halves (some ⟨m, bs, fa', fb', .idle⟩ : CState) γ _ _ $$ Hv Hv' with ⟨Hv, Hv'⟩
  imod Hclose $$ [Hv' Hm2 Hb2] with -
  · inext; iexists (some ⟨m, bs, fa', fb', .idle⟩); iframe Hv'; isplitl
    · iapply (invResS_idle _ _ rfl).2; iframe
    ipureintro; exact hok
  imodintro
  isplitl [Hv Hm1 Hb1]
  · iapply (csOwn_idle _ _ _ rfl).2
    iframe; ipureintro; exact ⟨hl, hab', hfb', trivial⟩
  icases (cBytes_split3 (L := L) p _ _ fa' fb' bs hab' (by omega)).1 $$ Hd with ⟨-, Hd, -⟩
  iapply (cBytes_full (L := L) p (fun _ => DFrac.discard) (fun k => decide (fa' ≤ k ∧ k < fb'))
    DFrac.discard fa' ((bs.drop fa').take (fb' - fa')) fun k hk => ⟨by
      simp only [List.length_take, List.length_drop] at hk
      simp only [decide_eq_true_eq]; omega, rfl⟩).1
  iexact Hd

end ops

end Perennial
