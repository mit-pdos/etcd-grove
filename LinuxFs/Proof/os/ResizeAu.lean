/-
The resizes' steps (`ftruncate`, `fallocate`'s growth: `GooseLang/Ext/Fs/Truncate.lean`,
`Falloc.lean`) on a file whose resources are **split between the caller and an atomic update**
(`osAUnc`, `Proof/os/SharedAu.lean`; I3b of `notes/wal-fsext-plan.md`), as the WAL's tail is between
its handle and `walInv`. Lean-first (no Rocq counterpart). Untrusted.

The pattern is the writes' (`pwTok`, W6's `wp_tailPWriteStart`/`Finish`): the change's token lives in
the update's owner (an invariant) while the change is in flight, so that a crash in between finds
it there (`crashRestAt_take_tok`).

* **The first step** (`wp_osFtruncateStart_au`, `wp_osFallocStart_au`): the caller holds half of the
  file's `OsMeta` (and of the bytes the resize cuts off); the update lends the other half (`α`) at
  the step and commits with the change's token (`rsTok`, outcome `(t, n)`), its `Q (t, n)` the
  caller's.
* **The second step** (`wp_osFtruncateFinish_au`, `wp_osFallocFinish_au`): the update lends the token
  and commits with what the step leaves (`rsOutT`/`rsOutF`, whole: the size landed, `rsDoneK`, with the
  new bytes, zeros, and, for a file with no sync cut, the candidates of the bytes announced past the
  new size in its `OsMeta`'s `tc`; or, on failure, maybe not, `rsUndone`), its `Q e` the caller's
  (typically its halves back: the update's owner splits them).

The files are unmapped (`m.maps = ∅`: no cells to lend). The whole-resource specs
(`wp_osFtruncateStart`, ...) are the special case where the update lends nothing the caller lacks;
these are proved from them (`wp_aunc_step`).
-/
module

public import LinuxFs.Proof.os.SharedAu
public import GooseLang.Ext.Fs.Falloc
public import GooseLang.Ext.Fs.Zeros

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

/-! ## `OsMeta`s up to the candidates known past the size -/

/-- `m` knowing the candidates `tc` past the size and the resize stamps `rz`. A resize's outcome
knows, for a file with no sync cut, the candidates of the bytes it announced past the new size and its
own stamp (`rsPostK`); a client that does not need them holds its half of the `OsMeta` up to them
(`os.ftDoneH`, `fallocDoneH`). -/
def OsMeta.withTc (m : OsMeta) (tc : GMap Nat Cands) (rz : List Nat) : OsMeta := { m with tc := tc, rz := rz }

section withTc
variable (m : OsMeta) (tc : GMap Nat Cands) (rz : List Nat)
@[simp] theorem OsMeta.withTc_size : (m.withTc tc rz).size = m.size := rfl
@[simp] theorem OsMeta.withTc_lo : (m.withTc tc rz).lo = m.lo := rfl
@[simp] theorem OsMeta.withTc_hi : (m.withTc tc rz).hi = m.hi := rfl
@[simp] theorem OsMeta.withTc_maps : (m.withTc tc rz).maps = m.maps := rfl
@[simp] theorem OsMeta.withTc_zf : (m.withTc tc rz).zf = m.zf := rfl
@[simp] theorem OsMeta.withTc_cut : (m.withTc tc rz).cut = m.cut := rfl
@[simp] theorem OsMeta.withTc_cz : (m.withTc tc rz).cz = m.cz := rfl
@[simp] theorem OsMeta.withTc_dlo : (m.withTc tc rz).dlo = m.dlo := rfl
@[simp] theorem OsMeta.withTc_dhi : (m.withTc tc rz).dhi = m.dhi := rfl
@[simp] theorem OsMeta.withTc_tc : (m.withTc tc rz).tc = tc := rfl
@[simp] theorem OsMeta.withTc_rz : (m.withTc tc rz).rz = rz := rfl
end withTc

theorem OsMeta.withTc_self (m : OsMeta) : m.withTc m.tc m.rz = m := rfl

@[simp] theorem OsMeta.withTc_withTc (m : OsMeta) (t u : GMap Nat Cands) (r s : List Nat) :
    (m.withTc t r).withTc u s = m.withTc u s := rfl

theorem rsPostK_withTc (keep tr : Bool) (m : OsMeta) (tg sz' n : Nat) (xs : List ByteG) :
    rsPostK keep tr m tg sz' n xs =
      (rsPost tr m tg sz').withTc (rsPostK keep tr m tg sz' n xs).tc (rsPostK keep tr m tg sz' n xs).rz :=
  rfl

theorem touch_withTc (m : OsMeta) (t : GMap Nat Cands) (r : List Nat) (lo hi : Nat) :
    (m.withTc t r).touch lo hi = (m.touch lo hi).withTc t r := by
  unfold OsMeta.touch
  by_cases h1 : hi ≤ lo
  · rw [if_pos h1, if_pos h1]
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : m.dhi ≤ m.dlo
    · rw [if_pos (show (m.withTc t r).dhi ≤ (m.withTc t r).dlo from h2), if_pos h2]; rfl
    · rw [if_neg (show ¬ (m.withTc t r).dhi ≤ (m.withTc t r).dlo from h2), if_neg h2]; rfl

theorem announce_withTc (m : OsMeta) (t : GMap Nat Cands) (r : List Nat) (lo hi tg : Nat)
    (u : GMap Nat Cands) (s : List Nat) :
    ((m.withTc t r).announce lo hi tg).withTc u s = (m.announce lo hi tg).withTc u s := by
  unfold OsMeta.announce
  rw [touch_withTc]; rfl

/-- A resize's outcome depends on the candidates and stamps `m` knows only through its own. -/
theorem rsPost_withTc (tr : Bool) (m : OsMeta) (t : GMap Nat Cands) (r : List Nat) (tg sz' : Nat)
    (u : GMap Nat Cands) (s : List Nat) :
    (rsPost tr (m.withTc t r) tg sz').withTc u s = (rsPost tr m tg sz').withTc u s := by
  unfold rsPost OsMeta.announce
  rw [touch_withTc]; rfl

@[simp] theorem synced_withTc (m : OsMeta) (t : GMap Nat Cands) (r : List Nat) :
    (m.withTc t r).synced = m.synced := rfl

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- An unmapped file has no cells to lend. -/
theorem mcellsAny_nomaps (lo hi : Nat) : ⊢ mcellsAny (GF := GF) (∅ : GMap Loc Nat) lo hi := by
  unfold mcellsAny; exact BigSepM.bigSepM_empty.2

/-- What `ftruncate`'s second step leaves: on success the size landed; on failure it did or not. -/
def rsOutT (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG) (n : Nat) (e : w64) : IProp GF :=
  iprop((⌜e = 0⌝ ∗ rsDoneK (L := L) m.cut.isNone true p tg tg m xs n) ∨
    (⌜e ≠ 0⌝ ∗ (rsDoneK (L := L) m.cut.isNone true p tg tg m xs n ∨
      rsUndone (L := L) true p tg m xs n)))

/-- What `fallocate`'s second step leaves: on success the growth landed; on failure none of it, or a
prefix (the size `w` between). -/
def rsOutF (p : Ino) (tg : Nat) (m : OsMeta) (n : Nat) (e : w64) : IProp GF :=
  iprop((⌜e = 0⌝ ∗ rsDoneK (L := L) m.cut.isNone false p tg tg m [] n) ∨
    (⌜e ≠ 0⌝ ∗ (rsUndone (L := L) false p tg m [] n ∨
      ∃ w, ⌜m.size ≤ w ∧ w ≤ tg⌝ ∗ rsDoneK (L := L) m.cut.isNone false p tg w m [] n)))

/-- **`ftruncate`'s first step, split**: the caller's halves of the `OsMeta` and of the bytes cut
off, the update's halves lent at the step; the update commits with the token. -/
theorem wp_osFtruncateStart_au (fd sz : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt) (hmaps : m.maps = ∅)
    (hlen : xs.length = m.size - sz.toNat) (Q : Nat × Nat → IProp GF) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      osMeta (L := L) d.ino (DFrac.own (1 : Qp).half) m -∗
      osBytes (L := L) d.ino (min m.size sz.toNat) (DFrac.own (1 : Qp).half) xs -∗
      osAUnc (L := L) (A := Nat × Nat)
        iprop(osMeta (L := L) d.ino (DFrac.own (1 : Qp).half) m ∗
          osBytes (L := L) d.ino (min m.size sz.toNat) (DFrac.own (1 : Qp).half) xs)
        (fun tn => rsTok (L := L) true tn.1 d.ino sz.toNat m xs tn.2) Q -∗
      iprop(∀ t : Nat, ∀ n : Nat, ⌜∀ x ∈ xs, ∀ q ∈ x.2, q.2 < n⌝ -∗ osFd (L := L) fd dq d -∗
        Q (t, n) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) {{ Φ }} := by
  iintro #Hinv Hfd Hm Hb Hau HΦ
  iapply wp_aunc_step "FtruncateStart" _ _ _ _ Φ $$ Hau
  iintro ⟨Hm', Hb'⟩
  ihave Hm : osMeta (L := L) d.ino (DFrac.own 1) m $$ [Hm Hm']
  · iapply (osMeta_halves (L := L) d.ino m).2; iframe
  ihave Hb : osBytes (L := L) d.ino (min m.size sz.toNat) (DFrac.own 1) xs $$ [Hb Hb']
  · have hb := osBytes_frac (L := L) d.ino (min m.size sz.toNat) (1 : Qp).half (1 : Qp).half xs
    rw [Qp.half_add_half] at hb
    iapply hb.2
    iframe
  ihave Hc := mcellsAny_nomaps (GF := GF) (min m.size sz.toNat) (rsHi true m.size sz.toNat)
  rw [← hmaps]
  iapply wp_osFtruncateStart fd sz dq d m xs osN_sub_au hwr hsz0 hlen $$ Hinv Hfd Hm Hb Hc
  iintro %t %n %hn Hfd Ht
  iright
  iexists (t, n)
  iframe Ht
  iintro HQ
  iapply HΦ $$ %t %n %hn Hfd HQ

/-- **`ftruncate`'s second step, split**: the update lends the token and commits with what the step
leaves (`rsOutT`). -/
theorem wp_osFtruncateFinish_au (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (xs : List ByteG)
    (n : Nat) (Q : w64 → IProp GF) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗
      osAUnc (L := L) (A := w64) (rsTok (L := L) true t p tg m xs n) (rsOutT (L := L) p tg m xs n) Q -∗
      (∀ e : w64, Q e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FtruncateFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hinv Hau HΦ
  iapply wp_aunc_step "FtruncateFinish" _ _ _ _ Φ $$ Hau
  iintro Ht
  iapply wp_osFtruncateFinishK m.cut.isNone t p tg m xs n Option.isNone_iff_eq_none.1 osN_sub_au $$ Hinv Ht
  iintro %e Hr
  iright
  iexists e
  isplitl [Hr]
  · unfold rsOutT; iexact Hr
  iintro HQ
  iapply HΦ $$ HQ

/-- **`fallocate`'s first step (mode 0), split**: the caller's half of the `OsMeta`, the update's
lent at the step; the update commits with the token of the growth to `max size (off + len)`. -/
theorem wp_osFallocStart_au (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) (hmaps : m.maps = ∅)
    (Q : Nat × Nat → IProp GF) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      osMeta (L := L) d.ino (DFrac.own (1 : Qp).half) m -∗
      osAUnc (L := L) (A := Nat × Nat) (osMeta (L := L) d.ino (DFrac.own (1 : Qp).half) m)
        (fun tn => rsTok (L := L) false tn.1 d.ino (max m.size (off.toNat + len.toNat)) m [] tn.2) Q -∗
      iprop(∀ t : Nat, ∀ n : Nat, osFd (L := L) fd dq d -∗ Q (t, n) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FallocStart" (Val (PairV (#fd) (PairV (#off) (#len))))) {{ Φ }} := by
  iintro #Hinv Hfd Hm Hau HΦ
  iapply wp_aunc_step "FallocStart" _ _ _ _ Φ $$ Hau
  iintro Hm'
  ihave Hm : osMeta (L := L) d.ino (DFrac.own 1) m $$ [Hm Hm']
  · iapply (osMeta_halves (L := L) d.ino m).2; iframe
  ihave Hc := mcellsAny_nomaps (GF := GF) m.size (max m.size (off.toNat + len.toNat))
  rw [← hmaps]
  iapply wp_osFallocStart fd off len dq d m osN_sub_au hwr hoff hlen $$ Hinv Hfd Hm Hc
  iintro %t %n Hfd Ht
  iright
  iexists (t, n)
  iframe Ht
  iintro HQ
  iapply HΦ $$ %t %n Hfd HQ

/-- **`fallocate`'s second step, split**: the update lends the token and commits with what the step
leaves (`rsOutF`). -/
theorem wp_osFallocFinish_au (t : Nat) (p : Ino) (tg : Nat) (m : OsMeta) (n : Nat)
    (hgrow : m.size ≤ tg) (Q : w64 → IProp GF) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗
      osAUnc (L := L) (A := w64) (rsTok (L := L) false t p tg m [] n) (rsOutF (L := L) p tg m n) Q -∗
      (∀ e : w64, Q e -∗ Φ (#e)) -∗
      WP (ExternalOp fsExt.name "FallocFinish" (Val (osTokV t))) {{ Φ }} := by
  iintro #Hinv Hau HΦ
  iapply wp_aunc_step "FallocFinish" _ _ _ _ Φ $$ Hau
  iintro Ht
  iapply wp_osFallocFinishK m.cut.isNone t p tg m n hgrow Option.isNone_iff_eq_none.1 osN_sub_au $$ Hinv Ht
  iintro %e Hr
  iright
  iexists e
  isplitl [Hr]
  · unfold rsOutF; iexact Hr
  iintro HQ
  iapply HΦ $$ HQ

end au

end Fs
end Perennial

end
