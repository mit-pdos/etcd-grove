/-
**One `copy_file_range` round of `io.CopyFiles.spec`'s copy** (`model.copyFileRangeRound`,
`TrustedCode/os.lean`): the extension's `PRead` of up to `max` bytes at the source's offset, then
`PWriteStart`/`PWriteFinish` of what it read at the destination's offset, both offsets moved by the count
written. Over a destination held as `io.copyDst` at the values `vs` (its offset `|vs|`, its end), it
writes the source's next `k` bytes: `k > 0` only with errno 0, and `k = 0` with errno 0 only at the
source's end. Lean-first.
-/
module

public import Proof.io.CopyDefs
public import Proof.os.ReadEof
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

/-- Signed sums of small words. -/
theorem os.cfr_sumZ (a b : w64) (ha : a.toNat < 2 ^ 61) (hb : b.toNat ≤ 0x7ffff000) :
    sint.Z (a + b) = a.toNat + b.toNat := by
  simp only [sint.Z]; word

theorem os.cfr_natZ (n : Nat) (h : n < 2 ^ 61) : sint.Z (W64 n) = n ∧ (W64 n).toNat = n := by
  simp only [sint.Z]; constructor <;> word

theorem os.cfr_W64_add (a b : Nat) : W64 (a : Int) + W64 (b : Int) = W64 ((a + b : Nat) : Int) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega

theorem os.cfr_W64_addI (a b : Int) : W64 a + W64 b = W64 (a + b) := by
  apply BitVec.eq_of_toInt_eq; simp [BitVec.toInt_add]

theorem os.cfr_natInt (n : Nat) (h : n < 2 ^ 61) : (W64 (n : Int)).toInt = n := by word

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [os.Assumptions]

/-- **One `copy_file_range` round** (see the file header). -/
theorem os.wp_cfrRound (ind ins : Loc) (fdd fds doff soff mx : w64) (dqd dqs dqfd dqfs : DFrac)
    (dd ds : OsFd) (m : OsMeta) (qm qb : DFrac) (bs : List ByteG) (vs : List w8)
    (hfdd : 0 ≤ fdd.toInt) (hfds : 0 ≤ fds.toInt) (hwr : dd.writable = true) (hrd : ds.readable = true)
    (hdoff : doff = W64 vs.length) (hs0 : 0 ≤ soff.toInt) (hsoff : soff.toNat ≤ bs.length)
    (hbs : bs.length = m.size) (hm : m.size < 2 ^ 61) (hvs : vs.length ≤ m.size)
    (hmx0 : 0 < mx.toInt) (hmx : mx.toInt ≤ 0x7ffff000) :
    {{ osInv (GF := GF) ∗ structFieldRef os.file go!"fd" ind ↦{dqd} fdd ∗
        structFieldRef os.file go!"off" ind ↦ doff ∗
        structFieldRef os.file go!"fd" ins ↦{dqs} fds ∗ structFieldRef os.file go!"off" ins ↦ soff ∗
        osFd fdd dqfd dd ∗ osFd fds dqfs ds ∗ osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗
        io.copyDst dd.ino (· = vs) }}
      (App (App (App (Val os.model.copyFileRangeRound) (Val #ind)) (Val #ins)) (Val #mx))
    {{ (w e : w64), RET (PairV #w #e);
        structFieldRef os.file go!"fd" ind ↦{dqd} fdd ∗ structFieldRef os.file go!"fd" ins ↦{dqs} fds ∗
        osFd fdd dqfd dd ∗ osFd fds dqfs ds ∗ osMeta ds.ino qm m ∗ osBytes ds.ino 0 qb bs ∗
        ∃ k : Nat, ⌜w = W64 k ∧ k ≤ mx.toNat ∧ (0 < k → e = W64 0) ∧
            (k = 0 → e = W64 0 → bs.length ≤ soff.toNat) ∧ soff.toNat + k ≤ bs.length⌝ ∗
          structFieldRef os.file go!"off" ind ↦ (doff + W64 k) ∗
          structFieldRef os.file go!"off" ins ↦ (soff + W64 k) ∗
          io.copyDst dd.ino (· = vs ++ ((bs.map Prod.fst).drop soff.toNat).take k) }} := by
  wp_start as ⟨#Hinv, Hdfd, Hdoff, Hsfd, Hsoff, Hfdd, Hfds, Hm, Hbs, Hdst⟩
  rw [os.file_ty_eq]
  have hvsN : vs.length < 2 ^ 61 := by omega
  have hdZ : sint.Z doff = vs.length := by rw [hdoff]; exact (os.cfr_natZ _ hvsN).1
  have hdN : doff.toNat = vs.length := by rw [hdoff]; exact (os.cfr_natZ _ hvsN).2
  have hsZ : sint.Z soff = soff.toNat := by simp only [sint.Z]; word
  have hmxZ : sint.Z mx = mx.toNat := by simp only [sint.Z]; word
  have hz0 : sint.Z (W64 0) = 0 := rfl
  have hmxN : mx.toNat ≤ 0x7ffff000 ∧ 0 < mx.toNat := by
    have := hmxZ; simp only [sint.Z] at this; omega
  have hsN : soff.toNat < 2 ^ 61 := by omega
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z fdd < sint.Z (W64 0) by rw [hz0]; exact Int.not_lt.2 hfdd)]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z fds < sint.Z (W64 0) by rw [hz0]; exact Int.not_lt.2 hfds)]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z doff < sint.Z (W64 0) by rw [hz0, hdZ]; omega)]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z soff < sint.Z (W64 0) by rw [hz0]; omega)]
  wp_auto
  rw [show os.model.offMax = W64 0x4000000000000000 from rfl]
  have hd2 : sint.Z (doff + mx) = vs.length + mx.toNat := by
    rw [os.cfr_sumZ doff mx (by omega) hmxN.1, hdN]
  have hs2 : sint.Z (soff + mx) = soff.toNat + mx.toNat := os.cfr_sumZ soff mx hsN hmxN.1
  have hmax : sint.Z (W64 0x4000000000000000) = 2 ^ 62 := rfl
  rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (doff + mx) by
    rw [hd2, hmax]; omega)]
  wp_auto
  rw [decide_eq_false (show ¬ sint.Z (W64 0x4000000000000000) ≤ sint.Z (soff + mx) by
    rw [hs2, hmax]; omega)]
  wp_auto
  -- the `pread` of the source
  have hmidl : ((bs.drop soff.toNat).take mx.toNat).length = min mx.toNat (m.size - soff.toNat) := by
    simp only [List.length_take, List.length_drop]; omega
  ihave ⟨Hmid, Hback⟩ := os.osBytes_mid ds.ino qb bs soff.toNat mx.toNat $$ Hbs
  wp_apply wp_osPRead fds soff mx dqfs qm qb ds m ((bs.drop soff.toNat).take mx.toNat)
    CoPset.subseteq_top hrd hs0 hmidl $$ Hinv Hfds Hm Hmid as %r %e %hre Hfds Hm Hmid
  ihave Hbs := Hback $$ Hmid
  obtain ⟨k', hk'l, hr, hke⟩ := hre
  have hrv : r = ((bs.map Prod.fst).drop soff.toNat).take k' := by
    rw [hr, List.map_take, List.map_drop, List.take_take]
    rw [Nat.min_eq_left (by rw [hmidl] at hk'l; omega)]
  by_cases he0 : e = W64 0
  rotate_left
  · -- an errno: nothing copied
    rw [decide_eq_false he0]
    wp_auto
    iapply HΦ
    iframe Hdfd Hsfd Hfdd Hfds Hm Hbs
    iexists 0
    simp only [List.take_zero, List.append_nil, show doff + W64 (0 : Nat) = doff by simp,
      show soff + W64 (0 : Nat) = soff by simp]
    iframe Hdoff Hsoff Hdst
    ipureintro
    exact ⟨rfl, Nat.zero_le _, fun h => absurd h (Nat.lt_irrefl 0), fun _ h => absurd h he0, by omega⟩
  subst he0
  rw [show decide ((W64 0) = W64 0) = true from decide_eq_true rfl]
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len r
  iintro %-
  wp_auto
  have hrl : r.length = k' := by
    rw [hrv, List.length_take, List.length_drop, List.length_map]; rw [hmidl] at hk'l; omega
  by_cases hk0 : k' = 0
  · -- the source's end
    have hlz : r.length = 0 := by omega
    rw [decide_eq_true (show (W64 r.length) = W64 0 by rw [hlz]; rfl)]
    wp_auto
    iapply HΦ
    iframe Hdfd Hsfd Hfdd Hfds Hm Hbs
    iexists 0
    simp only [List.take_zero, List.append_nil, show doff + W64 (0 : Nat) = doff by simp,
      show soff + W64 (0 : Nat) = soff by simp]
    iframe Hdoff Hsoff Hdst
    ipureintro
    refine ⟨rfl, Nat.zero_le _, fun h => absurd h (Nat.lt_irrefl 0), fun _ _ => ?_, by omega⟩
    rcases hke rfl with h | h
    · omega
    · have := congrArg List.length h
      rw [hmidl, List.length_nil] at this
      omega
  have hrne : ¬ (W64 r.length) = W64 0 := by
    intro h; have := congrArg BitVec.toNat h
    simp at this; omega
  rw [decide_eq_false hrne]
  wp_auto
  -- the destination, at its end
  ihave ⟨%md, %xs, Hmd, Hxs, %hmd⟩ := io.copyDst_elim dd.ino _ $$ Hdst
  obtain ⟨hok, hxl, hvs'⟩ := hmd
  have hxv : xs.length = vs.length := by rw [← hvs', List.length_map]
  ihave Hend : osBytes (GF := GF) dd.ino doff.toNat (DFrac.own 1) [] $$ []
  · unfold osBytes bytesG; iapply BigSepL.bigSepL_nil.2; iempintro
  ihave Hmc : mcellsAny (GF := GF) md.maps doff.toNat (doff.toNat + r.length) $$ []
  · rw [hok.1]; unfold mcellsAny; iapply BigSepM.bigSepM_empty.2; itrivial
  wp_apply wp_osPWriteStart fdd doff r dqfd dd md [] CoPset.subseteq_top hwr
    (by have := hdZ; simp only [sint.Z] at this; omega) (by omega)
    (fun h => by subst h; simp only [List.length_nil] at hrl; omega) (by simp only [List.length_nil]; omega)
    $$ Hinv Hfdd Hmd Hend Hmc as %t %nst %- Hfdd Ht
  wp_apply wp_osPWriteFinish t dd.ino doff.toNat r md [] nst CoPset.subseteq_top
    $$ Hinv Ht as %k %e' %zs %hfin %hpc Hmd Hnew Hmc
  have hdm : doff.toNat = md.size := by rw [hdN, ← hxv, hxl]
  have hrpos : 0 < r.length := by omega
  obtain ⟨hkr, hke', -⟩ := hfin
  rw [hdm]
  ihave Hdst := io.copyDst_after dd.ino md xs r k nst zs hok hxl hrpos hkr $$ [Hmd Hxs Hnew]
  · iframe
  have hvk : xs.map (·.1) ++ r.take k = vs ++ ((bs.map Prod.fst).drop soff.toNat).take k := by
    rw [hvs', hrv, List.take_take, Nat.min_eq_left (by omega)]
  rw [hvk]
  by_cases hk0' : k = 0
  · subst hk0'
    rw [decide_eq_true (show (W64 ((0 : Nat) : Int)) = W64 0 from rfl)]
    wp_auto
    iapply HΦ
    iframe Hdfd Hsfd Hfdd Hfds Hm Hbs
    iexists 0
    simp only [List.take_zero, List.append_nil, show doff + W64 (0 : Nat) = doff by simp,
      show soff + W64 (0 : Nat) = soff by simp]
    simp only [List.take_zero, List.append_nil] at hvk
    iframe Hdoff Hsoff Hdst
    ipureintro
    refine ⟨rfl, Nat.zero_le _, fun h => absurd h (Nat.lt_irrefl 0), fun _ h => ?_, by omega⟩
    rcases hke' with ⟨h1, -⟩ | h1
    · omega
    · exact absurd h h1
  have hkne : ¬ (W64 (k : Int)) = W64 0 := by
    intro h; have := congrArg BitVec.toNat h
    simp at this; omega
  rw [decide_eq_false hkne]
  wp_auto
  iapply HΦ
  iframe Hdfd Hsfd Hfdd Hfds Hm Hbs
  iexists k
  iframe Hdoff Hsoff Hdst
  ipureintro
  exact ⟨rfl, by omega, fun _ => rfl, fun h => absurd h hk0', by rw [hmidl] at hk'l; omega⟩

end proof

end EtcdGrove
end Perennial
