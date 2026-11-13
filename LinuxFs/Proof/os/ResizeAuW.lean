/-
The resizes' first steps (`ftruncate`, `fallocate`'s growth) under an atomic update that **lends the
whole** of the file's `OsMeta` (and of the bytes cut off): the form a crash invariant sharing the
file with a program can supply (I3b of `notes/wal-fsext-plan.md`, "The updates' shape"). The program
puts its halves into the update (the update's owner checks them against its own by agreement, so it
knows the state the step starts from), and the update keeps the program's tie with the owner's
record of the change (its `Q`) until the second step (`ResizeAu.lean`'s `wp_osFtruncateFinish_au`,
`wp_osFallocFinish_au`, which already lend the whole token). Lean-first (no Rocq counterpart).
Untrusted.

`ResizeAu.lean`'s `wp_osFtruncateStart_au`/`wp_osFallocStart_au` (the caller keeps its half and the
update lends the other) cannot be supplied by an invariant: the update would have to lend the half of
the state the caller is in without seeing the caller's half.
-/
module

public import LinuxFs.Proof.os.ResizeAu

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode

section au
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- **`ftruncate`'s first step, the update lending the whole**: of the `OsMeta` and of the bytes cut
off; it commits with the token. -/
theorem wp_osFtruncateStart_auW (fd sz : w64) (dq : DFrac) (d : OsFd) (m : OsMeta) (xs : List ByteG)
    (hwr : d.writable = true) (hsz0 : 0 ≤ sz.toInt) (hmaps : m.maps = ∅)
    (hlen : xs.length = m.size - sz.toNat) (Q : Nat × Nat → IProp GF) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      osAUnc (L := L) (A := Nat × Nat)
        iprop(osMeta (L := L) d.ino (DFrac.own 1) m ∗
          osBytes (L := L) d.ino (min m.size sz.toNat) (DFrac.own 1) xs)
        (fun tn => rsTok (L := L) true tn.1 d.ino sz.toNat m xs tn.2) Q -∗
      iprop(∀ t : Nat, ∀ n : Nat, ⌜∀ x ∈ xs, ∀ q ∈ x.2, q.2 < n⌝ -∗ osFd (L := L) fd dq d -∗
        Q (t, n) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FtruncateStart" (Val (PairV (#fd) (#sz)))) {{ Φ }} := by
  iintro #Hinv Hfd Hau HΦ
  iapply wp_aunc_step "FtruncateStart" _ _ _ _ Φ $$ Hau
  iintro ⟨Hm, Hb⟩
  ihave Hc := mcellsAny_nomaps (GF := GF) (min m.size sz.toNat) (rsHi true m.size sz.toNat)
  rw [← hmaps]
  iapply wp_osFtruncateStart fd sz dq d m xs osN_sub_au hwr hsz0 hlen $$ Hinv Hfd Hm Hb Hc
  iintro %t %n %hn Hfd Ht
  iright
  iexists (t, n)
  iframe Ht
  iintro HQ
  iapply HΦ $$ %t %n %hn Hfd HQ

/-- **`fallocate`'s first step (mode 0), the update lending the whole `OsMeta`**; it commits with the
token of the growth to `max size (off + len)`. -/
theorem wp_osFallocStart_auW (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) (hmaps : m.maps = ∅)
    (Q : Nat × Nat → IProp GF) (Φ : val → IProp GF) :
    ⊢ osInv (L := L) -∗ osFd (L := L) fd dq d -∗
      osAUnc (L := L) (A := Nat × Nat) (osMeta (L := L) d.ino (DFrac.own 1) m)
        (fun tn => rsTok (L := L) false tn.1 d.ino (max m.size (off.toNat + len.toNat)) m [] tn.2) Q -∗
      iprop(∀ t : Nat, ∀ n : Nat, osFd (L := L) fd dq d -∗ Q (t, n) -∗ Φ (osTokV t)) -∗
      WP (ExternalOp fsExt.name "FallocStart" (Val (PairV (#fd) (PairV (#off) (#len))))) {{ Φ }} := by
  iintro #Hinv Hfd Hau HΦ
  iapply wp_aunc_step "FallocStart" _ _ _ _ Φ $$ Hau
  iintro Hm
  ihave Hc := mcellsAny_nomaps (GF := GF) m.size (max m.size (off.toNat + len.toNat))
  rw [← hmaps]
  iapply wp_osFallocStart fd off len dq d m osN_sub_au hwr hoff hlen $$ Hinv Hfd Hm Hc
  iintro %t %n Hfd Ht
  iright
  iexists (t, n)
  iframe Ht
  iintro HQ
  iapply HΦ $$ %t %n Hfd HQ

end au

end Fs
end Perennial

end
