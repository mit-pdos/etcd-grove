/-
`syscall.Fallocate(fd, 0, off, len)` on a file whose resources are split between the caller and
atomic updates (I3b of `notes/wal-fsext-plan.md`; `Proof/os/ResizeAu.lean`), as the WAL's tail is
between its handle and `walInv`: the growth's two steps (`FallocStart`, `FallocFinish`, no retry)
each open an update with the crash token (`osAUnc`). Lean-first (no Rocq counterpart).

The caller holds half of the file's `OsMeta`; the first update lends the other half at the start
step and commits with the growth's token (`rsTok`), its commit giving the second update, which lends
the token at the finish step and commits with what the step leaves (`rsOutF`, whole: the update's
owner splits it), `Q n e` the caller's. `syscall.Fallocate.wp_grow` (`FileOps.lean`, whole
resources) is the case of updates that own nothing.

`wp_growAuW` is the form an invariant sharing the file can supply (`ResizeAuW.lean`): the caller
hands its half to the update (`fallocSup`, with its tie `K`), which lends the whole `OsMeta`; the
caller's share of the outcome is `fallocOutH` (its halves of `rsOutF`) and `K`.
-/
module

public import LinuxFs.GeneratedProof.syscall
public import LinuxFs.Proof.syscall.Base
public import LinuxFs.Proof.os.ResizeAuW
public import GooseLang.Ext.Fs.Zeros

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [syscall.Assumptions]

/-- The updates of a growth of the file `i` from `m` to `tg`, split (see the file header): the
start's, lending the other half of the `OsMeta` for the token, whose commit is the finish's,
lending the token for the outcome. -/
def fallocAu (i : Ino) (tg : Nat) (m : OsMeta) (Q : Nat → w64 → IProp GF) : IProp GF :=
  osAUnc (A := Nat × Nat) (osMeta i (DFrac.own (1 : Qp).half) m)
    (fun tn => rsTok false tn.1 i tg m [] tn.2)
    (fun tn => osAUnc (A := w64) (rsTok false tn.1 i tg m [] tn.2) (rsOutF i tg m tn.2) (Q tn.2))

/-- **`syscall.Fallocate(fd, 0, off, len)`, split**: the caller's half of the `OsMeta` of an unmapped
file, the updates `fallocAu` for the rest; the outcome's share `Q n e`, `n` the change's number. -/
theorem syscall.Fallocate.wp_growAu (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (Q : Nat → w64 → IProp GF) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hlen : 0 < len.toInt) (hmaps : m.maps = ∅) :
    {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
        osMeta (GF := GF) d.ino (DFrac.own (1 : Qp).half) m ∗
        fallocAu (GF := GF) d.ino (max m.size (off.toNat + len.toNat)) m Q }}
      (App (App (App (App (Val (@! syscall.Fallocate)) (Val #fd)) (Val #(W32 0)))
        (Val #off)) (Val #len))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗ ∃ n : Nat, Q n e }} := by
  wp_start as ⟨#Hinv, Hfd, Hm, Hau⟩
  unfold fallocAu
  wp_apply wp_osFallocStart_au fd off len dq d m hwr hoff hlen hmaps _ $$ Hinv Hfd Hm Hau
    as %t %n Hfd Hau
  wp_apply wp_osFallocFinish_au t d.ino _ m n (Nat.le_max_left _ _) _ $$ Hinv Hau as %e HQ
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  iexists n
  iexact HQ

/-- The caller's halves of a growth of `i` from `m` to `tg` that landed with the size `w`: the
`OsMeta` (up to the candidates it knows past the size and the resize stamps, `rsPostK`'s), and the bytes grown over,
zeros. -/
def fallocDoneH (i : Ino) (m : OsMeta) (tg w : Nat) : IProp GF :=
  iprop(∃ tc rz, osMeta i (DFrac.own (1 : Qp).half) ((rsPost false m tg w).withTc tc rz) ∗
    osZerosA i m.size (w - m.size) (DFrac.own (1 : Qp).half))

/-- **The caller's halves of a growth's outcome** (`rsOutF`'s): on success the growth landed; on
failure none of it (the `OsMeta` as announced), or a prefix. -/
def fallocOutH (i : Ino) (tg : Nat) (m : OsMeta) (e : w64) : IProp GF :=
  iprop((⌜e = 0⌝ ∗ fallocDoneH i m tg tg) ∨
    (⌜e ≠ 0⌝ ∗ (osMeta i (DFrac.own (1 : Qp).half) (m.announce (min m.size tg) (rsHi false m.size tg) tg) ∨
      ∃ w, ⌜m.size ≤ w ∧ w ≤ tg⌝ ∗ fallocDoneH i m tg w)))

/-- **The updates of a growth of `i` from `m` to `tg`, the update lending the whole `OsMeta`**, the
caller's share `Q`. -/
def fallocAuW (i : Ino) (tg : Nat) (m : OsMeta) (Q : Nat → w64 → IProp GF) : IProp GF :=
  osAUnc (A := Nat × Nat) (osMeta i (DFrac.own 1) m)
    (fun tn => rsTok false tn.1 i tg m [] tn.2)
    (fun tn => osAUnc (A := w64) (rsTok false tn.1 i tg m [] tn.2) (rsOutF i tg m tn.2) (Q tn.2))

/-- **The supply of a growth of `i` to `tg`**, the caller's tie `K` (persistent): from any `OsMeta`
at most `tg` long, the caller's half and `K` make the growth's updates, the caller's share its halves
of the outcome and `K`. -/
def fallocSup (K : IProp GF) (i : Ino) (tg : Nat) : IProp GF :=
  iprop(□ ∀ m0 : OsMeta, ⌜m0.size ≤ tg⌝ -∗ K -∗ osMeta i (DFrac.own (1 : Qp).half) m0 -∗
    fallocAuW i tg m0 (fun _ e => iprop(fallocOutH i tg m0 e ∗ K)))

instance fallocSup_persistent (K : IProp GF) (i : Ino) (tg : Nat) :
    Persistent (fallocSup (GF := GF) K i tg) := by
  unfold fallocSup; infer_instance

/-- **`syscall.Fallocate(fd, 0, off, len)`, the update lending the whole `OsMeta`** (see the file
header): the caller holds none of the file's resources. -/
theorem syscall.Fallocate.wp_growAuW (fd off len : w64) (dq : DFrac) (d : OsFd) (m : OsMeta)
    (Q : Nat → w64 → IProp GF) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt)
    (hlen : 0 < len.toInt) (hmaps : m.maps = ∅) :
    {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗
        fallocAuW (GF := GF) d.ino (max m.size (off.toNat + len.toNat)) m Q }}
      (App (App (App (App (Val (@! syscall.Fallocate)) (Val #fd)) (Val #(W32 0)))
        (Val #off)) (Val #len))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗ ∃ n : Nat, Q n e }} := by
  wp_start as ⟨#Hinv, Hfd, Hau⟩
  unfold fallocAuW
  wp_apply wp_osFallocStart_auW fd off len dq d m hwr hoff hlen hmaps _ $$ Hinv Hfd Hau
    as %t %n Hfd Hau
  wp_apply wp_osFallocFinish_au t d.ino _ m n (Nat.le_max_left _ _) _ $$ Hinv Hau as %e HQ
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  iexists n
  iexact HQ

end proof

end EtcdGrove
end Perennial

end
