/-
Specs of `syscall`'s trusted models of `Fallocate` (mode 0, growing the file, and
`FALLOC_FL_KEEP_SIZE`) and `FcntlFlock` (the commands that set a lock), over the extension's
(`GooseLang/Ext/Fs/Falloc.lean`): the same models as `golang.org/x/sys/unix`'s, and these the
same proofs as `Proof/golang_org/x/sys/unix/FileOps.lean`'s (fileutil's `Preallocate` and
`LockFile` call `syscall`'s). Mode-agnostic: they hold in the tree's shared mode too. Lean-first
(no Rocq counterpart).
-/
module

public import LinuxFs.GeneratedProof.syscall
public import LinuxFs.Proof.syscall.Base
public import GooseLang.Ext.Fs.Falloc

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

/-- `syscall.Fallocate(fd, 0, off, len)`, with the file's `OsMeta` whole and the client's halves of
the mapped cells over the bytes it grows the file over: a resize to `tg := max size (off + len)`
(`Falloc.lean`), its change number `n`. On success the file is grown to `tg`, the new bytes zeros
(`rsDone`); on failure nothing landed (`rsUndone`) or a prefix of the growth did (`rsDone` at its
end). -/
theorem syscall.Fallocate.wp_grow (fd off len : w64) (dq : DFrac) (d : OsFd)
    (m : OsMeta) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) :
    {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
        mcellsAny (GF := GF) m.maps m.size (max m.size (off.toNat + len.toNat)) }}
      (App (App (App (App (Val (@! syscall.Fallocate)) (Val #fd)) (Val #(W32 0)))
        (Val #off)) (Val #len))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗ ∃ n : Nat,
        ((⌜e = 0⌝ ∗ rsDone d.ino (max m.size (off.toNat + len.toNat))
            (max m.size (off.toNat + len.toNat)) m n) ∨
         (⌜e ≠ 0⌝ ∗ (rsUndone d.ino (max m.size (off.toNat + len.toNat)) m [] n ∨
           ∃ w, ⌜m.size ≤ w ∧ w ≤ max m.size (off.toNat + len.toNat)⌝ ∗
             rsDone d.ino (max m.size (off.toNat + len.toNat)) w m n))) }} := by
  wp_start as ⟨#Hinv, Hfd, Hm, Hc⟩
  wp_apply wp_osFallocStart fd off len dq d m CoPset.subseteq_top hwr hoff hlen
    $$ Hinv Hfd Hm Hc as %t %n Hfd Ht
  wp_apply wp_osFallocFinish t d.ino _ m n (Nat.le_max_left _ _) CoPset.subseteq_top
    $$ Hinv Ht as %e Hr
  iapply wp_errno
  iapply HΦ
  iframe Hfd
  iexists n
  iexact Hr

/-- `syscall.Fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: no visible change, any errno. -/
theorem syscall.Fallocate.wp_keep (fd off len : w64) (dq : DFrac) (d : OsFd)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) :
    {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d }}
      (App (App (App (App (Val (@! syscall.Fallocate)) (Val #fd)) (Val #(W32 1)))
        (Val #off)) (Val #len))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d }} := by
  wp_start as ⟨#Hinv, Hfd⟩
  wp_apply wp_osFallocKeep fd off len dq d CoPset.subseteq_top hwr hoff hlen $$ Hinv Hfd as %e Hfd
  iapply wp_errno
  iapply HΦ
  iframe

/-- `syscall.FcntlFlock(fd, cmd, lk)` for a command that sets a lock (`F_SETLK`, `F_SETLKW`,
`F_OFD_SETLK`, `F_OFD_SETLKW`): any errno. -/
theorem syscall.FcntlFlock.wp_lock (fd cmd : w64) (lk : Loc) (dq : DFrac) (d : OsFd)
    (hcmd : cmd = W64 6 ∨ cmd = W64 7 ∨ cmd = W64 37 ∨ cmd = W64 38) :
    {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d }}
      (App (App (App (Val (@! syscall.FcntlFlock)) (Val #fd)) (Val #cmd)) (Val #lk))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d }} := by
  wp_start as ⟨#Hinv, Hfd⟩
  rcases hcmd with rfl | rfl | rfl | rfl <;>
  · (try wp_auto)
    wp_apply wp_osOfdLock fd _ dq d CoPset.subseteq_top $$ Hinv Hfd as %e Hfd
    iapply wp_errno
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
