/-
Specs of `syscall`'s trusted models of `Fallocate` (mode 0, growing the file, and
`FALLOC_FL_KEEP_SIZE`) and `FcntlFlock` (the commands that set a lock, and the query `F_OFD_GETLK` on any fd), over the extension's
(`GooseLang/Ext/Fs/Falloc.lean`): the same models as `golang.org/x/sys/unix`'s, and these the
same proofs as `Proof/golang_org/x/sys/unix/FileOps.lean`'s (fileutil's `Preallocate` and
`LockFile` call `syscall`'s). Mode-agnostic: they hold in the tree's shared mode too. Lean-first
(no Rocq counterpart).
-/
module

public import GeneratedProof.syscall
public import Proof.syscall.Base
public import Proof.internal.gomodel.LocalChoose
public import GooseLang.Ext.Fs.Falloc
public import GooseLang.Ext.Fs.Locks
public import GooseLang.Ext.Fs.NoMapLockErrSpecs
public import GooseLang.Ext.Fs.NoIoErrResize

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
end), and the error witnessed: the file system can fail on an inode, or `tg` is past `maxBytes`. -/
theorem syscall.Fallocate.wp_grow [go.BasicIntoValInj] (fd off len : w64) (dq : DFrac) (d : OsFd)
    (m : OsMeta) (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) :
    {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d ∗ osMeta (GF := GF) d.ino (DFrac.own 1) m ∗
        mcellsAny (GF := GF) m.maps m.size (max m.size (off.toNat + len.toNat)) }}
      (App (App (App (App (Val (@! syscall.Fallocate)) (Val #fd)) (Val #(W32 0)))
        (Val #off)) (Val #len))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗ ∃ n : Nat,
        ((⌜e = 0⌝ ∗ rsDone false d.ino (max m.size (off.toNat + len.toNat))
            (max m.size (off.toNat + len.toNat)) m n) ∨
         (⌜e ≠ 0⌝ ∗ (rsUndone false d.ino (max m.size (off.toNat + len.toNat)) m [] n ∨
           ∃ w, ⌜m.size ≤ w ∧ w ≤ max m.size (off.toNat + len.toNat)⌝ ∗
             rsDone false d.ino (max m.size (off.toNat + len.toNat)) w m n))) ∗
        ⌜e ≠ 0 → ¬ FsNoErrIno ∨ maxBytes < max m.size (off.toNat + len.toNat)⌝ }} := by
  wp_start as ⟨#Hinv, Hfd, Hm, Hc⟩
  try wp_auto
  wp_stub syscall.fsFalloc.impl
  wp_apply wp_osFallocStart fd off len dq d m CoPset.subseteq_top hwr hoff hlen
    $$ Hinv Hfd Hm Hc as %t %n %_ Hfd Ht
  wp_apply wp_osFallocFinishW t d.ino _ m n (Nat.le_max_left _ _) CoPset.subseteq_top
    $$ Hinv Ht as %e Hr %hw
  try wp_auto
  wp_apply wp_errnoErr
  try wp_auto
  iapply HΦ
  iframe Hfd
  iexists n
  iframe Hr
  ipureintro; exact hw

/-- `syscall.Fallocate(fd, FALLOC_FL_KEEP_SIZE, off, len)`: no visible change, any errno. -/
theorem syscall.Fallocate.wp_keep (fd off len : w64) (dq : DFrac) (d : OsFd)
    (hwr : d.writable = true) (hoff : 0 ≤ off.toInt) (hlen : 0 < len.toInt) :
    {{ osInv (GF := GF) ∗ osFd (GF := GF) fd dq d }}
      (App (App (App (App (Val (@! syscall.Fallocate)) (Val #fd)) (Val #(W32 1)))
        (Val #off)) (Val #len))
    {{ (e : w64), RET #(errnoErr e); osFd fd dq d }} := by
  wp_start as ⟨#Hinv, Hfd⟩
  try wp_auto
  wp_stub syscall.fsFallocKeep.impl
  wp_apply wp_osFallocKeep fd off len dq d CoPset.subseteq_top hwr hoff hlen $$ Hinv Hfd as %e Hfd
  try wp_auto
  wp_apply wp_errnoErr
  try wp_auto
  iapply HΦ
  iframe

/-- `syscall.FcntlFlock(fd, cmd, lk)` for `F_OFD_SETLK` (37) or `F_OFD_SETLKW` (38) with a whole-file
description `*lk` (`Whence`, `Start`, `Len`, `Pid` all 0) of type `F_RDLCK`, `F_WRLCK` or `F_UNLCK`
(`ofdReq`: the request `req`): the extension's OFD lock (`wp_osOfdLockW`), `*lk` read only; a blocking
request's error witnessed (`¬ FsNoErrIno`). -/
theorem syscall.FcntlFlock.wp_lock (fd cmd : w64) (lk : Loc) (v : syscall.Flock_t)
    (d : OsFd) (req : Option Bool) (hcmd : cmd = W64 37 ∨ cmd = W64 38)
    (hwh : v.Whence' = 0) (hst : v.Start' = 0) (hln : v.Len' = 0) (hpid : v.Pid' = 0)
    (hreq : ofdReq v.Type'.toNat = some req) (hw : req = some true → d.writable = true)
    (hr : req = some false → d.readable = true) (hfree : req ≠ none → d.ofd = none) :
    {{ osInv (GF := GF) ∗ (lk ↦ v : IProp GF) ∗ osFd (GF := GF) fd (DFrac.own 1) d ∗
        lockTok (GF := GF) .ofd fd d }}
      (App (App (App (Val (@! syscall.FcntlFlock)) (Val #fd)) (Val #cmd)) (Val #lk))
    {{ (e : w64), RET #(errnoErr e); lk ↦ v ∗ ⌜cmd = W64 38 → e ≠ 0 → ¬ FsNoErrIno⌝ ∗
        lockOut (GF := GF) .ofd fd d req e }} := by
  wp_start as ⟨#Hinv, Hlk, Hfd, Ht⟩
  have hty : v.Type' = 0 ∨ v.Type' = 1 ∨ v.Type' = 2 := by
    have h := hreq; unfold ofdReq at h
    split at h <;> (try cases h) <;> bv_omega
  have hreq' : ∀ t : w64, t.toNat = v.Type'.toNat → ofdReq t.toNat = some req := fun t ht => by
    rw [ht]; exact hreq
  rcases hcmd with rfl | rfl <;>
  · try wp_auto
    rw [hwh, hst, hln, hpid]
    try wp_auto
    rcases hty with h0 | h0 | h0 <;> rw [h0] <;> (try wp_auto) <;>
    · wp_stub syscall.fsOfdLock.impl
      wp_apply wp_osOfdLockW fd _ _ d req CoPset.subseteq_top (by decide) (hreq' _ (by rw [h0]; rfl))
        hw hr hfree $$ Hinv Hfd Ht as %e %hW Hout
      try wp_auto
      wp_apply wp_errnoErr
      try wp_auto
      iapply HΦ
      iframe
      ipureintro; exact hW


/-- `syscall.FcntlFlock(fd, F_OFD_GETLK, lk)` on any fd (fileutil's package initializer, on fd 0):
no extension step; `*lk` whole for the call. On success (`e = 0`) its lock description is
arbitrary, its padding as it was; on failure it is unchanged. -/
theorem syscall.FcntlFlock.wp_getlk (fd : w64) (lk : Loc) (v : syscall.Flock_t) :
    {{ (lk ↦ v : IProp GF) }}
      (App (App (App (Val (@! syscall.FcntlFlock)) (Val #fd)) (Val #(W64 36))) (Val #lk))
    {{ (e : w64), RET #(errnoErr e); ∃ v' : syscall.Flock_t, lk ↦ v' ∗
        ⌜v'.Pad_cgo_0' = v.Pad_cgo_0' ∧ v'.Pad_cgo_1' = v.Pad_cgo_1' ∧ (e ≠ 0 → v' = v)⌝ }} := by
  wp_start as Hlk
  try wp_auto
  wp_apply internal.gomodel.ChooseUint64.wp_local as %e -
  try wp_auto
  by_cases he : e = 0
  · subst he
    try wp_auto
    wp_apply internal.gomodel.ChooseUint64.wp_local as %a1 -
    try wp_auto
    wp_apply internal.gomodel.ChooseUint64.wp_local as %a2 -
    try wp_auto
    wp_apply internal.gomodel.ChooseUint64.wp_local as %a3 -
    try wp_auto
    wp_apply internal.gomodel.ChooseUint64.wp_local as %a4 -
    try wp_auto
    wp_apply internal.gomodel.ChooseUint64.wp_local as %a5 -
    try wp_auto
    have h0 : errnoErr (W64 0) = interface.nil := by unfold errnoErr; simp
    rw [← h0]
    iapply HΦ
    iexists _
    iframe
    ipureintro
    exact ⟨rfl, rfl, fun h => absurd rfl h⟩
  · rw [decide_eq_false (show e ≠ W64 0 from he)]
    try wp_auto
    wp_apply wp_errnoErr
    try wp_auto
    iapply HΦ
    iexists v
    iframe
    ipureintro
    exact ⟨rfl, rfl, fun _ => rfl⟩

end proof

end EtcdGrove
end Perennial
