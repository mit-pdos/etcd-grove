/-
`flock(db, exclusive, timeout)` (U11f, `bolt_unix.go`): `syscall.Flock` on the file's descriptor
with `LOCK_NB`, retried (after `time.Sleep`) while it returns `EWOULDBLOCK` until `timeout` (if
any) passes. OsFs's `Flock` is a no-op returning any errno (`Spec/syscall/Flock.lean`), so the spec
is partial: the file is untouched, and an error is one `fmt` formats (an `Errno`, or
`ErrTimeout`). An internal spec of this unit (only `Open` calls `flock`). Over the file-lock
semantics (2026-11-15): from a description with no `flock` lock, `nil` means it holds the lock
asked for (with its token when exclusive), an error that it holds none.
-/
module

public import Proof.go_etcd_io.bbolt.Inv.Locks
public import Proof.go_etcd_io.bbolt.Mmap.Infra
public import Spec.os.File__Fd
public import Spec.syscall.Flock
public import Perennial.Spec.time.Now
public import Perennial.Spec.time.Since
public import Perennial.Spec.time.Sleep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`flock(db, exclusive, timeout)`**: the file is given back; on `nil` the descriptor holds
`flock`'s lock (exclusive if `ex`), with its token (`lockTok`), else it is as it was; an error is
one `fmt` formats (`fmtErrorOkOrNil`), and witnesses that the file system can fail or that a
timeout was set (session S3f: the `flock` loop retries `EWOULDBLOCK` forever without one). -/
abbrev flock.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (d : OsFd) (dqf : DFrac) (ex : Bool)
    (tmo : time.Duration),
  d.flk = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d }}
    (App (App (App (Val #(functions flock [])) (Val #db)) (Val #ex)) (Val #tmo))
  {{ (err : GoInterface), RET #err; db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path (DFrac.own 1) ∗
      fmtErrorOkOrNil err ∗
      ((⌜err = GoInterface.nil⌝ ∗ osFd fd (DFrac.own 1) (d.setLk .flock (some ex)) ∗
          lockTok .flock fd (d.setLk .flock (some ex))) ∨
        (⌜err ≠ GoInterface.nil ∧ (¬ FsNoErr ∨ tmo ≠ W64 0)⌝ ∗ osFd fd (DFrac.own 1) d)) }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [ExtSemantics fsExt] [FsSemOk] [hos : HasExt fsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem flock.wp_proof [syscall.Assumptions]
    (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hFlock : syscall.Flock.spec (GF := GF) (hG := hG))
    (hNow : time.Now.spec (GF := GF) (hG := hG))
    (hSince : time.Since.spec (GF := GF) (hG := hG))
    (hSleep : time.Sleep.spec (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    flock.spec (GF := GF) (hG := hG) := by
  intro db f fd p d dqf ex tmo hd
  obtain ⟨exv, hexv⟩ : ∃ b, ex = b := ⟨ex, rfl⟩
  wp_start as ⟨#Hos, Hf, Hfo, Hfd⟩
  ihave #Hsyspkg : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsyspkg
  ihave #Htime : isPkgInit (PROP := IProp GF) pkg_id.time $$ []
  · iPkgInit
  ihave #Herrs : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors $$ []
  · iPkgInit
  wp_auto
  by_cases htmo : tmo = W64 0
  case' pos =>
    rw [decide_eq_true htmo]
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    try wp_auto
  case' neg =>
    rw [decide_eq_false htmo]
    simp only [Bool.not_false, ↓reduceIte]
    try wp_auto
    wp_apply hNow as %t0 -
    try wp_auto
  all_goals
    ihave Ht : (∃ tt : time.Time, t_ptr ↦ tt : IProp GF) $$ [t]
    · iexists _; iexact t
    icases Ht with ⟨%tt, t⟩
    wp_apply hFd f fd p.path (DFrac.own 1) $$ [Hfo] as Hfo
    · rw [← fileOwn_eq]; iexact Hfo
    try wp_auto
    cases ex
    all_goals
      try wp_auto
      ihave IH : (∃ fl : w64, "%Hreq" ∷ ⌜flockReq fl.toNat = some (some exv, true)⌝ ∗
          "flag" ∷ flag_ptr ↦ fl ∗ "fd" ∷ fd_ptr ↦ fd ∗ "t" ∷ t_ptr ↦ tt ∗
          "timeout" ∷ timeout_ptr ↦ tmo ∗ "Hf" ∷ db.[DB, go!"file"] ↦{dqf} f ∗
          "Hfo" ∷ os.ownFile f fd p.path (DFrac.own 1) ∗ "Hfd" ∷ osFd fd (DFrac.own 1) d ∗
          "res" ∷ «$res0_ptr» ↦ (GoInterface.nil : GoInterface) : IProp GF)
        $$ [flag fd t timeout Hf Hfo Hfd «$res0»]
      · iexists _; simp only [named]; iframe; ipureintro; subst hexv; decide
      wp_for IH
      try rw [decide_eq_true (rfl : (#true : val) = #true)]
      try simp only [_root_.decide_true, ↓reduceIte]
      try rw [if_pos rfl]
      try wp_auto
      wp_apply hFlock fd fl d (some exv) true Hreq (fun _ => hd) $$ [Hfd]
        as %e ⟨%hW, Hout⟩
      · iframe #; iframe; iapply lockTok_none; simp [OsFd.lk, hd]
      unfold lockOut
      icases Hout with ⟨%d', Hfd, Htk, %hd'⟩
      obtain ⟨-, hd0, hde⟩ := hd'
      try wp_auto
      by_cases he : e = 0
      case' pos =>
        subst he
        obtain rfl := hd0 rfl
        simp only [errnoErr, ↓reduceIte]
        try wp_auto
        iapply wp_for_post_return
        wp_auto
        iapply HΦ
        rw [fileOwn_eq]
        subst hexv
        iframe
        isplitr
        · unfold fmtErrorOkOrNil; itrivial
        ileft; iframe; ipureintro; rfl
      obtain rfl := hde (by simp) he
      ihave #HeS : fmtErrorOk (errnoErr e) $$ []
      · iapply hErr e he $$ Hsys
      rw [show errnoErr e = interface.mkOk syscall.Errno.ty #e by unfold errnoErr; simp only [he, ↓reduceIte]]
      try wp_auto
      by_cases h11 : e = W64 11
      case' neg =>
        rw [decide_eq_false h11]
        simp only [Bool.not_false, ↓reduceIte]
        try wp_auto
        iapply wp_for_post_return
        wp_auto
        iapply HΦ
        rw [fileOwn_eq]
        iframe
        isplitr
        · iapply fmtErrorOkOrNil_of $$ HeS
        iright; iframe; ipureintro
        refine ⟨(fun h => nomatch h), Or.inl ?_⟩
        rcases hW with h | h | h
        · exact absurd h he
        · exact absurd h.2.2 h11
        · exact fun hf => h (FsNoErr.on hf)
      subst h11
      rw [decide_eq_true (rfl : W64 11 = W64 11)]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      try wp_auto
      by_cases htmo' : tmo = W64 0
      case' pos =>
        rw [decide_eq_true htmo']
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        try wp_auto
      case' neg =>
        rw [decide_eq_false htmo']
        simp only [Bool.not_false, ↓reduceIte]
        try wp_auto
        wp_apply hSince as %dd -
        try wp_auto
        by_cases hgt : sint.Z (tmo - W64 50000000) < sint.Z dd
        case' pos =>
          rw [decide_eq_true hgt]
          ihave #Hei : (go_etcd_io.bbolt.errors.bboltErrorsInit : IProp GF) $$ []
          · iapply isPkgInit_access $$ Herrs
          unfold go_etcd_io.bbolt.errors.bboltErrorsInit go_etcd_io.bbolt.errors.bboltErrorsVars
          icases Hei with ⟨%_, #-, %_, -, -, -, -, -, #Ht, -⟩
          unfold go_etcd_io.bbolt.errors.bboltErrVar
          icases Ht with ⟨%ev, #Hev, %-, #Hfe⟩
          try wp_auto
          iapply wp_for_post_return
          wp_auto
          iapply HΦ
          rw [fileOwn_eq]
          iframe
          isplitr
          · iapply fmtErrorOkOrNil_of $$ Hfe
          iright; iframe; ipureintro; exact ⟨(fun h => nomatch h), Or.inr htmo'⟩
        rw [decide_eq_false hgt]
        try wp_auto
      all_goals
        wp_apply hSleep
        try wp_auto
        wp_for_post
        iframe
        iexists fl
        simp only [named]
        iframe
        ipureintro; assumption

end proof

end bbolt
end EtcdGrove
end Perennial
