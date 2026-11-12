/-
`flock(db, exclusive, timeout)` (U11f, `bolt_unix.go`): `syscall.Flock` on the file's descriptor
with `LOCK_NB`, retried (after `time.Sleep`) while it returns `EWOULDBLOCK` until `timeout` (if
any) passes. OsFs's `Flock` is a no-op returning any errno (`Spec/syscall/Flock.lean`), so the spec
is partial: the file is untouched, and an error is one `fmt` formats (an `Errno`, or
`ErrTimeout`). An internal spec of this unit (only `Open` calls `flock`).
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

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **`flock(db, exclusive, timeout)`**: the file and its descriptor are given back; an error is
one `fmt` formats (`fmtErrorOkOrNil`). -/
abbrev flock.spec : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : GoString) (d : OsFd) (dqf : DFrac) (ex : Bool)
    (tmo : time.Duration),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p (DFrac.own 1) ∗ osFd fd (DFrac.own 1) d }}
    (App (App (App (Val #(functions flock [])) (Val #db)) (Val #ex)) (Val #tmo))
  {{ (err : GoInterface), RET #err; db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p (DFrac.own 1) ∗
      osFd fd (DFrac.own 1) d ∗ fmtErrorOkOrNil err }}

end spec

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
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
  intro db f fd p d dqf ex tmo
  wp_start as ⟨#Hos, Hf, Hfo, Hfd⟩
  ihave #Hsys : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
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
    wp_apply hFd f fd p (DFrac.own 1) $$ [Hfo] as Hfo
    · rw [← fileOwn_eq]; iexact Hfo
    try wp_auto
    cases ex
    all_goals
      try wp_auto
      ihave IH : (∃ fl : w64, "flag" ∷ flag_ptr ↦ fl ∗ "fd" ∷ fd_ptr ↦ fd ∗ "t" ∷ t_ptr ↦ tt ∗
          "timeout" ∷ timeout_ptr ↦ tmo ∗ "Hf" ∷ db.[DB, go!"file"] ↦{dqf} f ∗
          "Hfo" ∷ os.ownFile f fd p (DFrac.own 1) ∗ "Hfd" ∷ osFd fd (DFrac.own 1) d ∗
          "res" ∷ «$res0_ptr» ↦ (GoInterface.nil : GoInterface) : IProp GF)
        $$ [flag fd t timeout Hf Hfo Hfd «$res0»]
      · iexists _; simp only [named]; iframe
      wp_for IH
      try rw [decide_eq_true (rfl : (#true : val) = #true)]
      try simp only [_root_.decide_true, ↓reduceIte]
      try rw [if_pos rfl]
      try wp_auto
      wp_apply hFlock fd fl (DFrac.own 1) d $$ [Hfd] as %e Hfd
      · iframe #; iframe
      try wp_auto
      by_cases he : e = 0
      case' pos =>
        subst he
        simp only [errnoErr, ↓reduceIte]
        try wp_auto
        iapply wp_for_post_return
        wp_auto
        iapply HΦ
        rw [fileOwn_eq]
        iframe
        unfold fmtErrorOkOrNil; itrivial
      ihave #HeS : fmtErrorOk (errnoErr e) $$ []
      · iapply hErr e he
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
        iapply fmtErrorOkOrNil_of $$ HeS
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
          iapply fmtErrorOkOrNil_of $$ Hfe
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

end proof

end bbolt
end EtcdGrove
end Perennial
