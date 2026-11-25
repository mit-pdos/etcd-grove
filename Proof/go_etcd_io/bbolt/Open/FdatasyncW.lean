/-
`fdatasync(db)` whose error witnesses that **the file system can fail** (session S3f of
`notes/bbolt-integration-plan.md`): `fdatasync.spec` with `⌜¬ FsNoErr⌝` in its error arm, over
`syscall.Fdatasync.specB` (its error arm carries the witness). An internal spec of `Open`'s (its sync after `loadFreelist`, and
`DB.init`'s), so that `Open`'s proof, generic in the environment's errors, refutes the error under
the premises (`Open_sharedNoErr`).

`fdatasync.specS` is the variant with the file's bytes (`syscall.Fdatasync.spec`'s), for `Open`'s
sync before the mapping (bbolt `2f6fcff`), where `Open` holds the whole file: on success the
`OsMeta` is `m.synced` (its `cut` unchanged) and every byte durable (`durB`); on failure both come
back unchanged.
-/
module

public import Spec.go_etcd_io.bbolt.fdatasync
public import Spec.syscall.Fdatasync
public import Spec.os.File__Fd
public import Proof.go_etcd_io.bbolt.Mmap.Infra

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

/-- **`fdatasync(db)`**, an error witnessing `¬ FsNoErr` (see the file header). -/
abbrev fdatasync.specW : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (i : Ino) (m : OsMeta) (dqf dq : DFrac),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗ osFd fd dq (dbFd i) ∗
      osMeta i (DFrac.own 1) m }}
    (App (Val #(functions fdatasync [])) (Val #db))
  {{ (err : GoInterface), RET #err; db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗
      osFd fd dq (dbFd i) ∗
      (∃ m' : OsMeta, osMeta i (DFrac.own 1) m' ∗ ⌜m'.size = m.size ∧ m'.maps = m.maps⌝) ∗
      (⌜err = interface.nil⌝ ∨ ⌜err ≠ interface.nil ∧ ¬ FsNoErr⌝ ∗ fmtErrorOk err) }}

theorem fdatasync.wp_proofW (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSync : syscall.Fdatasync.specB (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    fdatasync.specW (GF := GF) (hG := hG) := by
  intro db f fd p i m dqf dq
  wp_start as ⟨#Hos, Hf, Hfo, Hfd, Hm⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply hSync fd dq (dbFd i) m $$ [Hfd Hm] as %e ⟨Hfd, Hr⟩
  · iframe; iframe #
  ihave Hfo : fileOwn f fd p.path dq $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  icases Hr with (⟨%he, %c, Hm⟩ | ⟨%he, Hm⟩)
  · subst he
    iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [Hm]
    · iexists m.bsynced c; iframe; ipureintro; exact ⟨rfl, rfl⟩
    · ileft; ipureintro; simp [errnoErr]
  · iapply HΦ
    iframe Hf Hfd Hfo
    isplitl [Hm]
    · iexists _; iframe; ipureintro; exact ⟨rfl, rfl⟩
    · iright
      isplitr
      · ipureintro
        refine ⟨?_, he.2.2⟩
        simp only [errnoErr, he.1, ↓reduceIte]; exact fun h => nomatch h
      · iapply hErr e he.1 $$ Hsys

/-- **`fdatasync(db)` with the file's bytes `xs` from offset 0**, which hold every byte that may not
be durable (see the file header). -/
abbrev fdatasync.specS : Prop :=
  ∀ (db f : Loc) (fd : w64) (p : BFile) (i : Ino) (m : OsMeta) (xs : List ByteG) (dqf dq : DFrac),
  m.Covers 0 xs.length →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗ osInv (GF := GF) ∗
      db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗ osFd fd dq (dbFd i) ∗
      osMeta i (DFrac.own 1) m ∗ osBytes i 0 (DFrac.own 1) xs }}
    (App (Val #(functions fdatasync [])) (Val #db))
  {{ (err : GoInterface), RET #err; db.[DB, go!"file"] ↦{dqf} f ∗ fileOwn f fd p.path dq ∗
      osFd fd dq (dbFd i) ∗
      ((⌜err = interface.nil⌝ ∗ osMeta i (DFrac.own 1) m.synced ∗
          osBytes i 0 (DFrac.own 1) (xs.map (fun x => durB x.1))) ∨
       (⌜err ≠ interface.nil ∧ ¬ FsNoErr⌝ ∗ fmtErrorOk err ∗ osMeta i (DFrac.own 1) m ∗
          osBytes i 0 (DFrac.own 1) xs)) }}

theorem fdatasync.wp_proofS (hFd : os.File.Fd.spec (GF := GF) (hG := hG))
    (hSync : syscall.Fdatasync.spec (GF := GF) (hG := hG))
    (hErr : errnoErrOk (GF := GF) (hG := hG)) :
    fdatasync.specS (GF := GF) (hG := hG) := by
  intro db f fd p i m xs dqf dq hcov
  wp_start as ⟨#Hos, Hf, Hfo, Hfd, Hm, Hxs⟩
  ihave #Hsys0 : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ []
  · iPkgInit
  ihave #Hsys := syscall.errnoOk_of_isPkgInit $$ Hsys0
  wp_auto
  wp_apply hFd f fd p.path dq $$ [Hfo] as Hfo
  · rw [← fileOwn_eq]; iexact Hfo
  try wp_auto
  wp_apply hSync fd dq (dbFd i) m 0 xs hcov $$ [Hfd Hm Hxs] as %e ⟨Hfd, Hr⟩
  · iframe Hfd Hm Hxs; iframe #
  ihave Hfo : fileOwn f fd p.path dq $$ [Hfo]
  · rw [fileOwn_eq]; iexact Hfo
  icases Hr with (⟨%he, Hm, Hxs⟩ | ⟨%he, Hm, Hxs⟩)
  · subst he
    iapply HΦ
    iframe Hf Hfd Hfo
    ileft
    iframe Hm Hxs
    ipureintro; simp [errnoErr]
  · iapply HΦ
    iframe Hf Hfd Hfo
    iright
    iframe Hm Hxs
    isplitr
    · ipureintro
      refine ⟨?_, fun h => he.2.2 h.on⟩
      simp only [errnoErr, he.1, ↓reduceIte]; exact fun h => nomatch h
    · iapply hErr e he.1 $$ Hsys

end spec

end bbolt
end EtcdGrove
end Perennial
