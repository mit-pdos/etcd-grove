/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/createNewWALFile.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk]
  [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.wp_proofLocked
    (wp_LockFile : go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specLocked (GF := GF) (hG := hG) := by
  intro path forceNew P X A C hopen
  wp_start as ⟨#Hinv, #Hpkg, HP⟩
  wp_auto
  cases forceNew
  · wp_auto
    rw [show W64 1 ||| W64 64 = wal.walOpenFlag false from rfl]
    wp_apply wp_LockFile path _ (W32 384) P X A C hopen $$ [HP] as %lf %err H
    · iframe; isplitl []
      · iexact Hinv
      · solve_pkg_init
    cases err with
    | nil =>
      wp_auto
      iapply HΦ $$ H
    | ok e =>
      unfold fileutil.lockPost
      icases H with ⟨%x, (⟨%h, -⟩ | ⟨%h, HA⟩)⟩
      · cases h
      obtain ⟨-, rfl⟩ := h
      wp_auto
      iapply HΦ
      iexists x
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexact HA
  · wp_auto
    rw [show (W64 1 ||| W64 64) ||| W64 512 = wal.walOpenFlag true from rfl]
    wp_apply wp_LockFile path _ (W32 384) P X A C hopen $$ [HP] as %lf %err H
    · iframe; isplitl []
      · iexact Hinv
      · solve_pkg_init
    cases err with
    | nil =>
      wp_auto
      iapply HΦ $$ H
    | ok e =>
      unfold fileutil.lockPost
      icases H with ⟨%x, (⟨%h, -⟩ | ⟨%h, HA⟩)⟩
      · cases h
      obtain ⟨-, rfl⟩ := h
      wp_auto
      iapply HΦ
      iexists x
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iexact HA

theorem go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.wp_proofFile :
    go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.specFile (GF := GF) (hG := hG) := by
  intro path forceNew P X A C hopen
  wp_start as HP
  wp_auto
  cases forceNew
  · wp_auto
    rw [show W64 1 ||| W64 64 = wal.walOpenFlag false from rfl]
    unfold fileutil.OpenTriple at hopen
    wp_apply hopen $$ HP as %f %err H
    cases err with
    | nil =>
      wp_auto
      iapply HΦ $$ H
    | ok e =>
      unfold fileutil.openPost
      icases H with ⟨%x, (⟨%h, -⟩ | ⟨%h, HA, #Herr⟩)⟩
      · cases h
      obtain ⟨-, rfl⟩ := h
      wp_auto
      iapply HΦ
      iexists x
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iframe
      iexact Herr
  · wp_auto
    rw [show (W64 1 ||| W64 64) ||| W64 512 = wal.walOpenFlag true from rfl]
    unfold fileutil.OpenTriple at hopen
    wp_apply hopen $$ HP as %f %err H
    cases err with
    | nil =>
      wp_auto
      iapply HΦ $$ H
    | ok e =>
      unfold fileutil.openPost
      icases H with ⟨%x, (⟨%h, -⟩ | ⟨%h, HA, #Herr⟩)⟩
      · cases h
      obtain ⟨-, rfl⟩ := h
      wp_auto
      iapply HΦ
      iexists x
      iright
      isplitr
      · ipureintro; exact ⟨(fun h => by cases h), rfl⟩
      iframe
      iexact Herr

theorem go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.wp_proof
    (wp_LockFile : go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.spec (GF := GF) (hG := hG) :=
  ⟨go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.wp_proofLocked wp_LockFile,
    go_etcd_io.etcd.server.v3.storage.wal.createNewWALFile.wp_proofFile⟩

end proof

end EtcdGrove
end Perennial
