/-
Proof of `Spec/go_etcd_io/etcd/server/v3/etcdserver/newSnapshotReaderCloser.lean`. Lean-first (no
Rocq counterpart); D22 S-h, 2026-10-20.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.newSnapshotReaderCloser
public import Spec.io.Pipe
public import Spec.io.PipeWriter__CloseWithError
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__WriteTo
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Close
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.defragmentedSnapshot__WriteTo
public import Spec.go_etcd_io.etcd.server.v3.storage.backend.defragmentedSnapshot__Close
public import Spec.go_uber_org.zap.Int64
public import Spec.go_uber_org.zap.String
public import Spec.go_uber_org.zap.Error
public import Spec.go_uber_org.zap.Logger__Info
public import Spec.go_uber_org.zap.Logger__Warn
public import Spec.github_com.dustin.go_humanize.Bytes

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A log line's field slice (`wp_slice_literal`). -/
local macro "zap_fields" : tactic => `(tactic| (
  wp_apply wp_slice_literal
  isplitr
  · ipureintro; rfl
  iintro %fsl ⟨-, -⟩
  (try wp_auto)))

theorem newSnapshotReaderCloser.wp_proof
    (hPipe : io.Pipe.spec (GF := GF) (hG := hG))
    (hWT : backend.snapshot.WriteTo.spec (GF := GF) (hG := hG))
    (hI64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hCWE : io.PipeWriter.CloseWithError.spec (GF := GF) (hG := hG))
    (hCl : backend.snapshot.Close.spec (GF := GF) (hG := hG)) :
    newSnapshotReaderCloser.spec (GF := GF) (hG := hG) := by
  intro lg sp D γ
  wp_start as ⟨%Hlg, Hsn⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Phum : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
  · iPkgInit
  wp_auto
  wp_apply hPipe (fun bs => backend.boltImage bs D) (backend.snapOpenQ sp D γ (1 : Qp).half)
    as %pr %pw ⟨#Hwok, Hpw, Hrs⟩
  (try wp_auto)
  wp_apply wp_fork $$ [Hsn Hpw snapshot lg pw]
  · -- the goroutine: `snapshot.WriteTo(pw)`, the log line, `pw.CloseWithError(err)` (which hands
    -- it the sender's half), `snapshot.Close()` (nil: no panic)
    wp_auto
    wp_apply hWT sp D γ _ _ _ false [] $$ [Hsn Hwok Hpw] as %n %err ⟨%bs, Hsn, Hpw, %Himg⟩
    · iframe #; iframe
    (try wp_auto)
    rcases err with ei | _
    · -- `WriteTo` failed: the warning, the pipe closed with the error
      (try wp_auto)
      wp_apply hHB as %_ -
      wp_apply hStr as %_ -
      wp_apply hErr as %_ -
      (try wp_auto)
      zap_fields
      wp_apply hWarn _ _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      (try wp_auto)
      wp_apply hCWE pw _ _ true ([] ++ bs) (GoInterface.ok ei) $$ [Hpw] as Hhalf
      · iframe Hpw; ipureintro; intro h; cases h
      (try wp_auto)
      ihave Hfull := (backend.snapOpenQ_half sp D γ 1).2 $$ [Hsn Hhalf]
      · iframe Hsn Hhalf
      wp_apply hCl sp D γ $$ [Hfull]
      · iframe #; iframe Hfull
      (try wp_auto)
      ipureintro; exact isPanic_intoVal ()
    · -- `WriteTo` succeeded: the bytes an image of `D`, the pipe closed with nil
      (try wp_auto)
      wp_apply hI64 as %_ -
      wp_apply hHB as %_ -
      wp_apply hStr as %_ -
      (try wp_auto)
      zap_fields
      wp_apply hInfo _ _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      (try wp_auto)
      wp_apply hCWE pw _ _ true ([] ++ bs) GoInterface.nil $$ [Hpw] as Hhalf
      · iframe Hpw; ipureintro; intro _; simpa using Himg rfl
      (try wp_auto)
      ihave Hfull := (backend.snapOpenQ_half sp D γ 1).2 $$ [Hsn Hhalf]
      · iframe Hsn Hhalf
      wp_apply hCl sp D γ $$ [Hfull]
      · iframe #; iframe Hfull
      (try wp_auto)
      ipureintro; exact isPanic_intoVal ()
  · (try wp_auto)
    iapply HΦ
    iexact Hrs

theorem newSnapshotReaderCloser_defrag.wp_proof
    (hPipe : io.Pipe.spec (GF := GF) (hG := hG))
    (hWT : backend.defragmentedSnapshot.WriteTo.spec (GF := GF) (hG := hG))
    (hI64 : zap.Int64.spec (GF := GF) (hG := hG))
    (hHB : go_humanize.Bytes.spec (GF := GF) (hG := hG))
    (hStr : zap.String.spec (GF := GF) (hG := hG))
    (hInfo : zap.Logger.Info.spec (GF := GF) (hG := hG))
    (hErr : zap.Error.spec (GF := GF) (hG := hG))
    (hWarn : zap.Logger.Warn.spec (GF := GF) (hG := hG))
    (hCWE : io.PipeWriter.CloseWithError.spec (GF := GF) (hG := hG))
    (hCl : backend.defragmentedSnapshot.Close.spec (GF := GF) (hG := hG)) :
    newSnapshotReaderCloser_defrag.spec (GF := GF) (hG := hG) := by
  intro lg ds D γ
  wp_start as ⟨%Hlg, Hsn⟩
  ihave #Pbe : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.backend $$ []
  · iPkgInit
  ihave #Pzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave #Phum : isPkgInit (PROP := IProp GF) pkg_id.github_com.dustin.go_humanize $$ []
  · iPkgInit
  wp_auto
  wp_apply hPipe (fun bs => backend.boltImage bs D) (backend.defragSnapOpenQ ds D γ (1 : Qp).half)
    as %pr %pw ⟨#Hwok, Hpw, Hrs⟩
  (try wp_auto)
  wp_apply wp_fork $$ [Hsn Hpw snapshot lg pw]
  · wp_auto
    wp_apply hWT ds D γ _ _ _ false [] $$ [Hsn Hwok Hpw] as %n %err ⟨%bs, Hsn, Hpw, %Himg⟩
    · iframe #; iframe
    (try wp_auto)
    rcases err with ei | _
    · (try wp_auto)
      wp_apply hHB as %_ -
      wp_apply hStr as %_ -
      wp_apply hErr as %_ -
      (try wp_auto)
      zap_fields
      wp_apply hWarn _ _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      (try wp_auto)
      wp_apply hCWE pw _ _ true ([] ++ bs) (GoInterface.ok ei) $$ [Hpw] as Hhalf
      · iframe Hpw; ipureintro; intro h; cases h
      (try wp_auto)
      ihave Hfull := (backend.defragSnapOpenQ_half ds D γ 1).2 $$ [Hsn Hhalf]
      · iframe Hsn Hhalf
      wp_apply hCl ds D γ $$ [Hfull]
      · iframe #; iframe Hfull
      (try wp_auto)
      ipureintro; exact isPanic_intoVal ()
    · (try wp_auto)
      wp_apply hI64 as %_ -
      wp_apply hHB as %_ -
      wp_apply hStr as %_ -
      (try wp_auto)
      zap_fields
      wp_apply hInfo _ _ _ $$ []
      · iframe #; ipureintro; exact Hlg
      (try wp_auto)
      wp_apply hCWE pw _ _ true ([] ++ bs) GoInterface.nil $$ [Hpw] as Hhalf
      · iframe Hpw; ipureintro; intro _; simpa using Himg rfl
      (try wp_auto)
      ihave Hfull := (backend.defragSnapOpenQ_half ds D γ 1).2 $$ [Hsn Hhalf]
      · iframe Hsn Hhalf
      wp_apply hCl ds D γ $$ [Hfull]
      · iframe #; iframe Hfull
      (try wp_auto)
      ipureintro; exact isPanic_intoVal ()
  · (try wp_auto)
    iapply HΦ
    iexact Hrs

end proof

end EtcdGrove
end Perennial
