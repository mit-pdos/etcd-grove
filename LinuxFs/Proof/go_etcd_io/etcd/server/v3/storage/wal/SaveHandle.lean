/- Lean-first (no Rocq counterpart).

# What `Save` reads of the handle without unfolding it (W6; `WAL__Save.lean`)

`walHandleIn_lockFacts`: the handle's persistent facts `Save` needs for `w.mu` (the mutex, `sync`'s
package) and the package's segment size (`SegmentSizeBytes`); `walHandleIn_idx`: its pure index
facts (`cut`'s name bound, `saveState`'s premise after the commit: the quiescent handle's
`walLastIdx ≤ max(enti, snapi)`, which the committed handle no longer states).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Handle
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section handle
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- The handle's mutex and the packages `Save` reads (see the file header). -/
theorem walHandleIn_lockFacts (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (h : WalHS) :
    ⊢ walHandleIn (W := W) P Mr w dir h -∗ walHandleIn (W := W) P Mr w dir h ∗
      (sync.isMutex (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" w)
        (BI.pure True : IProp GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.sync ∗
        globalAddr go_etcd_io.etcd.server.v3.storage.wal.SegmentSizeBytes ↦□ (W64 64000000)) := by
  iintro Hh
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  ihave #Henv0 := Henv
  iunfold encEnv at Henv0
  icases Henv0 with ⟨-, -, #Hsync, -, -⟩
  ihave #Hwi : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hwpk
  iunfold wal.walInit at Hwi
  icases Hwi with ⟨-, -, #Hseg, -⟩
  iframe Hmu Hsync Hseg
  iunfold walHandleIn
  iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
    Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
  ipureintro
  exact ⟨Hen, Hlt, Hpure⟩

/-- **The handle's `w.state`**, out and back (any pointer holding the same hard state). -/
theorem walHandleIn_state (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (h : WalHS) :
    ⊢ walHandleIn (W := W) P Mr w dir h -∗ ∃ sp : Loc,
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp ∗ P.hsIn sp h.st ∗
      (∀ sp' : Loc, structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"state" w ↦ sp' -∗
        P.hsIn sp' h.st -∗ walHandleIn (W := W) P Mr w dir h) := by
  iintro Hh
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  iexists sp
  iframe Hsp Hst
  iintro %sp' Hsp' #Hst'
  iunfold walHandleIn
  iexists lg, df, sp', e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
  iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp' Hst' Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
    Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
  ipureintro
  exact ⟨Hen, Hlt, Hpure⟩

/-- **The handle's tail file and its offset** (for `w.tail().Seek(0, SeekCurrent)`), out and back. -/
theorem walHandleIn_seek (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (h : WalHS) :
    ⊢ walHandleIn (W := W) P Mr w dir h -∗ ∃ (locks : GoSlice) (ls : List Loc) (lt f : Loc) (fd : w64)
        (name : GoString),
      structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks ∗
      locks ↦* (ls ++ [lt]) ∗ fileutil.lockedFile lt f ∗ os.ownFile f fd name (DFrac.own 1) ∗
      os.ownOff f (W64 (h.o0 + h.out.length)) ∗
      ⌜0 ≤ fd.toInt ∧ h.o0 + h.out.length ≤ 0xffffffff000⌝ ∗
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"locks" w ↦ locks -∗
        locks ↦* (ls ++ [lt]) -∗ os.ownFile f fd name (DFrac.own 1) -∗
        os.ownOff f (W64 (h.o0 + h.out.length)) -∗ walHandleIn (W := W) P Mr w dir h) := by
  iintro Hh
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  obtain ⟨ls, rfl⟩ := List.getLast?_eq_some_iff.1 Hlt
  iunfold walTailW at Htw
  icases Htw with ⟨Hf, Hfdo, Hoff, Htk, %m, %bs, Hm, Hbs, %hmb, Hv⟩
  iexists locks, ls, lt, f, fd, name
  iframe Hlocks Hls Hltf Hf Hoff
  isplitr
  · ipureintro; exact ⟨hmb.2.2.2, by have := Hpure.2.2.1; have := Hpure.2.2.2.1; omega⟩
  iintro Hlocks Hls Hf Hoff
  ihave Htw : walTailW (W := W) f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out
      $$ [Hf Hfdo Hoff Htk Hm Hbs Hv]
  · iunfold walTailW
    iframe Hf Hfdo Hoff Htk
    iexists m, bs
    iframe Hm Hbs Hv
    ipureintro; exact hmb
  iunfold walHandleIn
  iexists lg, df, sp, e, fp, lt, f, mds, locks, ls ++ [lt], fd, dfd, name, dnm, j, rc
  iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
    Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
  ipureintro
  exact ⟨Hen, Hlt, Hpure⟩

/-- The handle's pure index facts (see the file header). -/
theorem walHandleIn_idx (P : WalPbIn GF) (Mr : WalMarshal) (w : Loc) (dir : GoString)
    (h : WalHS) :
    ⊢ walHandleIn (W := W) P Mr w dir h -∗ walHandleIn (W := W) P Mr w dir h ∗
      ⌜(h.rest = 0 → walLastIdx (h.H.map WalOpG.toM) ≤ max (uint.nat h.enti) (uint.nat h.snapi)) ∧
        walMaxSnapIdx (h.H.map WalOpG.toM) ≤ uint.nat h.snapi⌝ := by
  iintro Hh
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk,
    Hopen, %Hpure⟩
  isplitl
  · iunfold walHandleIn
    iexists lg, df, sp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hsp Hst Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    ipureintro
    exact ⟨Hen, Hlt, Hpure⟩
  · ipureintro
    exact Hpure.2.2.2.2.2.1

end handle

end WalFs
end EtcdGrove
end Perennial

end
