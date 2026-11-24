/-
`(*WAL).encodeState` over the tail's `encode` (`encode.specTail`) and a law of `P` (`WalPbIn.MarshalHsLaw`: `MustMarshalMessage` of a hard state, `WAL__cutPre.lean`'s).
Proved over the callees' specs (the next record's guard and split: `SaveNext.lean`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__encodeState
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.encoder__encodeTail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__cutPre
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveNext
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.StreamBound
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SaveHandle

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [ioutil_sem : go_etcd_io.etcd.pkg.v3.ioutil.Assumptions]

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.wp_proof (P : WalPbIn GF) (Mr : WalMarshal)
    (wp_encode : go_etcd_io.etcd.server.v3.storage.wal.encoder.encode.specTail (W := W) Mr)
    (wp_marshal : WalPbIn.MarshalHsLaw P Mr) :
    go_etcd_io.etcd.server.v3.storage.wal.WAL.encodeState.spec (W := W) P Mr := by
  intro R jr r w dir h hp hs hrest hx hidx1
  wp_start as ⟨#Harea, Hh, #Hhs, %Hhp⟩
  icases WalFs.walHandleIn_pkgInit P Mr w dir h TailMetaW $$ Hh with ⟨Hh, #Hwpk0⟩
  ihave %hencS := walAreaOk_encState walCodec Mr R jr r $$ Harea
  iunfold walHandleIn at Hh
  icases Hh with ⟨%lg, %df, %sp, %e, %fp, %lt, %f, %mds, %locks, %lfs, %fd, %dfd, %name, %dnm, %j,
    %rc, Hlg, #Hzap, Hdir, Hdf, Hdff, Hmd, #Hmds, Hsp, #Hst, Hdec, Hrc, Hns, #Hmu, Henti, Hsnapi,
    He, %Hen, Henc, Htw, Hdh, Hlocks, Hls, Hcap, %Hlt, Hlks, #Hltf, Hfp, Hpipe, #Henv, #Hcrc, #Hwpk, Hopen, %Hpure⟩
  obtain ⟨hsplit, hfd, hoff, hsz, hidx, hidx2⟩ := Hpure
  try wp_auto
  wp_apply (wp_marshal hp hs hne -- BLOCKED (P6 hard stop, notes/wal-p6-handoff.md): `hs` may be empty here; needs `MarshalPb.spec` to give a non-nil empty slice) $$ [] as %d ⟨Hd, %Hdn⟩
  · iexact Hhs
  imod ownSlice_persist $$ Hd with #Hd
  unfold go_etcd_io.etcd.server.v3.storage.wal.StateType
  try wp_auto
  imod (typedPointsto_dfractional _ _).dfractional_persist (DFrac.own 1) $$ «$v0» with #Ht
  have hguard := WalHS.next_guard Mr h hsplit hrest stateType (Mr.encState hs) hx
  have hrs : recSize (recOf ⟨stateType, hash.crc32.crc32c (h.crc Mr) (Mr.encState hs),
      Mr.encState hs⟩) < 2 ^ 47 := by
    have h1 := recSize_tight stateType (hash.crc32.crc32c (h.crc Mr) (Mr.encState hs))
      (Mr.encState hs) (by decide) (by have := hencS hs; omega)
    have := hencS hs; omega
  wp_apply (wp_encode R jr r e f fd name dir h.γ h.ino h.H h.md h.cuts h.o0 h.sz h.out h.pend
      (h.crc Mr) «$r0_ptr» stateType (Mr.encState hs) hrs hguard hoff hsz) $$ [Henc Htw «$r0»]
      as %err ⟨%pend', Henc, -, Hr⟩
  · iframe Harea Henv Henc Htw
    iunfold encRecIn
    iexists _
    iframe «$r0»
    have hd : (recOf ⟨stateType, 0#32, Mr.encState hs⟩).data = some (Mr.encState hs) := by
      simp [recOf, stateType, crcType]
    simp only [hd, recBytes]
    have hst : stateType = W64 3 := rfl
    rw [hst]
    isplitl
    · iexact Ht
    isplitr
    · isplitr
      · ipureintro; exact Hdn
      · iexact Hd
    · ipureintro; trivial
  icases Hr with (⟨%out', %sz', %Hok, Htw⟩ | %Herr)
  · obtain ⟨Herr, hsp, hoff', hsz'⟩ := Hok
    subst Herr
    try wp_auto
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    iexists out', pend', sz'
    obtain ⟨hsplit', hcrc'⟩ := WalHS.split_next Mr h
      { h with rest := h.rest - 1, out := out', pend := pend', st := hs, sz := sz' } hsplit hrest
      stateType (Mr.encState hs) hx rfl rfl rfl rfl rfl hsp
    iunfold walHandleIn
    iexists lg, df, hp, e, fp, lt, f, mds, locks, lfs, fd, dfd, name, dnm, j, rc
    rw [hcrc']
    simp only
    iframe Hlg Hzap Hdir Hdf Hdff Hmd Hmds Hhs Hdec Hrc Hns Hmu Henti Hsnapi He Henc Htw Hdh
      Hlocks Hls Hcap Hlks Hltf Hfp Hpipe Henv Hcrc Hwpk Hopen
    isplitl [Hsp]
    · iexact Hsp
    ipureintro
    refine ⟨Hen, Hlt, hsplit', hfd, hoff', hsz', ⟨fun h0 => hidx1 (by omega), hidx.2⟩, hidx2⟩
  · try wp_auto
    iapply HΦ
    iright
    ipureintro; exact Herr

end proof

end EtcdGrove
end Perennial
