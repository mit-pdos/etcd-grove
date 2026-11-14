/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/openLast.lean` (W7 of
`notes/wal-fsext-plan.md`; the W7-W12 log, eighth session): the update commits and the WAL's last
segment is pinned at the first step (`walInv_openLast`, law L1); no WAL: `readWALNames` of the missing
directory fails (`specAbsent`); else a path to the WAL directory (`walInv_dirPath`), `readWALNames`
over the directory claim's half (its names are the segments', `walNamesOut_segs`), the last name joined
(`filepath.Join`), `fileutil.LockFile` read-write over `walOpen_triple`; an error puts the pin back at the
next step (`walInv_unpinLast`). Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openLast
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNames
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNamesAbsent
public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile
public import LinuxFs.Spec.path.filepath.Join
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPin

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
variable [os_sem : os.Assumptions]

/-- The last of the names is the last segment's. -/
theorem names_last {ws : List GoString} {segs : List SegG} {gL : SegG}
    (hws : ws = segs.map (·.name)) (hgL : segs.getLast? = some gL) :
    ws[ws.length - 1]? = some gL.name := by
  subst hws
  obtain ⟨l, rfl⟩ := List.getLast?_eq_some_iff.1 hgL
  simp

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.openLast.wp_proof [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] (Mr : WalMarshal)
    (wp_names : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.spec (GF := GF) (hG := hG))
    (wp_namesAbs : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.specAbsent (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_Lock : go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.openLast.spec (W := W) Mr := by
  intro lg R jr r dir nm qp Q hin hnmO hr hdl
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb⟩
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %hok, Hcl⟩
  ihave %hrc := osPathS_cleanAbs' R r _ jr $$ Hp
  have hnm := hin.1
  have hdc := dir_child hin
  try wp_auto
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_openLast walCodec Mr R jr r dir nm N _ h Wn Q hin (hok.1 nm hnm)
    $$ Hinv Hsi Hnc Hu Hau HN Hsf with ⟨Hnc, HN, Hsf, %o, HQ, Hcase⟩
  icases Hcase with (⟨⟨%ho, %hNnm, %hcn⟩, Hu⟩ | ⟨%ho, %d, Hpin⟩)
  · -- no WAL: `readWALNames` fails on the missing directory
    subst ho
    imodintro
    iframe Hnc
    subst hdc
    wp_apply wp_namesAbs lg r nm R jr (DFrac.own qp) 1 N (DFrac.own (1 : Qp).half) h hnmO hNnm hcn
      $$ [Hp Hperm HN] as %rr %err ⟨Hp, Hperm, HN, %e, %herr, #He⟩
    · iframe; iframe #
    subst herr
    try wp_auto
    iapply HΦ
    iframe Hp Hperm
    isplitl [HN Hsf Hcl]
    · iapply walAreaRes_close jr N h cl Wn hok; iframe
    iexists none
    iframe HQ
    ileft
    iframe Hu
    ipureintro; nofun
  · iunfold walPinLast at Hpin
    icases Hpin with ⟨%lay, %X, %hj, %gL, %hfacts, #Hkey, Hl, Htf, Ho, HS, Hj⟩
    obtain ⟨hljr, hX, hcoh, habs, hidle, hnd, hsn, hgL⟩ := hfacts
    icases Htf with ⟨Htf, Hnf⟩
    imod walInv_dirPath walCodec Mr R jr r dir lay.j X $$ Hinv Hnc Hnf Hkey with ⟨Hnc, Hnf, %qd, Hpd⟩
    imodintro
    iframe Hnc
    have hgLm : gL ∈ lay.segs := List.mem_of_getLast? hgL
    have hSz : gL.om.size = gL.bs.length := (habs.metas gL hgLm).1
    have hnmf := walLay_nameFmt habs
    try wp_auto
    wp_apply wp_names lg dir R lay.j (DFrac.own qd) 1 (.except X) (DFrac.own (1 : Qp).half) hj
      $$ [Hpd Hperm Hj] as %rr %err ⟨Hpd, Hperm, Hj, Hnames⟩
    · iframe; iframe #
    icases Hnames with (⟨%ws, ⟨%herr, %hout⟩, Hws⟩ | ⟨%e, %herr, #He⟩)
    rotate_left
    · -- `readWALNames` failed: the pin back
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_unpinLast walCodec Mr R jr r dir lay.j X hj gL hSz $$ Hinv Hnc Hl [Htf Hnf] Ho HS Hj
        Hkey with ⟨Hnc, Hu⟩
      · iframe
      imodintro
      iframe Hnc
      subst herr
      try wp_auto
      iapply HΦ
      iframe Hp Hperm
      isplitl [HN Hsf Hcl]
      · iapply walAreaRes_close jr N h cl Wn hok; iframe
      iexists o
      iframe HQ
      ileft
      iframe Hu
      ipureintro; nofun
    subst herr
    have hws : ws = lay.segs.map (·.name) :=
      walNamesOut_segs hX hsn habs.names.1 hnd habs.names.2 hnmf hout
    have hlast := names_last hws hgL
    have hwsl : 0 < ws.length := by
      rw [hws, List.length_map]; exact List.length_pos_of_mem hgLm
    have hbok : NameOk gL.name :=
      (hout.2.2.1 gL.name (List.mem_of_getElem? hlast)).1
    have hbN : (NameSet.except X).Mem gL.name := fun hbX => by
      have := hX _ hbX; rw [(hsn.1 gL hgLm).1] at this; cases this
    have hbi : hj.cur !! gL.name = some (.file gL.ino) := (hsn.1 gL hgLm).2
    ihave %hcd := osPathS_cleanAbs' R dir _ lay.j $$ Hpd
    ihave %Hll := ownSlice_len _ _ _ $$ Hws
    try wp_auto
    -- `names[len(names)-1]`
    have hidx : 0 ≤ sint.Z (rr.len - W64 1) := by
      have := Hll.2; have h1 : ws.length = sint.nat rr.len := Hll.1; word
    have hidx' : (sint.Z (rr.len - W64 1)).toNat = ws.length - 1 := by
      have := Hll.2; have h1 : ws.length = sint.nat rr.len := Hll.1; word
    have hkb : 0 ≤ sint.Z (rr.len - W64 1) ∧ sint.Z (rr.len - W64 1) < sint.Z rr.len := by
      have := Hll.2; have h1 : ws.length = sint.nat rr.len := Hll.1; constructor <;> word
    rw [ite_eq_left_of_eq_true _ _ (eq_true hkb)]
    wp_apply wp_load_slice_index rr (sint.Z (rr.len - W64 1)) ws (DFrac.own 1) gL.name hidx $$ [Hws]
      as Hws
    · iframe; ipureintro; rw [hidx']; exact hlast
    try wp_auto
    wp_apply wp_slice_literal (V := GoString) [dir, gL.name]
    isplitr
    · ipureintro; rfl
    iintro %jsl ⟨Hjsl, -⟩
    try wp_auto
    obtain ⟨sq, ix, hgn⟩ := hnmf gL hgLm
    have hjl : ([dir, gL.name].map List.length).sum + 2 < 2 ^ 62 := by
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hgn, walFileName_length]
      omega
    wp_apply wp_Join _ _ _ hjl $$ [$Hjsl] as %fpath ⟨%hfpath, -⟩
    rw [join_child hcd hbok] at hfpath
    subst hfpath
    try wp_auto
    ihave #Hfu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
    · iPkgInit
    wp_apply +noauto wp_Lock (child dir gL.name) (W64 2) (W32 384) _ Unit _ _
        (walOpen_triple R dir gL.name (DFrac.own qd) lay.j gL.ino (.except X) (DFrac.own (1 : Qp).half)
          hj 1 (W64 2) (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide)
          hbok hbN hbi)
      $$ [Hpd Hj Hperm] as %lf %err Hpost
    · iframe; iframe #
    iunfold fileutil.lockPost at Hpost
    icases Hpost with ⟨%u, Hpost⟩
    icases Hpost with (⟨%herr, ⟨Hpd, Hj, Hperm⟩, %f, %fd, %i, ⟨%hfd, %hi⟩, #Hlf, Hf, Hoff, Hfd⟩ |
      ⟨⟨%herr, %hlf⟩, %bb, Hpd, Hj, Hperm⟩)
    · subst hi herr
      try wp_auto
      iapply HΦ
      iframe Hp Hperm
      isplitl [HN Hsf Hcl]
      · iapply walAreaRes_close jr N h cl Wn hok; iframe
      iexists o
      iframe HQ
      iright
      isplitr
      · ipureintro; exact ⟨rfl, ho⟩
      iunfold walLastOpen
      iexists d, lay, X, hj, gL, f, fd, qd
      iframe
      iframe #
      ipureintro; exact ⟨hljr, hX, hcoh, habs, hidle, hnd, hsn, hgL, hfd⟩
    · -- the lock's open failed: the pin back
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_unpinLast walCodec Mr R jr r dir lay.j X hj gL hSz $$ Hinv Hnc Hl [Htf Hnf] Ho HS Hj
        Hkey with ⟨Hnc, Hu⟩
      · iframe
      imodintro
      iframe Hnc
      try wp_auto
      iapply HΦ
      iframe Hp Hperm
      isplitl [HN Hsf Hcl]
      · iapply walAreaRes_close jr N h cl Wn hok; iframe
      iexists o
      iframe HQ
      ileft
      iframe Hu
      ipureintro; exact herr

end proof

end EtcdGrove
end Perennial
