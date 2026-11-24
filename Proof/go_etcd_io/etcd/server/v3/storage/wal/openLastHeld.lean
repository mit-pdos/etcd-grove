/-
The proof of `openLast.specHeld` (`Spec/go_etcd_io/etcd/server/v3/storage/wal/openLast.lean`;
2026-11-15, the lock semantics, `notes/wal-units/locks.md` item 5): `readWALNames` over the held claim's
share (its names are the segments', `walNamesOut_segs`), the last name joined, `fileutil.LockFile`
read-write over `walOpen_triple` at the last segment's inode, whose lock is held: only the error arm of
`lockPost` is possible (`fileutil.lockPost_held`). Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openLast
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNames
public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile
public import Spec.path.filepath.Join
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openWALFilesLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndexLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairPin
public import Proof.go_etcd_io.etcd.client.pkg.v3.fileutil.LockKind

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

/-- See the file header. -/
theorem go_etcd_io.etcd.server.v3.storage.wal.openLast.wp_specHeld [os.file.FieldAssumptions]
    [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (wp_names : go_etcd_io.etcd.server.v3.storage.wal.readWALNames.spec (GF := GF) (hG := hG))
    (wp_Join : filepath.Join.spec (GF := GF) (hG := hG))
    (wp_Lock : go_etcd_io.etcd.client.pkg.v3.fileutil.LockFile.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.openLast.specHeld (GF := GF) (hG := hG) := by
  intro lg R dir j X hj segs gL qd dqn k fd hX hsn hino hnd hsort hnmf hgL hdl
  have hdl' : dir.length < 4096 := hdl.1
  wp_start as ⟨#Hzap, #Hinv, #Hsi, Hpd, Hperm, Hj, Hl, #Hk⟩
  have hgLm : gL ∈ segs := List.mem_of_getLast? hgL
  try wp_auto
  wp_apply wp_names lg dir R j (DFrac.own qd) 1 (.except X) dqn hj
    $$ [Hpd Hperm Hj] as %rr %err ⟨Hpd, Hperm, Hj, Hnames⟩
  · iframe; iframe #
  icases Hnames with (⟨%ws, ⟨%herr, %hout⟩, Hws⟩ | ⟨%e, %herr, #He, -⟩)
  rotate_left
  · -- `readWALNames` failed
    subst herr
    try wp_auto
    iapply HΦ
    iframe
    ipureintro; nofun
  subst herr
  have hws : ws = segs.map (·.name) := walNamesOut_segs hX hsn hino hnd hsort hnmf hout
  have hlast : ws[ws.length - 1]? = some gL.name := by
    subst hws; obtain ⟨l, hl⟩ := List.getLast?_eq_some_iff.1 hgL; rw [hl]; simp
  have hbok : NameOk gL.name := (hout.2.2.1 gL.name (List.mem_of_getElem? hlast)).1
  have hbN : (NameSet.except X).Mem gL.name := fun hbX => by
    have := hX _ hbX; rw [(hsn.1 gL hgLm).1] at this; cases this
  have hbi : hj.cur !! gL.name = some (.file gL.ino) := (hsn.1 gL hgLm).2
  ihave %hcd := osPathS_cleanAbs' R dir _ j $$ Hpd
  ihave %Hll := ownSlice_len _ _ _ $$ Hws
  try wp_auto
  have hidx : 0 ≤ sint.Z (rr.len - W64 1) := by
    have := Hll.2; have h1 : ws.length = sint.nat rr.len := Hll.1
    have : 0 < ws.length := by rw [hws, List.length_map]; exact List.length_pos_of_mem hgLm
    word
  have hidx' : (sint.Z (rr.len - W64 1)).toNat = ws.length - 1 := by
    have := Hll.2; have h1 : ws.length = sint.nat rr.len := Hll.1
    have : 0 < ws.length := by rw [hws, List.length_map]; exact List.length_pos_of_mem hgLm
    word
  have hkb : 0 ≤ sint.Z (rr.len - W64 1) ∧ sint.Z (rr.len - W64 1) < sint.Z rr.len := by
    have := Hll.2; have h1 : ws.length = sint.nat rr.len := Hll.1
    have : 0 < ws.length := by rw [hws, List.length_map]; exact List.length_pos_of_mem hgLm
    constructor <;> word
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
  have hjl : ([dir, gL.name].map List.length).sum + 2 ≤ _root_.Perennial.strings.joinMax := by
    unfold _root_.Perennial.strings.joinMax
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, hgn, walFileName_length]
    omega
  wp_apply wp_Join _ _ _ hjl $$ [$Hjsl] as %fpath ⟨%hfpath, -⟩
  rw [join_child hcd hbok] at hfpath
  subst hfpath
  try wp_auto
  ihave #Hfu : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil $$ []
  · iPkgInit
  wp_apply +noauto wp_Lock (child dir gL.name) (W64 2) (W32 384) _ Unit _ _
      (walOpen_triple R dir gL.name (DFrac.own qd) j gL.ino (.except X) dqn hj 1 (W64 2)
        (by simp only [OpenFlagsOk, O_CREAT, O_TRUNC, O_CLOEXEC]; decide) (by decide)
        hbok hbN hbi) (by decide)
    $$ [Hpd Hj Hperm] as %lf %err Hpost
  · iframe; iframe #; iPkgInit
  ihave Hpost := fileutil.lockPost_of_W _ _ _ _ _ _ _ $$ Hpost
  icases fileutil.lockPost_held (X := Unit)
      (fun _ _ => iprop(osPathS (GF := GF) R dir (DFrac.own qd) j ∗ osNames j (.except X) dqn hj ∗
        osCallPerm (callKey R dir) 1))
      (fun _ i' => i' = gL.ino) _ _ lf err k gL.ino fd (fun _ i' h => h) $$ [Hpost Hl Hk]
    with ⟨⟨%herr, %hlf⟩, ⟨%u, %b, Hpd, Hj, Hperm⟩, Hl⟩
  · iframe; iframe #
  try wp_auto
  iapply HΦ
  iframe
  ipureintro; exact herr

end proof

end EtcdGrove
end Perennial
