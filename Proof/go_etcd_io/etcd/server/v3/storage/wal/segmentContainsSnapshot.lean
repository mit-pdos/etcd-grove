/- Probe a closed segment using its own fresh decoder and close the borrowed file. -/
module
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.segmentContainsSnapshot
public import Spec.google_golang_org.protobuf.proto.UnmarshalPb
public import Proof.google_golang_org.protobuf.proto.CloneWalSnapLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.readWALNames
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__Decode
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__LastCRC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__UpdateCRC
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetType
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__GetCrc
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Record__Validate
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__GetIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.ReadAllCallees
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndexLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VsePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseAttemptPure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseErr
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecTerm
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.DecStreams
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllTail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllInv
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadAllExit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CloseOpeningFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.VseAttemptLemmas

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
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [errs_sem : _root_.Perennial.errors.Assumptions]

private theorem probe_error_streams (d rp : Loc) (IoE : GoInterface → Prop)
    (eof ueof : GoInterface) (fs fsD : List (DecFile GF)) (kD off : Nat) (c : w32) (e : GoInterface)
    (hkD : fsD = fs.drop kD) (he : e ≠ GoInterface.nil) :
    decPostB walCodec d rp IoE eof ueof fsD off c e ∗ ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ⊢
      [∗list] F ∈ fs, ∃ q, F.S q := by
  iintro ⟨Hpb, Hleft⟩
  unfold decPostB
  icases Hpb with (⟨%k, Hk, Hm⟩ | ⟨-, -, -, %k, %off', %c', Hk, Hdec⟩ |
    ⟨%k, %s, %off', %c', -, Hk, Hdec⟩)
  · generalize hgd : goDecode walCodec (fsD.map (·.bs)) off c = gd
    rcases gd with ⟨r, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
    · icases Hm with ⟨%hst, -, -⟩
      exact absurd hst.1 he
    · icases Hm with ⟨-, -, Hdec⟩
      iapply vse_streams d IoE eof fs fsD kD k off' c' _ hkD; iframe
  · iapply vse_streams d IoE eof fs fsD kD k off' c' false hkD; iframe
  · iapply vse_streams d IoE eof fs fsD kD k off' c' false hkD; iframe

theorem wal.segmentContainsSnapshot.wp_proof
 [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
    (U : WalUnmarshal) (hUs : U.SnapCoh)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_IsEof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG))
    (wp_Term : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG))
    (wp_openFiles : go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.spec (GF := GF) (hG := hG))
    (wp_NewDecoder : go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec (GF := GF) (hG := hG))
    (wp_Decode : go_etcd_io.etcd.server.v3.storage.wal.decoder.Decode.spec (GF := GF) (hG := hG))
    (wp_UpdateCRC : go_etcd_io.etcd.server.v3.storage.wal.decoder.UpdateCRC.spec (GF := GF) (hG := hG))
    (wp_GetType : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetType.spec (GF := GF) (hG := hG))
    (wp_GetCrc : go_etcd_io.etcd.server.v3.storage.wal.walpb.Record.GetCrc.spec (GF := GF) (hG := hG))
    (wp_SnapIndex : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_FName : os.fileStat.Name.spec (GF := GF) (hG := hG))
    (wp_Unmarshal : proto.UnmarshalPb.spec (GF := GF) (hG := hG)) :
    wal.segmentContainsSnapshot.spec (GF := GF) U := by
  intro lg R dir j dq qc N dqn hj g index hdir hN hok hname hcur hsize hbelow
  have hdir' : dir.length < 4096 := hdir.1
  wp_start as ⟨#Hzap, #HosI, #Hsi, Hown⟩
  iunfold wal.probeOwn at Hown
  icases Hown with ⟨Hpd, Hperm, Hj, Hg⟩
  wp_auto
  wp_apply wp_with_defer as %defer defer
  (try wp_auto)
  wp_apply wp_slice_literal (V := GoString) [g.name]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  have hzero : sint.nat (W64 0) = 0 := rfl
  wp_apply wp_openFiles lg dir _ [g.name] (DFrac.own 1) (W64 0) false [g.ino] R j dq qc N dqn hj
    (by decide) (by simp [hzero]) rfl hdir ?nm $$ [Hpd Hperm Hj Hsl] as
      %rsl %lsl %cl %err ⟨Hpd, Hperm, Hj, Hsl, Hopened⟩
  case nm =>
    intro m b i hb hi
    cases m with
    | zero => cases hb; cases hi; exact ⟨hN, hok, hname, hcur⟩
    | succ m => simp [hzero] at hb
  · iframe; iframe #
  icases Hopened with (⟨%frs, %lfs, ⟨%he, %hfl, %hll⟩, Hrsl, -, -, -, Hfiles, Hcl⟩ |
    ⟨%ei, %he, -, -⟩)
  rotate_left
  · subst he
    (try wp_auto)
    iapply HΦ
    unfold wal.probeOwn
    iframe; iframe #
  subst he
  iunfold wal.walCloser at Hcl
  icases Hcl with ⟨%hcl, #Hcl⟩
  ihave #Hosp := wal_osInit $$ Hpkg
  ihave ⟨%IoE, %eof, %ueof, #Hde, %hIo⟩ := hEnv $$ Hpkg
  obtain ⟨hIo, hIoN⟩ := hIo
  ihave #Hde' := Hde
  iunfold decEnv at Hde'
  icases Hde' with ⟨-, -, -, -, #Hbufio, #Heof, #Hueof, -, #Hcrc, -, -⟩
  ihave ⟨#Heofa, %hIoEof⟩ := isEofOk_eof IoE eof ueof $$ [Hde]
  · iunfold decEnv at Hde
    icases Hde with ⟨-, -, -, -, -, -, -, #Heok, -⟩; iexact Heok
  ihave HS : ([∗list] sg ∈ [g], segRes (L := hG.goose_localGS) sg) $$ [Hg]
  · iapply BigSepL.bigSepL_singleton.2; iexact Hg
  iapply wp_segs_size _ _ _ _ rfl _ $$ HS
  iintro %hsz0 HS
  have hsz : ∀ x ∈ [g], x.om.size = x.bs.length ∧ x.bs.length + 2 ^ 12 < 2 ^ 62 := by
    intro x hx
    cases List.mem_singleton.1 hx
    have h := hsz0 g (List.mem_singleton_self _)
    exact ⟨hsize, by omega⟩
  ihave ⟨%fs, %fls, ⟨%htie, %hfr⟩, Hdf, Hlk, #Hfrf⟩ := walDecFiles_mk wp_Stat wp_Size wp_FName wp_IsEof
    wp_Term IoE hIo eof hIoEof false dir [g] frs lfs hfl hll hsz $$ [Hfiles HS]
  · simp only [List.map_cons, List.map_nil, List.drop_zero]
    iframe HosI Heof Hosp Hfiles
    isplitl []
    · iexact Heofa
    unfold segHalves segRes; iexact HS
  subst hfr
  rw [List.map_map] at *
  (try wp_auto)
  wp_apply wp_NewDecoder rsl fs IoE eof $$ [Hrsl Hdf] as %dI ⟨%dec, %hdI, -, Hdec⟩
  · iframe; iframe #
  subst hdI
  (try wp_auto)
  have hbss : fs.map (·.bs) = [segImg g] :=
    decFiles_bs htie.1 (fun k F g h1 h2 => (htie.2.2 k F g h1 h2).1)
  have hinit : ProbeBelow walCodec U (uint.nat index) (fs.map (·.bs)) 0 0#32 := hbss ▸ hbelow
  ihave %hnn := decEnv_nonnil IoE eof ueof $$ Hde
  generalize «$r0_ptr» = rcp at *
  ihave HI : (∃ (fsD : List (DecFile GF)) (kD off : Nat) (c : w32),
      "Hdec" ∷ ownDecoder dec IoE eof fsD off c true ∗ "Hrec" ∷ ownRecAny rcp ∗
      "Hleft" ∷ ([∗list] F ∈ fs.take kD, ∃ q, F.S q) ∗
      "%hkD" ∷ ⌜fsD = fs.drop kD⌝ ∗ "%hprobe" ∷ ⌜ProbeBelow walCodec U (uint.nat index) (fsD.map (·.bs)) off c⌝
      : IProp GF) $$ [Hdec «$r0»]
  · iexists fs, 0, 0, (0#32); simp only [named, List.take_zero]; iframe Hdec
    isplitl [«$r0»]
    · unfold ownRecAny; iexists _; iexact «$r0»
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro; exact ⟨rfl, hinit⟩
  irename «rec» => HrecPtr
  wp_for HI
  (try wp_auto)
  wp_apply (wp_Decode walCodec dec rcp IoE eof ueof fsD off c rfl) $$ [Hdec Hrec] as %e Hpost
  · iframe Hdec Hrec Hde
  (try wp_auto)
  cases e with
  | ok ei =>
    (try wp_auto)
    iunfold decPost at Hpost
    icases Hpost with ⟨Hpb, #Hans, -⟩
    ihave Hall := probe_error_streams dec rcp IoE eof ueof fs fsD kD off c (.ok ei) hkD (by simp) $$ [Hpb Hleft]
    · iframe
    ihave ⟨HS, Hclo⟩ := vse_close dir [g] fs fls lfs htie
      (fun g' hg' => by rw [List.mem_singleton] at hg'; subst hg'; exact wal.closeBound_of hdir' hname) $$ [Hall]
    · iframe Hall; iexact Hfrf
    iunfold decAns at Hans
    icases Hans with (%h | #Hea)
    · cases h
    iunfold isEofAns at Hea
    wp_apply Hea as %b %hb
    cases b <;> (try wp_auto) <;> wp_for_post <;> (try wp_auto)
    all_goals
      (try simp only [decide_eq_false hcl, Bool.not_false])
      (try wp_auto)
      wp_apply Hcl $$ [Hclo] as %e3 -
      · iexact Hclo
      (try wp_auto)
      iapply HΦ
      iunfold wal.probeOwn
      icases BigSepL.bigSepL_singleton.1 $$ HS with Hg
      iframe; iframe #
  | nil =>
    (try wp_auto)
    iunfold decPost at Hpost
    iunfold decPostB at Hpost
    icases Hpost with ⟨⟨%k, Hk, Hm⟩ | ⟨%hio, -, -⟩ | ⟨%k, %sx, %offx, %cx, %hgf, -⟩, -, -⟩
    rotate_left
    · exact absurd hio hIoN
    · exact absurd hgf.2 (stopErr_ne_nil hnn.1 hnn.2 sx)
    generalize hgd : goDecode walCodec (List.map (fun x => x.bs) fsD) off c = gd
    rcases gd with ⟨r, fs', off', c'⟩ | ⟨sx, fs', off', c'⟩
    rotate_left
    · icases Hm with ⟨%hst, -, -⟩
      exact absurd hst.1 (stopErr_ne_nil hnn.1 hnn.2 sx)
    icases Hm with ⟨%hok, Hr, Hdec⟩
    obtain ⟨hsnap, hnext⟩ := hprobe.next hgd
    rw [← hok.2] at hnext
    ihave Hleft := leftS_merge fs fsD kD k hkD $$ [Hleft Hk]
    · iframe
    have hkD' : fsD.drop k = fs.drop (kD + k) := by rw [hkD, List.drop_drop]
    (try wp_auto)
    wp_apply wp_GetType $$ Hr as Hr
    wp_if_destruct
    · have ht : r.typ = crcType := Hif
      wp_apply wp_GetCrc $$ Hr as Hr
      wp_apply wp_UpdateCRC dec IoE eof (fsD.drop k) off' c' r.crc true $$ [Hdec] as Hdec
      · iframe Hdec Hcrc
      wp_for_post
      iframe
      iexists fsD.drop k, kD + k, off', r.crc
      iframe Hdec Hleft
      isplitl [Hr]
      · iapply ownRec_any $$ Hr
      ipureintro; exact ⟨hkD', by simpa [rdCrc, ht] using hnext⟩
    · have hnc : r.typ ≠ crcType := Hif
      wp_if_destruct
      · have ht : r.typ = snapshotType := Hif
        obtain ⟨p, hp, hlt⟩ := hsnap ht
        obtain ⟨c₀, hu, hbs, hc₀⟩ := hUs r.data p hp
        unfold ownRec
        icases Hr with ⟨%v, Hl, Ht, Hc, Hd⟩
        (try wp_auto)
        have wpU := wp_Unmarshal pbSnapC pbSnapC_reg v.Data' r.data (DFrac.own 1) snap_ptr
        simp only [pbSnapC_ty] at wpU
        wp_apply wpU $$ [Hd snap] as %errU ⟨Hd, %Hok, Hdecoded⟩
        · iframe Hd; simp only [pbSnapC, pbSnapM]; iexact snap
        have heU : errU = GoInterface.nil := Hok ⟨c₀, trivial, hu, hbs⟩
        subst heU
        (try wp_auto)
        ihave ⟨%cR, Hm, %hCR⟩ := Hdecoded $$ %rfl
        obtain ⟨-, -, -, huniq⟩ := hCR
        have heq := huniq c₀ trivial hu hbs
        subst heq
        iapply wp_fupd
        imod snapOwnC_freeze snap_ptr cR $$ Hm with #Hm
        ihave #Hid : walSnapIdTerm snap_ptr p $$ []
        · unfold walSnapIdTerm; iexists cR; iframe Hm; ipureintro; exact hc₀
        wp_apply wp_SnapIndex snap_ptr p $$ Hid
        have hne : p.1 ≠ index := fun e => by rw [e] at hlt; omega
        (try wp_auto)
        (try simp only [hne, decide_false, Bool.false_eq_true, ↓reduceIte])
        (try wp_auto)
        wp_for_post
        (try imodintro)
        (try wp_auto)
        iframe
        iexists fsD.drop k, kD + k, off', c'
        iframe Hdec Hleft
        isplitl [Hl Ht Hc Hd]
        · unfold ownRecAny; iexists v; iexact Hl
        ipureintro; exact ⟨hkD', by simpa [rdCrc, hnc] using hnext⟩
      · wp_for_post
        iframe
        iexists fsD.drop k, kD + k, off', c'
        iframe Hdec Hleft
        isplitl [Hr]
        · iapply ownRec_any $$ Hr
        ipureintro; exact ⟨hkD', by simpa [rdCrc, hnc] using hnext⟩

end proof
end EtcdGrove
end Perennial
