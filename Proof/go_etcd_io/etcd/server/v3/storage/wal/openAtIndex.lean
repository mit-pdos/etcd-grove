/-
The proof of `Spec/go_etcd_io/etcd/server/v3/storage/wal/openAtIndex.lean` (W5 of
`notes/wal-fsext-plan.md`; the W3/W5 log, twelfth session). The update commits and the WAL is pinned at
the first step (`walInv_openAt`, `OpenAtPin.lean`); then `selectWALFiles`, `openWALFiles`, the decoder
(`walDecFiles_mk`, `NewDecoder`), the struct, and in write mode `parseWALName` of the tail's name and the
pipeline; the error arms put the pinned halves back at the `Errorf` call's step (`walInv_unpin`).
The path to the WAL directory is lent by the invariant (`walInv_dirPath`, with the pin's
`walNamesFrag none`; until 2026-11-14 the hypothesis `WalDirPathLaw`). Hypotheses besides the callees'
specs: `WalDecEnvSupply` (the decoder's environment from the package's initialization). (Until
2026-11-14 also `WalPinSized`: the segments' size bound is now read at the step after the pin,
`wp_segs_size`, `SegSize.lean`.)
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFilesAbsent
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__Clone
public import Spec.os.File__Name
public import Spec.path.filepath.Base
public import Spec.fmt.ErrorfErrs
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtSteps
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenNames
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtTail
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.selectWALFilesLemmas
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HandleLoans
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SegSize
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePre
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.openAtIndexLemmas

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open Fs WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.wp_proof (Mr : WalMarshal)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_IsEof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG))
    (wp_Term : errors.IsPathErrnoTerm.spec (GF := GF) (hG := hG))
    (wp_Clone : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.Clone.spec (GF := GF) (hG := hG))
    (wp_select : go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.spec (GF := GF) (hG := hG))
    (wp_selectAbs : go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.specAbsent (GF := GF) (hG := hG))
    (wp_openFiles : go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.spec (GF := GF) (hG := hG))
    (wp_NewDecoder : go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Base : filepath.Base.spec (GF := GF) (hG := hG))
    (wp_parse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG))
    (wp_pipe : go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_FName : os.fileStat.Name.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.spec (W := W) Mr := by
  intro lg R jr r dir nm sp s write qp Q ic hin hnmO hr hdl
  have hdl' : dir.length < 4096 := hdl.1
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, #Hsp, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb0, %hrb1, -⟩
  have hrb := And.intro hrb0 hrb1
  icases walInv_roots _ _ _ _ _ $$ Hinv with %hWR
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %hok, Hcl⟩
  icases osPathS_callKey R r _ jr $$ Hp with ⟨Hp, %hkc⟩
  have hkd : callKey R dir = callKey R r := by rw [show dir = child r nm by rw [hin.2]; simp [child]; rfl]; exact hkc nm
  rw [← hkd]
  have hnm := hin.1
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_openAt walCodec Mr R jr r dir nm N _ h Wn write s.1 Q ic hin (hok.1 nm hnm)
    $$ Hinv Hsi Hnc Hu Hau HN Hsf with ⟨Hnc, HN, Hsf, %o, HQ, Hcase⟩
  icases Hcase with (⟨⟨%ho, %hNnm, %hcn⟩, Hu⟩ | ⟨%ho, %d, Hpin⟩)
  · -- no WAL: `selectWALFiles` fails on the missing directory
    subst ho
    imodintro
    iframe Hnc
    wp_apply wp_Clone sp s $$ [] as %sp' #Hsp'
    · iexact Hsp
    try wp_auto
    have hdc := dir_child hin
    subst hdc
    wp_apply wp_selectAbs lg r nm sp' R jr (DFrac.own qp) 1 N (DFrac.own (1 : Qp).half) h hnmO hNnm hcn
      $$ [Hp Hperm HN] as %rr %kk %err ⟨Hp, Hperm, HN, %e, %herr, #He⟩
    · rw [hkd]; iframe; iframe #
    rw [← hkd]
    subst herr
    try wp_auto
    wp_apply wp_slice_literal (V := GoAny) [interface.ok e]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply wp_Errorf _ _ [interface.ok e] [e] ?wf $$ [Hasl] as %e1 #He1
    case wf => errargs_wf
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
      iexact He
    try wp_auto
    iapply HΦ
    iframe Hp
    isplitl [HN Hsf Hcl]
    · iapply walAreaRes_close jr N h cl Wn hok; iframe
    iexists none
    iframe HQ
    ileft
    isplitr
    · ipureintro; nofun
    iframe Hu Hperm
    iexists e1
    iframe He1
    ipureintro; rfl
  · unfold walPinOut
    icases Hpin with ⟨%lay, %X, %hj, %hfacts, #Hkey, ⟨%Il, Hl, %hIl⟩, Htf, Ho, HS, Hj, Ht⟩
    subst hIl
    obtain ⟨hljr, hX, hcoh, habs, hnd, hsn⟩ := hfacts
    icases Htf with ⟨Htf, Hnf⟩
    icases walLockedTokI_incQ (W := W) Il $$ Hl with ⟨HIl, Hl⟩
    imod walInv_dirPath walCodec Mr R jr r dir Il lay.j X [] $$ Hinv Hnc Hnf Hkey HIl
      with ⟨Hnc, HIl, %nmd, %qd, %hdnm, Hnf, Hpd⟩
    ihave Hl := Hl $$ HIl
    have hnmd : nmd = nm := Fs.child_inj (hdnm.symm.trans (dir_child hin))
    subst nmd
    imodintro
    iframe Hnc
    have hnmf := walLay_nameFmt habs
    have hdn : WalDirNamesOk (.except X) hj := walDirNamesOk_of hX hsn habs.names.1 hnd hnmf
    have hS : ∀ g ∈ lay.segs.drop (walOpenK s.1 lay), g.om.size = g.bs.length := fun g hg =>
      (habs.metas g (List.mem_of_mem_drop hg)).1
    -- the segments' size bound, before the next step (the model's `s_maxbytes`)
    iapply wp_segs_size _ _ _ _ rfl _ $$ HS
    iintro %hsz0 HS
    have hsz : ∀ g ∈ lay.segs.drop (walOpenK s.1 lay), g.bs.length + 2 ^ 12 < 2 ^ 62 := fun g hg => by
      have h1 := hsz0 g hg; rw [hS g hg] at h1; omega
    wp_apply wp_Clone sp s $$ [] as %sp' #Hsp'
    · iexact Hsp
    try wp_auto
    wp_apply wp_select lg dir sp' s R lay.j (DFrac.own qd) 1 (.except X) (DFrac.own (1 : Qp).half) hj hdn
      $$ [Hpd Hperm Hj] as %rr %kk %err ⟨Hpd, Hperm, Hj, Hsel⟩
    · iframe; iframe #
    icases Hsel with (⟨%ws, ⟨%herr, %hk0, %hsel⟩, Hws⟩ | ⟨%e, %herr, #He⟩)
    rotate_left
    · -- `selectWALFiles` failed: the halves back
      subst herr
      try wp_auto
      wp_apply wp_slice_literal (V := GoAny) [interface.ok e]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_dirPathRetD walCodec Mr R jr r dir nm qd lay.j hdnm $$ Hinv Hnc Hnf Hpd with ⟨Hnc, Hnf⟩
      ihave Htf : iprop(walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) $$ [Htf Hnf]
      · iframe
      imod walInv_unpin walCodec Mr R jr r dir lay.j X hj _ write hS Il _ rfl $$ Hinv Hnc Hl Htf Ho HS Hj Ht Hkey
        with ⟨Hnc, Hu⟩
      imodintro
      iframe Hnc
      wp_apply wp_Errorf _ _ [interface.ok e] [e] ?wf $$ [Hasl] as %e1 #He1
      case wf => errargs_wf
      · iframe
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
        iexact He
      try wp_auto
      iapply HΦ
      iframe Hp
      isplitl [HN Hsf Hcl]
      · iapply walAreaRes_close jr N h cl Wn hok; iframe
      iexists o
      iframe HQ
      ileft
      isplitr
      · ipureintro; nofun
      iframe Hu Hperm
      iexists e1
      iframe He1
      ipureintro; rfl
    obtain ⟨hout, hsearch, -⟩ := hsel
    have hws : ws = lay.segs.map (·.name) :=
      walNamesOut_segs hX hsn habs.names.1 hnd habs.names.2 hnmf hout
    have hK : walOpenK s.1 lay = sint.nat kk := walOpenK_eq hsearch hws
    have hselg : ∀ g, (lay.segs.drop (sint.nat kk)).head? = some g → ∀ sq ix,
        g.name = walFileName sq ix → ix < 2 ^ 64 → ix ≤ uint.nat s.1 :=
      fun g hg sq ix hn hix => walSearch_sel (by rw [← hws]; exact hsearch) g hg sq ix hn hix
    have hKl : sint.nat kk < ws.length := walSearch_lt hsearch
    have hwl : ws.length = lay.segs.length := by rw [hws, List.length_map]
    subst herr
    rw [hK] at hS hsz
    rw [hK]
    try wp_auto
    wp_apply wp_openFiles lg dir rr ws (DFrac.own 1) kk write ((lay.segs.map (·.ino)).drop (sint.nat kk))
      R lay.j (DFrac.own qd) 1 (.except X) (DFrac.own (1 : Qp).half) hj hk0 (by omega)
      (by simp [hwl]) hdl (walOpenNames_ok (sint.nat kk) hX hsn hnmf hout hws)
      $$ [Hpd Hperm Hj Hws] as %rsl %lsl %clo %err2 ⟨Hpd, Hperm, Hj, Hws, Hopen⟩
    · iframe; iframe #
    icases Hopen with (⟨%frs, %lfs, ⟨%herr2, %hfl, %hll⟩, Hrsl, Hrc, Hlsl, Hlc, Hfiles, -⟩ | ⟨%e, %herr, #He, -⟩)
    rotate_left
    · -- `openWALFiles` failed: the halves back
      obtain ⟨-, rfl⟩ : True ∧ err2 = GoInterface.ok e := ⟨trivial, herr⟩
      try wp_auto
      wp_apply wp_slice_literal (V := GoAny) [interface.ok e]
      isplitr
      · ipureintro; rfl
      iintro %asl ⟨Hasl, -⟩
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_dirPathRetD walCodec Mr R jr r dir nm qd lay.j hdnm $$ Hinv Hnc Hnf Hpd with ⟨Hnc, Hnf⟩
      ihave Htf : iprop(walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) $$ [Htf Hnf]
      · iframe
      imod walInv_unpin walCodec Mr R jr r dir lay.j X hj _ write hS Il _ rfl $$ Hinv Hnc Hl Htf Ho HS Hj Ht Hkey
        with ⟨Hnc, Hu⟩
      imodintro
      iframe Hnc
      wp_apply wp_Errorf _ _ [interface.ok e] [e] ?wf $$ [Hasl] as %e1 #He1
      case wf => errargs_wf
      · iframe
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
        iexact He
      try wp_auto
      iapply HΦ
      iframe Hp
      isplitl [HN Hsf Hcl]
      · iapply walAreaRes_close jr N h cl Wn hok; iframe
      iexists o
      iframe HQ
      ileft
      isplitr
      · ipureintro; nofun
      iframe Hu Hperm
      iexists e1
      iframe He1
      ipureintro; rfl
    subst herr2
    -- the decoder over the opened files
    rw [hws, ← List.map_drop, ← List.map_drop] at *
    have hKs : sint.nat kk < lay.segs.length := by omega
    have hsz' : ∀ g ∈ lay.segs.drop (sint.nat kk), g.om.size = g.bs.length ∧ g.bs.length + 2 ^ 12 < 2 ^ 62 :=
      fun g hg => ⟨hS g hg, hsz g hg⟩
    generalize hgs : lay.segs.drop (sint.nat kk) = gs at *
    have hgl : gs.length = lay.segs.length - sint.nat kk := by rw [← hgs, List.length_drop]
    obtain ⟨gL, hgL⟩ : ∃ gL, gs[gs.length - 1]? = some gL :=
      ⟨gs[gs.length - 1]'(by omega), List.getElem?_eq_getElem _⟩
    rw [List.length_map] at hfl hll
    have hEnv' : ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal -∗
        ∃ (IoE : GoInterface → Prop) (eof ueof : GoInterface), decEnv IoE eof ueof ∗
          ⌜(∀ pe : Loc, IoE (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) ∧
            ¬ IoE GoInterface.nil⌝ := hEnv
    ihave ⟨%IoE, %eof, %ueof, #Hde, %hIo⟩ := hEnv' $$ Hpkg
    obtain ⟨hIo, hIoN⟩ := hIo
    ihave #Hde' := Hde
    iunfold decEnv at Hde'
    icases Hde' with ⟨-, -, -, -, #Hbufio, #Heof, -, -, #Hcrc, -, -⟩
    ihave ⟨Hfiles, #Hlast⟩ := WalFs.walOpenedFiles_last write dir gs frs lfs _ gL hgL $$ Hfiles
    ihave #Hosp := wal_osInit $$ Hpkg
    ihave ⟨#Heofa, %hIoEof⟩ := isEofOk_eof IoE eof ueof $$ [Hde]
    · iunfold decEnv at Hde
      icases Hde with ⟨-, -, -, -, -, -, -, #Hok, -⟩
      iexact Hok
    ihave ⟨%fs, %fls, ⟨%htie, %hfr⟩, Hdf, Hlk, -⟩ := walDecFiles_mk wp_Stat wp_Size wp_FName wp_IsEof wp_Term IoE hIo eof
      hIoEof write dir gs frs lfs hfl hll hsz' $$ [Hfiles HS]
    · iframe Hfiles
      isplitl []
      · iexact Hosi
      isplitl []
      · iexact Heof
      isplitl []
      · iexact Hosp
      isplitl []
      · iexact Heofa
      unfold segHalves segRes
      iexact HS
    subst hfr
    rw [List.map_map] at *
    try wp_auto
    wp_apply wp_NewDecoder rsl fs IoE eof $$ [Hrsl Hdf] as %dI ⟨%dec, %hdI, Hrsl, Hdec⟩
    · iframe; iframe #
    irename lg => Hlgp
    irename «$r0» => Hwal
    generalize «$r0_ptr» = wl at *
    iStructNamed Hwal
    imod sync.init_Mutex (BI.pure True : IProp GF) ⊤
      (structFieldRef go_etcd_io.etcd.server.v3.storage.wal.WAL go!"mu" wl) $$ mu [] with #Hmu
    · inext; ipureintro; trivial
    ihave #Henc := wal_encEnv $$ Hpkg
    have hnmg : ∀ g ∈ gs, hj.cur !! g.name = some (.file g.ino) := fun g hg =>
      (hsn.1 g (by rw [← hgs] at hg; exact List.mem_of_mem_drop hg)).2
    have hndg : (gs.map (·.ino)).Nodup := by
      rw [← hgs, List.map_drop]; exact hnd.sublist (List.drop_sublist _ _)
    have htf := walReadTie_facts htie hll hnmg
    have hgne : gs ≠ [] := List.ne_nil_of_length_pos (by omega)
    have hlastw : write = true → ∀ g, gs.getLast? = some g → (walNames hj.cur).getLast? = some g.name := by
      intro _ g hg
      rw [walNames_segs hsn habs.names.1 hnd habs.names.2, List.getLast?_map]
      rw [← hgs, List.getLast?_drop, if_neg (by omega)] at hg
      rw [hg]; rfl
    have hdropn : ∃ kk, (walNames hj.cur).drop kk = gs.map (·.name) :=
      ⟨sint.nat kk, by rw [walNames_segs hsn habs.names.1 hnd habs.names.2, ← hgs, List.map_drop]⟩
    try wp_auto
    wp_join iprop(walReadFallback wl dir (walNames hj.cur) (gs.map (·.name)) ∗ w_ptr ↦ wl)
      at (If _ _ _) with [w names nameIndex fallback Hws] as ⟨Hfall, w⟩
    · wp_if_destruct
      · try wp_auto
        isplitr
        · itrivial
        iframe w
        unfold walReadFallback
        iexists _
        iframe fallback
        iright
        iexists _, lay.segs.map (·.name)
        iframe
        dsimp only
        ipureintro
        refine ⟨by word, hKl, by omega, (walNames_segs hsn habs.names.1 hnd habs.names.2).symm, ?_⟩
        rw [← hgs, List.map_drop]
      · try wp_auto
        isplitr
        · itrivial
        iframe w
        unfold walReadFallback
        iexists null
        iframe fallback
        ileft; ipureintro; rfl
    cases write
    · -- read mode: the directory path's loan back
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_dirPathRetD walCodec Mr R jr r dir nm qd lay.j hdnm $$ Hinv Hnc Hnf Hpd with ⟨Hnc, Hnf⟩
      ihave Htf : iprop(walTailsFrag (W := W) ∅ ∗ walHLoans (W := W) dir none []) $$ [Htf Hnf]
      · iframe Htf
        have hm := walHLoans_mk (W := W) dir r nm [] hin
        simp only [List.map_nil] at hm
        iapply hm $$ Hnf
      imodintro
      iframe Hnc
      try wp_auto
      iapply HΦ
      iframe Hp
      isplitl [HN Hsf Hcl]
      · iapply walAreaRes_close jr N h cl Wn hok; iframe
      iexists o
      iframe HQ
      iright
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact ho
      iframe dirFile
      simp only [Bool.false_eq_true, ↓reduceIte]
      iframe Hperm
      isplitl [Hl]
      · iexists Il
        isplitl [Hl]
        · iexact Hl
        · ipureintro; rfl
      unfold walReadH walOpenIn walReadTie
      isplitl [lg dir start]
      · iexists lg, sp'
        iframe
        iframe #
      iexists dec, IoE, eof, ueof, fs, lsl, lfs, null, clo, lay.j, []
      subst hdI
      iframe
      iframe #
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr
      · ipureintro; exact hIoN
      isplitl [Ho Hlk]
      · iexists fls
        iframe Ho
        isplitr
        · ipureintro; exact ⟨hgne, hndg, hS, hselg, by first | exact fun h => h.elim | exact fun _ => ⟨hlastw rfl, hXt⟩ | exact fun _ => hlastw rfl | exact hlastw rfl | exact hlastw, hdropn⟩
        isplitr
        · ipureintro; exact htf
        iexact Hlk
      ipureintro; trivial
    · -- write mode
      have hgLm : gL ∈ lay.segs := by
        have := List.mem_of_getElem? hgL
        rw [← hgs] at this; exact List.mem_of_mem_drop this
      obtain ⟨sqL, ixL, hgLn⟩ := hnmf gL hgLm
      obtain ⟨ls, lt, hlfs⟩ : ∃ ls lt, lfs = ls ++ [lt] := by
        rcases List.eq_nil_or_concat lfs with h0 | ⟨ls, lt, h1⟩
        · subst h0; simp at hll; omega
        · exact ⟨ls, lt, by rw [h1, List.concat_eq_append]⟩
      have hlt : lfs.getD (gs.length - 1) null = lt := by
        subst hlfs; simp only [List.length_append, List.length_singleton] at hll
        rw [← hll]; simp [List.getD]
      rw [hlt]
      simp only [↓reduceIte]
      icases Hlast with ⟨%fL, #HfL, #HltL⟩
      try wp_auto
      rw [hlfs]
      wp_apply (wp_tail wl lsl ls lt (DFrac.own 1) (DFrac.own 1)) $$ [locks Hlsl] as ⟨locks, Hlsl⟩
      · iframe
      ihave #Hlt1 := HltL
      iunfold fileutil.lockedFile at Hlt1
      ihave %hltn := typedPointsto_not_null lt _ _ $$ Hlt1
      iStructNamed Hlt1
      try simp only [decide_eq_false hltn]
      try wp_auto
      wp_method_call
      wp_call
      try wp_auto
      wp_apply os.File.Name.wp_named fL (child dir gL.name) $$ []
      · iexact HfL
      try wp_auto
      wp_apply wp_Base as %bn %hbn
      rw [hgLn, baseModel_child_walFileName] at hbn
      subst hbn
      try wp_auto
      obtain ⟨hsuf, hscan⟩ := scanWalName_walFileName sqL ixL
      wp_apply wp_parse as %sq' %ix' %perr %hpe
      obtain ⟨rfl, -, -⟩ := hpe.1 _ _ hsuf hscan
      try wp_auto
      ihave #Hw2 : (wal.walInit : IProp GF) $$ []
      · iapply isPkgInit_access $$ Hpkg
      ihave #Hseg := wal.walInit_segSize $$ Hw2
      try wp_auto
      ihave ⟨Hperm1, Hcp⟩ := osCallPerm_halves' _ $$ Hperm
      icases osCallPerm_halfSplit _ (1 : Qp).half $$ Hperm1 with ⟨Hperm1, Hperm2⟩
      icases Ht with ⟨Ht, HIe⟩
      imod walTmpsRes_mem_except R lay.j X _ hj $$ Hsi Hj Ht with ⟨%hXt, Hj, Ht⟩
      icases walPipeKey_ofLocked (W := W) Il dir _ lay.j X rfl $$ Hl Hkey HIe with ⟨Hl, Hpk⟩
      ihave ⟨Ht0, Ht1⟩ := walTmpsRes_split lay.j $$ Ht
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_mintOpening walCodec Mr R jr r wl dir s Il $$ Hinv Hnc Hl with ⟨Hnc, Hop⟩
      imodintro
      iframe Hnc
      wp_apply wp_pipe lg dir (W64 64000000) R (DFrac.own qd) lay.j (by decide) (by decide) (by omega)
        (by decide) $$ [Hperm1 Hpd Ht0 Hpk] as %fp ⟨%hfpn, %γ, #Hfp, Hmain⟩
      · iframe; iframe #
        unfold pipeRes
        iframe
      try wp_auto
      ihave Htf : iprop(walTailsFrag (W := W) ∅ ∗ walHLoans (W := W) dir none [qd]) $$ [Htf Hnf]
      · iframe Htf
        have hm := walHLoans_mk (W := W) dir r nm [qd] hin
        simp only [List.map_cons, List.map_nil] at hm
        iapply hm $$ Hnf
      iapply HΦ
      iframe Hp
      isplitl [HN Hsf Hcl]
      · iapply walAreaRes_close jr N h cl Wn hok; iframe
      iexists o
      iframe HQ
      iright
      isplitr
      · ipureintro; rfl
      isplitr
      · ipureintro; exact ho
      iframe dirFile Hop Hperm2 Hcp
      unfold walReadH walOpenIn walReadTie
      isplitl [lg dir start]
      · iexists lg, sp'
        iframe
        iframe #
      rw [← hlfs]
      iexists dec, IoE, eof, ueof, fs, lsl, lfs, fp, func.nil, lay.j, [qd]
      subst hdI
      iframe
      iframe #
      simp only [↓reduceIte]
      isplitr
      · ipureintro; exact hIoN
      isplitl [Ho Hlk]
      · iexists fls
        iframe Ho
        isplitr
        · ipureintro; exact ⟨hgne, hndg, hS, hselg, by first | exact fun h => h.elim | exact fun _ => ⟨hlastw rfl, hXt⟩ | exact fun _ => hlastw rfl | exact hlastw rfl | exact hlastw, hdropn⟩
        isplitr
        · ipureintro; exact htf
        rw [hlfs]
        iexact Hlk
      isplitr
      · ipureintro; rfl
      unfold walPipeH
      iexists γ, R, DFrac.own qd, W64 64000000, 0
      iframe
      iframe #
      isplitr
      · ipureintro; exact ⟨Nat.le_refl 0, qd, rfl, rfl⟩
      · ipureintro; exact ⟨hfpn, hWR.symm⟩

end proof

end EtcdGrove
end Perennial
