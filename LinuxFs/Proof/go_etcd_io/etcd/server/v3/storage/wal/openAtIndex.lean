/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/openAtIndex.lean` (W5 of
`notes/wal-fsext-plan.md`; the W3/W5 log, twelfth session). The update commits and the WAL is pinned at
the first step (`walInv_openAt`, `OpenAtPin.lean`); then `selectWALFiles`, `openWALFiles`, the decoder
(`walDecFiles_mk`, `NewDecoder`), the struct, and in write mode `parseWALName` of the tail's name and the
pipeline; the error arms put the pinned halves back at the `Errorf` call's step (`walInv_unpin`).
Hypotheses besides the callees' specs: `WalPinSized` and `WalDirPathLaw` (the invariant's owner's,
`OpenAtPin.lean`), `WalDecEnvSupply` (the decoder's environment from the package's initialization).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFilesAbsent
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.openWALFiles
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.NewDecoder
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.parseWALName
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.WAL__tail
public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot__Clone
public import LinuxFs.Spec.os.File__Name
public import LinuxFs.Spec.path.filepath.Base
public import LinuxFs.Spec.fmt.ErrorfErrs
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtSteps
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenFiles
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenNames
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateArea
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePure
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.OpenAtTail
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode
open Fs WalEnc WalFs

section pure
variable [GooseExts]

theorem walLay_nameFmt {C : WalCodec} {Mr : WalMarshal} {d : WalDur} {lay : WalLay} {ents : Ents}
    (habs : WalAbsD C Mr d lay ents) : ∀ g ∈ lay.segs, ∃ sq ix : Nat, g.name = walFileName sq ix := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  obtain ⟨sq, ix, h1, -⟩ := habs.nameBound k _ (List.getElem?_eq_getElem hk)
  exact ⟨sq, ix, h1⟩

theorem walOpenK_eq {idx : w64} {lay : WalLay} {ws : List GoString} {k : Nat}
    (hk : walSearch (ws.map walNameIdx) idx = some k) (hws : ws = lay.segs.map (·.name)) :
    walOpenK idx lay = k := by
  unfold walOpenK; rw [← hws, hk]; rfl

theorem walSearch_lt {ws : List GoString} {idx : w64} {k : Nat}
    (hk : walSearch (ws.map walNameIdx) idx = some k) : k < ws.length := by
  have := walSearchFrom_lt hk; simpa using this

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [os.file.FieldAssumptions] [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- **The decoder's environment** (hypothesis): from the WAL package's initialization, `io.EOF`'s and
`io.ErrUnexpectedEOF`'s values, `errors.Is(_, io.EOF)` on the readers' errors (`isEofOk`, over Perennial's
`errors.Is` on pointer errors), the decoder's packages and variables (`decEnv`); the readers' errors are
the pointer errors (`os.File.Read`'s and `Stat`'s `*PathError`s). -/
def WalDecEnvSupply : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ⊢
    ∃ (IoE : GoInterface → Prop) (eof ueof : GoInterface), decEnv IoE eof ueof ∗
      ⌜∀ ii, _root_.Perennial.errors.IsPointerError ii → IoE (GoInterface.ok ii)⌝

/-- The program's area claim back. -/
theorem walAreaRes_close (jr : Ino) (N : NameSet) (h : NamesH) (cl : List (GoString × Claim))
    (hok : AreaOk N h cl) :
    osNames (L := hG.goose_localGS) jr N (DFrac.own (1 : Qp).half) h ∗
      osClaims hG.goose_localGS (cl.map (fun c => (c.2, DFrac.own 1))) ⊢
      walAreaRes (L := hG.goose_localGS) jr := by
  unfold walAreaRes
  iintro ⟨Hn, Hc⟩
  iexists N, h, cl
  iframe
  ipureintro; exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩

theorem go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.wp_proof (Mr : WalMarshal)
    (hpin : ∀ R jr r, WalPinSized (L := hG.goose_localGS) (W := W) walCodec Mr R jr r)
    (hpath : ∀ R jr r, WalDirPathLaw (L := hG.goose_localGS) (W := W) walCodec Mr R jr r)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_Clone : go_etcd_io.etcd.server.v3.storage.wal.walpb.Snapshot.Clone.spec (GF := GF) (hG := hG))
    (wp_select : go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.spec (GF := GF) (hG := hG))
    (wp_selectAbs : go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles.specAbsent (GF := GF) (hG := hG))
    (wp_openFiles : go_etcd_io.etcd.server.v3.storage.wal.openWALFiles.spec (GF := GF) (hG := hG))
    (wp_NewDecoder : go_etcd_io.etcd.server.v3.storage.wal.NewDecoder.spec (GF := GF) (hG := hG))
    (wp_tail : go_etcd_io.etcd.server.v3.storage.wal.WAL.tail.spec (GF := GF) (hG := hG))
    (wp_Name : os.File.Name.spec (GF := GF) (hG := hG))
    (wp_Base : filepath.Base.spec (GF := GF) (hG := hG))
    (wp_parse : go_etcd_io.etcd.server.v3.storage.wal.parseWALName.spec (GF := GF) (hG := hG))
    (wp_pipe : go_etcd_io.etcd.server.v3.storage.wal.newFilePipeline.spec (GF := GF) (hG := hG))
    (wp_Errorf : fmt.ErrorfErrs.spec (GF := GF) (hG := hG))
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_FName : os.fileStat.Name.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.spec (W := W) Mr := by
  intro lg R jr r dir nm sp s write qp Q hin hnmO hr hdl
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, #Hsp, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb⟩
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, HN, %hok, Hcl⟩
  have hnm := hin.1
  have hNnm : N.Mem nm := hok.1 nm hnm
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_openAt walCodec Mr R jr r (hpin R jr r) dir nm N _ h write s.1 Q hin hNnm
    $$ Hinv Hsi Hnc Hu Hau HN with ⟨Hnc, HN, %o, HQ, Hcase⟩
  icases Hcase with (⟨⟨%ho, %hcn⟩, Hu⟩ | ⟨%ho, %d, Hpin⟩)
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
    · iframe; iframe #
    subst herr
    try wp_auto
    wp_apply wp_slice_literal (V := GoAny) [interface.ok e]
    isplitr
    · ipureintro; rfl
    iintro %asl ⟨Hasl, -⟩
    wp_apply wp_Errorf _ _ [interface.ok e] [e] (by
        intro ii hii
        right
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
        cases hii
        simp) $$ [Hasl] as %e1 #He1
    · iframe
      iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
      iexact He
    try wp_auto
    iapply HΦ
    iframe Hp
    isplitl [HN Hcl]
    · iapply walAreaRes_close jr N h cl hok; iframe
    iexists none
    iframe HQ
    ileft
    iframe
    ipureintro; nofun
  · unfold walPinOut
    icases Hpin with ⟨%lay, %X, %hj, %hfacts, #Hkey, Hl, Htf, Ho, HS, Hj, Ht⟩
    obtain ⟨hljr, hX, hcoh, habs, hnd, hsn, hsz⟩ := hfacts
    imod hpath R jr r dir lay.j X qp $$ Hinv Hnc Hkey Hp with ⟨Hnc, Hp, %qd, Hpd⟩
    imodintro
    iframe Hnc
    have hnmf := walLay_nameFmt habs
    have hdn : WalDirNamesOk (.except X) hj := walDirNamesOk_of hX hsn habs.names.1 hnd hnmf
    have hS : ∀ g ∈ lay.segs.drop (walOpenK s.1 lay), g.om.size = g.bs.length := fun g hg =>
      (habs.metas g (List.mem_of_mem_drop hg)).1
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
      imod walInv_unpin walCodec Mr R jr r dir lay.j X hj _ write hS $$ Hinv Hnc Hl Htf Ho HS Hj Ht Hkey
        with ⟨Hnc, Hu⟩
      imodintro
      iframe Hnc
      wp_apply wp_Errorf _ _ [interface.ok e] [e] (by
          intro ii hii
          right
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hii
          cases hii
          simp) $$ [Hasl] as %e1 #He1
      · iframe
        iapply (BigSepL.bigSepL_singleton (Φ := fun _ e => errOk (GF := GF) e)).2
        iexact He
      try wp_auto
      iapply HΦ
      iframe Hp
      isplitl [HN Hcl]
      · iapply walAreaRes_close jr N h cl hok; iframe
      iexists o
      iframe HQ
      ileft
      iframe
      ipureintro; nofun
    sorry

end proof

end EtcdGrove
end Perennial
