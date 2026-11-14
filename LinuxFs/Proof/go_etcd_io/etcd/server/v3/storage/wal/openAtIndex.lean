/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/openAtIndex.lean` (W5 of
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
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutName
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.NameClaims
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.SegSize
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePre

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
  obtain ⟨sq, ix, h1, -, -⟩ := habs.nameBound k _ (List.getElem?_eq_getElem hk)
  exact ⟨sq, ix, h1⟩

theorem walOpenK_eq {idx : w64} {lay : WalLay} {ws : List GoString} {k : Nat}
    (hk : walSearch (ws.map walNameIdx) idx = some k) (hws : ws = lay.segs.map (·.name)) :
    walOpenK idx lay = k := by
  unfold walOpenK; rw [← hws, hk]; rfl

theorem walSearch_lt {ws : List GoString} {idx : w64} {k : Nat}
    (hk : walSearch (ws.map walNameIdx) idx = some k) : k < ws.length := by
  have := walSearchFrom_lt hk; simpa using this

/-- **The selected segment's name index is at most the start's** (`searchIndex`; `readAll_success`'s
`hsel`), for a name `walFileName sq ix` with `ix < 2^64` (`walFileName` keeps `ix` modulo `2^64`). -/
theorem walSearch_sel {segs : List SegG} {idx : w64} {k : Nat}
    (hk : walSearch ((segs.map (·.name)).map walNameIdx) idx = some k) (g : SegG)
    (hg : (segs.drop k).head? = some g) (sq ix : Nat) (hn : g.name = walFileName sq ix)
    (hix : ix < 2 ^ 64) : ix ≤ uint.nat idx := by
  have hle := walSearchFrom_le hk
  have hg' : segs[k]? = some g := by
    rw [List.head?_drop] at hg; exact hg
  have e : ((segs.map (·.name)).map walNameIdx).getD k 0 = BitVec.ofNat 64 ix := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_map, hg']
    simp only [Option.map_some, Option.getD_some]
    rw [hn, walFileName_walNameStr]
    unfold walNameIdx
    rw [fmt.scanWalName_walNameStr]
  rw [e] at hle
  have h1 : uint.Z (BitVec.ofNat 64 ix) = ix := by
    simp only [uint.Z, BitVec.toNat_ofNat]; omega
  have h2 : uint.Z idx = uint.nat idx := by simp [uint.Z, uint.nat]
  omega

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
`io.ErrUnexpectedEOF`'s values, `errors.Is(_, io.EOF)` on the readers' errors (`isEofOk`), the decoder's
packages and variables (`decEnv`); the readers' errors `IoE` hold of every `*PathError` (`os.File.Read`'s
and `Stat`'s errors) and not of `nil` (since 2026-11-14, `wal-readall20`: `ReadAll`'s loop goes on at
`err == nil`, so an I/O error `nil` would run its body on a dead decoder; ledger, "no I/O error is nil"). Until 2026-11-14 `IoE` held of every pointer error, which made the hypothesis
unsatisfiable (`isEofOk` needs `¬ IoE eof`, and `io.EOF` is a pointer error); `walDecEnv_eof_not` checks
that the new form's pure part agrees with `io`'s initialization. Since 2026-11-14 (`wal-readall17`; ledger,
"the readers' errors and `errors.Is`", adopted provisionally) `isEofOk` asks `errors.Is(e, io.EOF)`'s
answer only on `nil`, `io.EOF` and `io.ErrUnexpectedEOF` (the readers' errors carry their own, `decRdE`),
so the hypothesis is true of Go. **Not provable from the packages' facts**: `errors.newVar` (Perennial's
`io` fact, the part's `walpb` fact) keeps no trace of the allocation, so nothing says `io.EOF`,
`io.ErrUnexpectedEOF` and `walpb.ErrCRCMismatch` are three different errors (`eof ≠ ueof`, and
`errors.Is(ErrCRCMismatch, io.EOF)` false); the general fix is a Perennial change (`newVar` keeping the
`errorString`'s field, `notes/perennial-changes.md`). -/
abbrev WalDecEnvSupply : Prop :=
  ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal -∗
    ∃ (IoE : GoInterface → Prop) (eof ueof : GoInterface), decEnv IoE eof ueof ∗
      ⌜(∀ pe : Loc, IoE (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe)) ∧
        ¬ IoE GoInterface.nil⌝

/-- **The sanity check of `WalDecEnvSupply`'s pure part**: by `io`'s initialization `io.EOF` holds an
`*errorString` (`errors.newVar`), so it is no `*PathError`, and `IoE` the `*PathError`s meets both
`¬ IoE eof` (`isEofOk`) and the readers' errors. (The old form, every pointer error in `IoE`, failed
here: `io.EOF` is one.) -/
theorem walDecEnv_eof_not (eof : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.io ∗ globalAddr _root_.Perennial.io.EOF ↦□ eof ⊢
      ⌜∀ pe : Loc, interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe ≠ eof⌝ := by
  iintro ⟨#Hio, #Heof⟩
  ihave #Hn := _root_.Perennial.io.eof_of_init $$ Hio
  iunfold _root_.Perennial.errors.newVar at Hn
  icases Hn with ⟨%x, #Hx, -⟩
  icombine Heof Hx gives %he
  ipureintro
  subst he
  intro pe h
  unfold interface.mkOk at h
  injection h with h
  injection h with h
  injection h with h
  rw [io.fs.PathError.ty.eq_1, _root_.Perennial.errors.errorString.ty.eq_1] at h
  injection h with h
  revert h; decide

/-- The program's area claim back. -/
theorem walAreaRes_close (jr : Ino) (N : NameSet) (h : NamesH) (cl : List (GoString × Claim))
    (Wn : List GoString) (hok : AreaOk N h cl Wn) :
    osNames (L := hG.goose_localGS) jr N (DFrac.own (1 : Qp).half) h ∗ walSplitFrag (W := W) Wn ∗
      areaCls (L := hG.goose_localGS) cl ⊢
      walAreaRes (L := hG.goose_localGS) jr := by
  unfold walAreaRes
  iintro ⟨Hn, Hs, Hc⟩
  iexists N, h, cl, Wn
  iframe
  ipureintro; exact ⟨hok.1, hok.2.1, hok.2.2.1, hok.2.2.2⟩

/-- The encoder's environment, from the package's initialization. -/
theorem wal_encEnv :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal -∗ encEnv (GF := GF) := by
  iintro #Hpkg
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨#Hbin, -, -, -, -, #Hsync, #Hproto, -, -, -, -, -, -, #Htime, -, -, -, -, -, -, -, -,
    -, -⟩
  ihave #Hw : (wal.walInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  ihave #Hm := wal.walInit_metrics $$ Hw
  iunfold encEnv
  iframe #
/-- `os`'s initialization, from the WAL package's. -/
theorem wal_osInit :
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal -∗
      isPkgInit (PROP := IProp GF) pkg_id.os := by
  iintro #Hpkg
  ihave #Hdeps := isPkgInit_unfold_deps pkg_id.go_etcd_io.etcd.server.v3.storage.wal $$ Hpkg
  isimp only [isPkgInitDeps] at Hdeps
  icases Hdeps with ⟨-, -, -, -, -, -, -, -, -, -, -, -, #Hos, -⟩
  iexact Hos

/-- `walReadTie`'s pure part, from the decoder's files and the segments' names. -/
theorem walReadTie_facts {dir : GoString} {write : Bool} {gs : List SegG} {fs : List (DecFile GF)}
    {fls lfs : List Loc} {hj : NamesH} (htie : WalDecTie dir write gs fs fls)
    (hll : lfs.length = gs.length) (hnm : ∀ g ∈ gs, hj.cur !! g.name = some (.file g.ino)) :
    fs.length = gs.length ∧ lfs.length = gs.length ∧ fls.length = gs.length ∧
      ∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
        F.bs = g.bs.map (·.1) ∧ hj.cur !! g.name = some (.file g.ino) ∧
        ∃ (f : Loc) (fd : w64), fls[k]? = some f ∧
          F.S = walFileS f fd (child dir g.name) (openFd g.ino (walReadFlag write)) g := by
  obtain ⟨h1, h2, h3⟩ := htie
  refine ⟨h1, hll, h2, fun k F g hF hg => ?_⟩
  obtain ⟨hb, f, fd, hf, hS⟩ := h3 k F g hF hg
  exact ⟨hb, hnm g (List.mem_of_getElem? hg), f, fd, hf, hS⟩

theorem osCallPerm_halves' :
    osCallPerm (L := hG.goose_localGS) 1 ⊢
      osCallPerm (L := hG.goose_localGS) (1 : Qp).half ∗ osCallPerm (L := hG.goose_localGS) (1 : Qp).half := by
  have h := osCallPerm_split (L := hG.goose_localGS) (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h.1

theorem walTmpsRes_split (j : Ino) :
    walTmpsRes (hG := hG) j ⊢ tmpClaim (hG := hG) j (pipeTmp 0) ∗ tmpClaim (hG := hG) j (pipeTmp 1) := by
  unfold walTmpsRes walTmps
  iintro ⟨H0, H1, -⟩
  iframe

/-- **The pipeline's names are outside the WAL directory's claim** (`walDirH`'s `walTmps ⊆ X`):
their claims, held whole, and the directory's share no name (`osNames_disj`). -/
theorem walTmpsRes_mem_except (R : Roots) (j : Ino) (X : List GoString) (dq : DFrac) (hj : NamesH) :
    ⊢ osSharedInv (GF := GF) R -∗ osNames j (.except X) dq hj -∗ walTmpsRes (hG := hG) j ={⊤}=∗
      ⌜∀ t ∈ walTmps, t ∈ X⌝ ∗ osNames j (.except X) dq hj ∗ walTmpsRes (hG := hG) j := by
  iintro #Hsi Hj Ht
  ihave ⟨Ht0, Ht1⟩ := walTmpsRes_split j $$ Ht
  have key : ∀ b, ⊢ osSharedInv (GF := GF) R -∗ osNames j (.except X) dq hj -∗ tmpClaim (hG := hG) j b
      ={⊤}=∗ ⌜b ∈ X⌝ ∗ osNames j (.except X) dq hj ∗ tmpClaim (hG := hG) j b := by
    intro b
    iintro #Hsi Hj Hb
    by_cases hb : b ∈ X
    · imodintro; iframe Hj Hb; ipureintro; exact hb
    · unfold tmpClaim
      icases Hb with ⟨%h, Hn, -⟩
      imod osNames_disj R j (.except X) (.only [b]) dq (DFrac.own 1) hj h b (by simp)
        (fun h' => hb h') (by simp [NameSet.Mem]) (fun _ _ => CoPset.mem_full) $$ Hsi Hj Hn with %hF
      exact hF.elim
  imod key (pipeTmp 0) $$ Hsi Hj Ht0 with ⟨%h0, Hj, Ht0⟩
  imod key (pipeTmp 1) $$ Hsi Hj Ht1 with ⟨%h1, Hj, Ht1⟩
  imodintro
  iframe Hj
  isplitr
  · ipureintro
    intro t ht
    simp only [walTmps, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact h0
    · exact h1
  unfold walTmpsRes walTmps
  rw [show pipeTmp 0 = go!"0.tmp" from rfl, show pipeTmp 1 = go!"1.tmp" from rfl]
  iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
  iframe Ht0
  iapply (BigSepL.bigSepL_cons (PROP := IProp GF)).2
  iframe Ht1
  iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
  iempintro

theorem go_etcd_io.etcd.server.v3.storage.wal.openAtIndex.wp_proof (Mr : WalMarshal)
    (hEnv : WalDecEnvSupply (GF := GF))
    (wp_IsEof : errors.IsPathErrnoEof.spec (GF := GF) (hG := hG))
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
  intro lg R jr r dir nm sp s write qp Q hin hnmO hr hdl
  wp_start as ⟨#Hzap, #Hok, Hp, Hres, Hperm, #Hsp, Hu, Hau⟩
  ihave #Hok' := Hok
  iunfold WalFs.walAreaOk at Hok'
  icases Hok' with ⟨#Hinv, #Hosi, #Hsi, %hrb⟩
  icases walAreaRes_open jr $$ Hres with ⟨%N, %h, %cl, %Wn, HN, Hsf, %hok, Hcl⟩
  have hnm := hin.1
  ihave %hlgn := zapLoggerOk_ne_null lg $$ Hzap
  try wp_auto
  rw [decide_eq_false hlgn]
  try wp_auto
  iapply wp_notCrashed_acc _ _ rfl
  iintro Hnc
  imod walInv_openAt walCodec Mr R jr r dir nm N _ h Wn write s.1 Q hin (hok.1 nm hnm)
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
    icases Hpin with ⟨%lay, %X, %hj, %hfacts, #Hkey, Hl, Htf, Ho, HS, Hj, Ht⟩
    obtain ⟨hljr, hX, hcoh, habs, hnd, hsn⟩ := hfacts
    icases Htf with ⟨Htf, Hnf⟩
    imod walInv_dirPath walCodec Mr R jr r dir lay.j X $$ Hinv Hnc Hnf Hkey with ⟨Hnc, Hnf, %qd, Hpd⟩
    ihave Htf : iprop(walTailsFrag (W := W) ∅ ∗ walNamesFrag (W := W) none) $$ [Htf Hnf]
    · iframe
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
      (by simp [hwl]) (by omega) (walOpenNames_ok (sint.nat kk) hX hsn hnmf hout hws)
      $$ [Hpd Hperm Hj Hws] as %rsl %lsl %clo %err2 ⟨Hpd, Hperm, Hj, Hws, Hopen⟩
    · iframe; iframe #
    icases Hopen with (⟨%frs, %lfs, ⟨%herr2, %hfl, %hll⟩, Hrsl, Hrc, Hlsl, Hlc, Hfiles⟩ | ⟨%e, %herr, #He⟩)
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
    ihave ⟨%fs, %fls, ⟨%htie, %hfr⟩, Hdf, Hlk⟩ := walDecFiles_mk wp_Stat wp_Size wp_FName wp_IsEof IoE hIo eof
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
    cases write
    · -- read mode
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
      iframe Hl Hperm
      unfold walReadH walOpenIn walReadTie
      isplitl [lg dir start]
      · iexists lg, sp'
        iframe
        iframe #
      iexists dec, IoE, eof, ueof, fs, lsl, lfs, null, clo, lay.j
      subst hdI
      iframe
      iframe #
      simp only [Bool.false_eq_true, ↓reduceIte]
      isplitr
      · ipureintro; exact hIoN
      isplitl [Ho Hlk]
      · iexists gs, fls
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
      ihave ⟨Hperm1, Hperm2⟩ := osCallPerm_halves' $$ Hperm
      imod walTmpsRes_mem_except R lay.j X _ hj $$ Hsi Hj Ht with ⟨%hXt, Hj, Ht⟩
      ihave ⟨Ht0, Ht1⟩ := walTmpsRes_split lay.j $$ Ht
      iapply wp_notCrashed_acc _ _ rfl
      iintro Hnc
      imod walInv_mintOpening walCodec Mr R jr r wl dir s $$ Hinv Hnc Hl with ⟨Hnc, Hop⟩
      imodintro
      iframe Hnc
      wp_apply wp_pipe lg dir (W64 64000000) R (DFrac.own qd) lay.j (by decide) (by decide) (by omega)
        (by decide) $$ [Hperm1 Hpd Ht0] as %fp ⟨%hfpn, %γ, #Hfp, Hmain⟩
      · iframe; iframe #
        unfold pipeRes
        iframe
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
      iframe dirFile Hop Hperm2
      unfold walReadH walOpenIn walReadTie
      isplitl [lg dir start]
      · iexists lg, sp'
        iframe
        iframe #
      rw [← hlfs]
      iexists dec, IoE, eof, ueof, fs, lsl, lfs, fp, func.nil, lay.j
      subst hdI
      iframe
      iframe #
      simp only [↓reduceIte]
      isplitr
      · ipureintro; exact hIoN
      isplitl [Ho Hlk]
      · iexists gs, fls
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
      · ipureintro; exact Nat.le_refl 0
      · ipureintro; exact hfpn

end proof

end EtcdGrove
end Perennial
