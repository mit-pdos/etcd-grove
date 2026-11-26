/-
The lemmas of `openAtIndex.lean`'s proof (`walLay_nameFmt`, `WalDecEnvSupply`, `wal_osInit`, ...), in a
module of their own so that `validSnapshotEntriesPinned.lean` and `openLastHeld.lean` import them
without the proof (import tiers, 2026-11-18).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.wal.openAtIndex
public import Spec.go_etcd_io.etcd.server.v3.storage.wal.selectWALFiles
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.selectWALFilesLemmas
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
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.NameClaims
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CutSynced
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.SegSize
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadState
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreatePre

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
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
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
        ∃ (f : Loc) (fd : w64) (lo lk : Option Bool), fls[k]? = some f ∧
          F.S = walFileS f fd (child dir g.name) (walSegFd write lo lk g.ino) g := by
  obtain ⟨h1, h2, h3⟩ := htie
  refine ⟨h1, hll, h2, fun k F g hF hg => ?_⟩
  obtain ⟨hb, f, fd, lo, lk, hf, hS⟩ := h3 k F g hF hg
  exact ⟨hb, hnm g (List.mem_of_getElem? hg), f, fd, lo, lk, hf, hS⟩

theorem osCallPerm_halves' (k : GoString) :
    osCallPerm (L := hG.goose_localGS) k 1 ⊢
      osCallPerm (L := hG.goose_localGS) k (1 : Qp).half ∗ osCallPerm (L := hG.goose_localGS) k (1 : Qp).half := by
  have h := osCallPerm_split (L := hG.goose_localGS) k (1 : Qp).half (1 : Qp).half
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
      imod osNames_disj R j (.except X) (.only [b]) dq (DFrac.own qTmp) hj h b (by simp)
        (fun h' => hb h') (by simp [NameSet.Mem]) (fun _ _ => CoPset.mem_full) $$ Hsi Hj Hn with %hF
      exact hF.elim
  imod key (pipeTmp 0) $$ Hsi Hj Ht0 with ⟨%h0, Hj, Ht0⟩
  imod key (pipeTmp 1) $$ Hsi Hj Ht1 with ⟨%h1, Hj, Ht1⟩
  imodintro
  iframe Hj
  isplitr
  · ipureintro
    intro t ht
    simp only [walTmps, List.mem_cons, List.not_mem_nil, _root_.or_false] at ht
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

end proof

end EtcdGrove
end Perennial
