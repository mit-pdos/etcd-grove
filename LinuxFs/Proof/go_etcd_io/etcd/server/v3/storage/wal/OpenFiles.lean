/- Lean-first (no Rocq counterpart).

# The decoder's files from the opened segments (W3/W5 of `notes/wal-fsext-plan.md`)

`openAtIndex` turns what `openWALFiles` returns (`walOpenedFile`, per opened name: the `*os.File`, its
fd and offset, the `*fileReader`, the lock) and the program's halves of the opened segments (taken out
of `walInv`'s `walParked`) into `NewDecoder`'s precondition (`decFile` of each reader, its stream state
at `[]`) and `walReadTie`'s per-file facts.

* `walDecFiles_mk`: by induction over the opened segments `gs` (their names `ns`, the readers `frs`, the
  locks `lfs`, by position), each file the bridge's `walDecFile` (`walDecFile_ok`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.ReadBridge

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Fs WalEnc

section files
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [W : WalGS GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [os_sem : os.Assumptions] [bufio_sem : _root_.Perennial.bufio.Assumptions]
variable [os.file.FieldAssumptions] [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

/-- The program's halves of a segment (what `walFileS` holds of it). -/
def segHalves (g : SegG) : IProp GF :=
  iprop(osMeta g.ino (DFrac.own (1 : Qp).half) g.om ∗ osBytes g.ino 0 (DFrac.own (1 : Qp).half) g.bs)

/-- **What the decoder's files are**, by position: the `k`-th reads the `k`-th segment `g` of `gs`
through the file `fls[k]` (`walFileS`), its bytes `g`'s values. -/
def WalDecTie (dir : GoString) (write : Bool) (gs : List SegG) (fs : List (DecFile GF))
    (fls : List Loc) : Prop :=
  fs.length = gs.length ∧ fls.length = gs.length ∧
    ∀ (k : Nat) (F : DecFile GF) (g : SegG), fs[k]? = some F → gs[k]? = some g →
      F.bs = g.bs.map (·.1) ∧ ∃ (f : Loc) (fd : w64), fls[k]? = some f ∧
        F.S = walFileS f fd (child dir g.name) (openFd g.ino (walReadFlag write)) g

theorem walDecTie_cons {dir : GoString} {write : Bool} {g : SegG} {gs : List SegG}
    {F : DecFile GF} {fs : List (DecFile GF)} {f : Loc} {fls : List Loc} (fd : w64)
    (hF : F.bs = g.bs.map (·.1) ∧
      F.S = walFileS f fd (child dir g.name) (openFd g.ino (walReadFlag write)) g)
    (h : WalDecTie dir write gs fs fls) : WalDecTie dir write (g :: gs) (F :: fs) (f :: fls) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by simp [h1], by simp [h2], fun k F' g' hF' hg' => ?_⟩
  cases k with
  | zero =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hF' hg'
    subst hF' hg'
    exact ⟨hF.1, f, fd, rfl, hF.2⟩
  | succ k =>
    simp only [List.getElem?_cons_succ] at hF' hg'
    obtain ⟨hb, f', fd', hf', hS⟩ := h3 k F' g' hF' hg'
    exact ⟨hb, f', fd', by simpa using hf', hS⟩

/-- **The decoder's files** (see the file header). -/
theorem walDecFiles_mk
    (wp_Stat : os.File.Stat.spec (GF := GF) (hG := hG))
    (wp_Size : os.fileStat.Size.spec (GF := GF) (hG := hG))
    (wp_Name : os.fileStat.Name.spec (GF := GF) (hG := hG))
    (IoE : GoInterface → Prop) (hIo : ∀ pe : Loc, IoE (interface.mkOk (go.GoType.PointerType io.fs.PathError.ty) #pe))
    (eof : GoInterface) (write : Bool) (dir : GoString) :
    ∀ (gs : List SegG) (frs : List GoInterfaceOk) (lfs : List Loc),
    frs.length = gs.length → lfs.length = gs.length →
    (∀ g ∈ gs, g.om.size = g.bs.length ∧ g.bs.length + 2 ^ 12 < 2 ^ 62) →
    osInv (GF := GF) ∗ globalAddr _root_.Perennial.io.EOF ↦□ eof ∗
      ([∗list] m ↦ i ∈ gs.map (·.ino), walOpenedFile write dir ((gs.map (·.name)).getD m []) i
        (frs.getD m ⟨go.GoType.PointerType go.string, #()⟩) (lfs.getD m null)) ∗
      ([∗list] g ∈ gs, segHalves g) ⊢
    ∃ (fs : List (DecFile GF)) (fls : List Loc), ⌜WalDecTie dir write gs fs fls ∧ fs.map (·.fr) = frs⌝ ∗
      ([∗list] F ∈ fs, decFile IoE eof F ∗ F.S []) ∗
      [∗list] k ↦ lf ∈ lfs, if write then fileutil.lockedFile lf (fls.getD k null) else ⌜lf = null⌝
  | [], frs, lfs, hfr, hlf, _ => by
    rw [List.length_eq_zero_iff.1 hfr, List.length_eq_zero_iff.1 hlf]
    iintro ⟨-, -, -, -⟩
    iexists [], []
    isplitr
    · ipureintro
      exact ⟨⟨rfl, rfl, fun k F g hF _ => by simp at hF⟩, rfl⟩
    isplitl
    · iapply BigSepL.bigSepL_nil.2; iempintro
    · iapply BigSepL.bigSepL_nil.2; iempintro
  | g :: gs, fr :: frs, lf :: lfs, hfr, hlf, hsz => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hfr hlf
    obtain ⟨hsz1, hlen1⟩ := hsz g (List.mem_cons_self ..)
    have ih := walDecFiles_mk wp_Stat wp_Size wp_Name IoE hIo eof write dir gs frs lfs hfr hlf
      (fun g' hg' => hsz g' (List.mem_cons_of_mem _ hg'))
    iintro ⟨#Hinv, #Heof, Hop, Hh⟩
    simp only [List.map_cons]
    icases BigSepL.bigSepL_cons.1 $$ Hop with ⟨H0, Hop⟩
    icases BigSepL.bigSepL_cons.1 $$ Hh with ⟨Hh0, Hh⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ]
    ihave ⟨%fs, %fls, %Ht, Hfs, Hls⟩ := ih $$ [Hop Hh]
    · iframe Hinv Heof Hh
      iexact Hop
    unfold walOpenedFile
    icases H0 with ⟨%f, %fd, %rl, Hf, Hfd, Ho, %hfd0, %hfr, #Hrl, Hlk⟩
    iexists walDecFile rl f fd (child dir g.name) (openFd g.ino (walReadFlag write)) g :: fs, f :: fls
    have hfr' : fr = ⟨go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.fileReader.ty, #rl⟩ := by
      have := hfr; unfold interface.mkOk at this; cases this; rfl
    isplitr
    · ipureintro
      refine ⟨walDecTie_cons fd ⟨rfl, rfl⟩ Ht.1, ?_⟩
      simp only [List.map_cons, Ht.2, hfr']
      rfl
    isplitl [Hfs Hf Hfd Ho Hh0]
    · iapply BigSepL.bigSepL_cons.2
      iframe Hfs
      isplitr
      · iapply (walDecFile_ok wp_Stat wp_Size wp_Name IoE hIo eof rl f fd (child dir g.name)
          (openFd g.ino (walReadFlag write)) g hfd0 rfl ?_ hsz1 hlen1)
        · cases write <;> rfl
        · iframe Hinv Heof Hrl
      simp only [walDecFile]
      iunfold walFileS
      unfold segHalves
      iframe
      ipureintro
      exact List.nil_prefix
    · iapply BigSepL.bigSepL_cons.2
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      iframe Hls
      cases write
      · simp only [Bool.false_eq_true, ↓reduceIte]
        iexact Hlk
      · simp only [↓reduceIte]
        iexact Hlk
  | _ :: _, [], _, hfr, _, _ => by simp at hfr
  | _ :: _, _ :: _, [], _, hlf, _ => by simp at hlf

end files

end WalFs
end EtcdGrove
end Perennial
