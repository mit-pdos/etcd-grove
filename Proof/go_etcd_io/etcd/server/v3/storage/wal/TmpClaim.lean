/- Lean-first (no Rocq counterpart).

# A whole claim on a pipeline name (`N.tmp`) of a WAL directory

`tmpClaim j b` (moved here from `Pipe.lean`, so that `walInv`'s parked resources, `Inv.lean`, can
name it without importing the pipeline): the whole claim on the name `b` of the directory `j`, with
what it holds (nothing, or a leftover file whole, `trFile`; never a directory). `walTmpsRes j`: both
pipeline names of `j` (`walTmps`), what `walInv` parks for each WAL directory without a write-mode
handle (W3/W5's gap 3, `notes/wal-fsext-plan.md`).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.wal.Cut
public import Spec.os.OpenFileTruncS
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.HistFo
public import GooseLang.Ext.Fs.TreeCommit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Fs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The program's fraction of a pipeline name's claim** (`tmpClaim`): three quarters, so that two
of them on one name contradict (`Close`'s put-back of both names, `tmpClaims_walTmpsRes`). -/
abbrev qTmp : Qp := (1 : Qp).half + (1 : Qp).half.half

/-- **The WAL invariant's fraction of a pipeline name's claim** (`tmpHalf`): a quarter. -/
abbrev qTmpI : Qp := (1 : Qp).half.half

theorem qTmp_add : qTmp + qTmpI = 1 := by
  apply Subtype.ext
  show (1 : Rat) / 2 + (1 : Rat) / 2 / 2 + (1 : Rat) / 2 / 2 = 1
  grind

theorem qTmp_two : ¬ (qTmp + qTmp ≤ 1) := by
  intro h
  have h' : ((1 : Rat) / 2 + (1 : Rat) / 2 / 2 + ((1 : Rat) / 2 + (1 : Rat) / 2 / 2)) ≤ 1 := h
  grind

/-- What a name of the pipeline holds, owned with its claim: nothing, or a file, whole (`trFile`:
a leftover `N.tmp`, which `alloc`'s `O_TRUNC` open takes whole, `os.OpenFile.wp_truncS`); never a
directory. -/
def tmpEnt : Option Node → IProp GF
  | none => iprop(emp)
  | some (.file i) => trFile i False
  | some (.dir _) => iprop(False)

/-- **The program's half of the claim on the name `b` of the directory `j`, holding no directory**,
with what it holds (absent or a file: `alloc`'s `O_CREAT|O_TRUNC` open makes it a fresh, empty file
either way). The other half is the WAL invariant's (`tmpHalf`, in `walTmpParked`), or, before
`Create`'s commit, `Create`'s: a step on the name opens the invariant (`walTmp_osAUnc`). -/
def tmpClaim (j : Ino) (b : GoString) : IProp GF :=
  iprop(∃ h : NamesH, osNames j (.only [b]) (DFrac.own qTmp) h ∗ tmpEnt (h.cur !! b))

/-- **The invariant's half of the claim on the pipeline name `b` of `j`** (step 2 (B) of
`notes/wal-units/tester.md`): with a commit bound `n0` reached, at which no version of the history a
crash may leave holds a directory at `b` (`HistFoP`), so that after a crash the WAL directory's
pipeline names hold no directory (`BootFoRest`'s first part, `walInv_crash`). -/
def tmpHalf (j : Ino) (b : GoString) : IProp GF :=
  iprop(∃ (h : NamesH) (n0 : Nat), osNames j (.only [b]) (DFrac.own qTmpI) h ∗
    osCommitLb n0 ∗ ⌜HistFoP (fun _ => True) n0 j (.only [b]) h⌝)

/-- Both pipeline names' invariant halves. -/
def walTmpsHalf (j : Ino) : IProp GF :=
  iprop([∗list] b ∈ walTmps, tmpHalf j b)

/-- **Both pipeline names of the WAL directory `j`** (`0.tmp`, `1.tmp`), each claimed whole: what
`walInv` parks for a WAL without a write-mode handle (`walParked`), what `Open` hands the pipeline
and its handle, what `Close` puts back. -/
def walTmpsRes (j : Ino) : IProp GF :=
  iprop([∗list] b ∈ walTmps, tmpClaim j b)

instance tmpEnt_timeless (o : Option Node) : Timeless (tmpEnt (GF := GF) o) := by
  unfold tmpEnt trFile mcellsAny cellsR osMeta osBytes
  split <;> infer_instance

instance tmpClaim_timeless (j : Ino) (b : GoString) : Timeless (tmpClaim (GF := GF) j b) := by
  haveI : ∀ (j : Ino) (N : NameSet) (q : DFrac) (h : NamesH), Timeless (osNames (GF := GF) j N q h) :=
    fun _ _ _ _ => by unfold osNames; split <;> infer_instance
  unfold tmpClaim; infer_instance

instance walTmpsRes_timeless (j : Ino) : Timeless (walTmpsRes (GF := GF) j) := by
  unfold walTmpsRes; infer_instance

instance tmpHalf_timeless (j : Ino) (b : GoString) : Timeless (tmpHalf (GF := GF) j b) := by
  haveI : ∀ (j : Ino) (N : NameSet) (q : DFrac) (h : NamesH), Timeless (osNames (GF := GF) j N q h) :=
    fun _ _ _ _ => by unfold osNames; split <;> infer_instance
  unfold tmpHalf; infer_instance

instance walTmpsHalf_timeless (j : Ino) : Timeless (walTmpsHalf (GF := GF) j) := by
  unfold walTmpsHalf; infer_instance

end defs

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- A whole claim as the program's three quarters and the invariant's quarter. -/
theorem osNames_tmpSplit (j : Ino) (N : NameSet) (h : NamesH) :
    osNames (GF := GF) j N (DFrac.own 1) h ⊣⊢
      osNames j N (DFrac.own qTmp) h ∗ osNames j N (DFrac.own qTmpI) h := by
  have e := osNames_frac (L := hG.goose_localGS) j N qTmp qTmpI h
  rw [qTmp_add] at e
  exact e

/-- **A whole claim on a pipeline name, split**: the program's half (`tmpClaim`) and the invariant's
(`tmpHalf`), given a commit bound with the claim's fact. -/
theorem tmpWhole_split (j : Ino) (b : GoString) (h : NamesH) (n0 : Nat)
    (hf : HistFoP (fun _ => True) n0 j (.only [b]) h) :
    osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∗ tmpEnt (h.cur !! b) ∗ osCommitLb n0 ⊢
      tmpClaim j b ∗ tmpHalf j b := by
  iintro ⟨Hn, He, #Hc⟩
  icases (osNames_tmpSplit j (.only [b]) h).1 $$ Hn with ⟨H1, H2⟩
  isplitl [H1 He]
  · unfold tmpClaim; iexists h; iframe
  · unfold tmpHalf; iexists h, n0; iframe; iframe #; ipureintro; exact hf

/-- **The two halves of a pipeline name's claim, joined**: the whole claim, with what it holds. -/
theorem tmpClaim_join (j : Ino) (b : GoString) :
    tmpClaim (GF := GF) j b ∗ tmpHalf j b ⊢
      ∃ h : NamesH, osNames j (.only [b]) (DFrac.own 1) h ∗ tmpEnt (h.cur !! b) := by
  unfold tmpClaim tmpHalf
  iintro ⟨⟨%h, H1, He⟩, ⟨%h', %n0, H2, -, -⟩⟩
  icases osNames_agree j (.only [b]) _ _ h h' $$ H1 H2 with %e
  subst e
  iexists h
  iframe He
  iapply (osNames_tmpSplit j (.only [b]) h).2 $$ [$H1 $H2]

end laws

end WalFs
end EtcdGrove
end Perennial

end
