/- Lean-first (no Rocq counterpart).

# A whole claim on a pipeline name (`N.tmp`) of a WAL directory

`tmpClaim j b` (moved here from `Pipe.lean`, so that `walInv`'s parked resources, `Inv.lean`, can
name it without importing the pipeline): the whole claim on the name `b` of the directory `j`, with
what it holds (nothing, or a leftover file whole, `trFile`; never a directory). `walTmpsRes j`: both
pipeline names of `j` (`walTmps`), what `walInv` parks for each WAL directory without a write-mode
handle (W3/W5's gap 3, `notes/wal-fsext-plan.md`).
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.Cut
public import LinuxFs.Spec.os.OpenFileTruncS

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

/-- What a name of the pipeline holds, owned with its claim: nothing, or a file, whole (`trFile`:
a leftover `N.tmp`, which `alloc`'s `O_TRUNC` open takes whole, `os.OpenFile.wp_truncS`); never a
directory. -/
def tmpEnt : Option Node → IProp GF
  | none => iprop(emp)
  | some (.file i) => trFile i False
  | some (.dir _) => iprop(False)

/-- **A whole claim on the name `b` of the directory `j`, holding no directory**, with what it holds
(absent or a file: `alloc`'s `O_CREAT|O_TRUNC` open makes it a fresh, empty file either way). -/
def tmpClaim (j : Ino) (b : GoString) : IProp GF :=
  iprop(∃ h : NamesH, osNames j (.only [b]) (DFrac.own 1) h ∗ tmpEnt (h.cur !! b))

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

end defs

end WalFs
end EtcdGrove
end Perennial

end
