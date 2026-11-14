/-
**`tmpDirH j b h`**: the whole claim on the name `b` of `j` (its history `h`), `b` holding nothing or a
directory of files only, whose whole claim is held too, with its `.touch`'s file if any (`wal-leaf5`): what `fileutil.TouchDirAll`/`CreateDirAll` leave on
an error, and what `wal.Create` keeps of its temporary directory `nm.tmp` (a leftover's, `walAreaRes`;
`RemoveAll`'s). Moved here from `LinuxFs/Spec/.../wal/CreateCallees.lean` (`wal-leaf4`) so that the
fileutil specs can state their error posts with it. Lean-first.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateDefs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **What a temporary directory's entry `e` holds, owned**: nothing, or a directory of files, whose
whole claim is held, with what its `.touch` holds (nothing, or a file whole, `WalFs.tmpEnt`: a leftover
probe of `fileutil.IsDirWriteable`, which `CreateDirAll`'s probe truncates, `os.OpenFile.wp_truncS`
taking the file whole; ledger 2026-11-14, "a leftover `.touch` needs its file", adopted on `wal-leaf5`:
only `.touch`'s file, the one a callee changes; the other files are only unlinked, `RemoveAll`, which
needs none). -/
def tmpSub : Option Node → IProp GF
  | none => iprop(emp)
  | some (.file _) => iprop(False)
  | some (.dir J) => iprop(∃ hJ : NamesH, ⌜FilesOnly hJ.cur⌝ ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
      WalFs.tmpEnt (hJ.cur !! go!".touch"))

/-- **The whole of the name `b` of `j` (its claim's history `h`), holding nothing or a directory of
files** (whose whole claim is held). -/
def tmpDirH (j : Ino) (b : GoString) (h : NamesH) : IProp GF :=
  iprop(osNames j (.only [b]) (DFrac.own 1) h ∗ tmpSub (h.cur !! b))

end defs

end EtcdGrove
end Perennial
