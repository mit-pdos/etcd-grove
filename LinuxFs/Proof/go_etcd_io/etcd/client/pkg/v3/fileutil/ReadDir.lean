/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/client/pkg/v3/fileutil/ReadDir.lean`: **`sorry`** (not
done: the two loops, `applyOpts` over the option closures and the extension filter). Its callees:
`os.Open.wp_dirS`, `File.Readdirnames.wp_dirS`, `File.Close.wp_dirS` (proved, `NsS.lean`),
`sort.Strings.spec` (Perennial's, proved there) and `filepath.Ext.spec` (proved in the part).
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir
public import LinuxFs.Spec.path.filepath.Ext
public import Perennial.Spec.sort.Strings

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Fs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]

theorem go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.wp_proof
    (wp_Strings : sort.Strings.spec (GF := GF) (hG := hG))
    (wp_Ext : filepath.Ext.spec (GF := GF) (hG := hG)) :
    go_etcd_io.etcd.client.pkg.v3.fileutil.ReadDir.spec (GF := GF) (hG := hG) := by
  sorry

end proof

end EtcdGrove
end Perennial
