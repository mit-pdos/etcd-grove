/-
The package-initialization instances of `os` and `io/fs`, this repository's translations (project
bboltfs's, `Code/os.lean`, `Code/io/fs.lean`: names only but for the types and the functions the
Linux file extension osFsExt models), which every project translates against since 2026-11-03
(`os=`, `io/fs=` in `etc/goose.py`; until then raft, the server and the k8s packages used
Perennial's names-only `os`, which bbolt's `os.FileMode` fields cannot use). Here so that raft
(its default logger loads `os.Stderr`), bbolt and minibolt share them: `IsPkgInit` must have one
instance per package (moved out of raft's `Base.lean`).
-/
module

public import GeneratedProof.os
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors
public import Perennial.Proof.io
public import Proof.syscall.PkgInit

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace io.fs

/-- `io/fs`, types and names only: nothing is read of its initialization. -/
instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.io.fs :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.io.fs :=
  build_get_is_pkg_init_wf

end io.fs

namespace os

/-- `os`, names-only: its initialization is not modelled (its variables' initializers are
opaque, `Init.lean`), so this is what that initialization is assumed to give: `Stderr`
holds a fixed `*File`, which raft's initializer loads (`defaultLogger`). -/
instance os_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.os :=
  define_is_pkg_init iprop(∃ f : Loc, typedPointsto (globalAddr os.Stderr) f DFrac.discard)
instance os_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.os :=
  build_get_is_pkg_init_wf

end os

end init

end Perennial
