/-
The package-initialization instance of this repository's `golang.org/x/sys/unix` (project bboltfs's
translation, `Code/golang_org/x/sys/unix.lean`), for the packages that import it (bbolt). Its fact is
`True`: the initializer runs only untranslated initializers, which nothing reads, and `syscall`'s.
Its `wp_initialize'` is `Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Fs.Impl
public import Perennial.GeneratedProof.sync
public import Perennial.Golang.Theory
public import Code.syscall
public import Code.golang_org.x.sys.unix
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

namespace golang_org.x.sys.unix

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.golang_org.x.sys.unix :=
  define_is_pkg_init iprop(True)

end golang_org.x.sys.unix

end init

end Perennial
