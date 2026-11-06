/-
The package-initialization instance of this repository's `golang.org/x/sys/unix` (project bboltfs's
translation, `Code/golang_org/x/sys/unix.lean`), for the packages that import it (bbolt). Its fact is
`True`: the initializer runs only untranslated initializers, which nothing reads, and `syscall`'s.
Its `wp_initialize'` is `Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import GeneratedProof.golang_org.x.sys.unix
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
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.golang_org.x.sys.unix :=
  build_get_is_pkg_init_wf

end golang_org.x.sys.unix

end init

end Perennial
