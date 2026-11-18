/-
The package-initialization instance of this repository's `syscall` (project bboltfs's translation,
`Code/syscall.lean`; Perennial has none), for the packages that import it (bbolt, minibolt). Its fact
is `True`: the initializer runs only untranslated initializers and `func init()`s, which nothing reads.
Its `wp_initialize'` is `Init.lean` (generated, `etc/gen-init.py`).
-/
module

public import Perennial.Proof.ProofPrelude
public import GooseLang.Ext.Fs.Impl
public import Perennial.GeneratedProof.sync
public import Perennial.Golang.Theory
public import Code.syscall
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base

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

namespace syscall

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.syscall :=
  define_is_pkg_init iprop(True)

end syscall

end init

end Perennial
