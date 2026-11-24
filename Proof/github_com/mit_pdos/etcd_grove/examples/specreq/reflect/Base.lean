/-
The requirement snippets of `examples/specreq/reflect` (goose project `specreq-reflect`): their
package fact. Lean-first (no Rocq counterpart).

The snippets proved so far (reflect S0's typed-nil ones of `typednil.go`: `isNil`, `typedNilString`,
`MustPanicIsNilZeroValue`, `MustPanicIsNilStruct`) read no package variable: the fact is `True`.
-/
module

public import GeneratedProof.github_com.mit_pdos.etcd_grove.examples.specreq.reflect
public import Perennial.Proof.reflect.Base

@[expose] public section

noncomputable section

namespace Perennial
namespace github_com.mit_pdos.etcd_grove.examples.specreq.reflect

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst :
    IsPkgInit (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.specreq.reflect :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst :
    GetIsPkgInitWf (IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.specreq.reflect :=
  build_get_is_pkg_init_wf

end init

end github_com.mit_pdos.etcd_grove.examples.specreq.reflect
end Perennial
