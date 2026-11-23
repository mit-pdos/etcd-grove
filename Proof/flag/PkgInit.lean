/-
The package fact of `flag` (this repository's translation, project etcd's: `Code/flag.toml`, names
only but for its initializers, `init` and `NewFlagSet`): no fact (featuregate-3, 2026-11-23:
featuregate imports `flag` only for `MutableFeatureGate.AddFlag`'s `*flag.FlagSet`, which nothing
verified calls).
-/
module

public import GeneratedProof.flag
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.fmt.Base
public import Proof.os.PkgInit

@[expose] public section

set_option linter.iris.dupNamespace false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace flag

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.flag :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.flag :=
  build_get_is_pkg_init_wf

end flag

end init

end Perennial
