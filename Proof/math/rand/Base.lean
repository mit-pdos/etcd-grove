/-
Package initialization instance of Go's `math/rand` (names only in Perennial; generated `Init.lean`
beside). Its fact is `True`. Lean-first (no Rocq counterpart). (Until 2026-10-27 in the gRPC
server's `v3rpc/Base.lean`, the watch slice's unit W-S: `GetProgressReportInterval`'s jitter; moved
here so that the model API server's proofs, `examples/k8sdaemonset/apimodel`, do not import the
server.)
-/
module

public import Perennial.Code.math.rand
public import Perennial.GeneratedProof.math.rand
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance mathRand_is_pkg_init_inst : IsPkgInit (IProp GF) pkg_id.math.rand :=
  define_is_pkg_init iprop(True)
instance mathRand_get_is_pkg_init_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.math.rand :=
  build_get_is_pkg_init_wf

end init

end Perennial
