/-
The package initialization instance of the standard library's `internal/byteorder` (Perennial does not
translate it; the k8s-apiserver project's `Code/internal/byteorder.toml` translates, with their bodies,
the big-endian stores `encoding/base64`'s decoder calls). Its fact is `True` (the package has no
variable). Lean-first (prove-authcrypto, 2026-11-21).
-/
module

public import GeneratedProof.internal.byteorder

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI

section init
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

namespace internal.byteorder

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.internal.byteorder :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.internal.byteorder :=
  build_get_is_pkg_init_wf

end internal.byteorder

end init

end Perennial
