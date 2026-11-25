/-
The package fact of `path`: `True`. Shared by every tree that imports the package (membership's store
paths, k8s's `etcd3`, `Dsverify/`'s Rabia; L1, 2026-11-24: until then declared in membership's
`PkgInit.lean` and k8s's `etcd3/Base.lean`, and again in `Dsverify/`).
-/
module

public import GeneratedProof.path
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.errors.Base
public import Perennial.Proof.internal.bytealg.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace path

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.path :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.path :=
  build_get_is_pkg_init_wf

end def_

end path
end Perennial
