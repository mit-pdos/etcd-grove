/-
The package fact of `container/heap` (names only in this repository's translation): `True`. Shared by
every tree that imports the package (the lease's proofs, `Dsverify/`'s Rabia; L1, 2026-11-24: until then
declared in `Proof/go_etcd_io/etcd/server/v3/lease/Base.lean`, and again in `Dsverify/`).
-/
module

public import GeneratedProof.container.heap
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sort.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace container.heap

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.container.heap :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.container.heap :=
  build_get_is_pkg_init_wf

end def_

end container.heap
end Perennial
