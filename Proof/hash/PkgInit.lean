/-
The package-initialization instance of `hash/fnv` (a standard-library package Perennial does not
translate: the etcd project's names- and types-only translation), for every package of this
repository that imports it: the DaemonSet controller (`controller.ComputeHash`) and bbolt
(`Meta.Sum64`); and, through `Perennial.Proof.hash.Base`, `hash`'s (Perennial's translation since its
pin b3f2fc485, for `crypto/sha1`; this repository's, types only, until 2026-11-24), for mvcc (the
type of `kvHasher`'s `hash` field) and the importers of `hash/fnv` and `hash/crc32`. Moved out of
`storage/mvcc/Base.lean` and `k8s_io/kubernetes/Base.lean` (2026-11-03) so that bbolt can import
them alone: `IsPkgInit` must have one instance per package. Both facts are `True`.
-/
module

public import GeneratedProof.hash.fnv
public import Perennial.Proof.hash.Base
public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.io

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

namespace hash.fnv

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash.fnv :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.hash.fnv :=
  build_get_is_pkg_init_wf

end hash.fnv

end init

end Perennial
