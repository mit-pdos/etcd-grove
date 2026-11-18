/-
The package-initialization instances of `hash` and `hash/fnv` (standard-library packages
Perennial does not translate: the etcd project's names- and types-only translations), for every
package of this repository that imports them: mvcc (the type of `kvHasher`'s `hash` field), the
DaemonSet controller (`controller.ComputeHash`) and bbolt (`Meta.Sum64`). Moved out of
`storage/mvcc/Base.lean` and `k8s_io/kubernetes/Base.lean` (2026-11-03) so that bbolt can import
them alone: `IsPkgInit` must have one instance per package. Both facts are `True`.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.GeneratedProof.io
public import Perennial.Golang.Theory
public import Code.hash
public import Code.hash.fnv
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

namespace hash

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash :=
  define_is_pkg_init iprop(True)

end hash

namespace hash.fnv

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.hash.fnv :=
  define_is_pkg_init iprop(True)

end hash.fnv

end init

end Perennial
