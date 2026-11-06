/-
The package-initialization instance of `reflect` (names-only in Perennial), for every package of
this repository that imports it: raft (`raftpb`'s `ConfState.Equivalent` calls `reflect.DeepEqual`),
the server's txn package (`util.go`'s `isNil`) and bbolt's freelist (`reflect.DeepEqual` in its
consistency checks). Its fact is `True`. Moved out of raft's and txn's `Base.lean` (2026-11-03):
`IsPkgInit` must have one instance per package. Its `wp_initialize'` is `Init.lean`.
-/
module

public import Perennial.Code.reflect
public import Perennial.Proof.ProofPrelude
public import Perennial.Golang.Theory

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

namespace reflect

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.reflect :=
  define_is_pkg_init iprop(True)
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.reflect :=
  build_get_is_pkg_init_wf

end reflect

end init

end Perennial
