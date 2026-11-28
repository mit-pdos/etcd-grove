/-
(hraft_robust R3) The spec of `disk.(*reader).uint64` (`codec.go`), on input that holds an encoding.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Codec

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

open github_com.hashicorp.raft.examples.hraftnet.disk in
/-- `r.uint64()` on input that starts with `encU64 x` returns `x` and leaves the rest. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.reader.uint64.spec : Prop :=
  ∀ (r : Loc) (x : w64) (rest : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      readerSt r (encU64 x ++ rest) }}
    (App (Val (r @!! go.GoType.PointerType reader.ty @!! go!"uint64")) (Val #()))
  {{ RET #x; readerSt r rest }}

end spec

end Perennial
