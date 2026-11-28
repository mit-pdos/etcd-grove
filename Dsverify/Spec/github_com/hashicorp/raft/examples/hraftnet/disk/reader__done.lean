/-
(hraft_robust R3) The spec of `disk.(*reader).done` (`codec.go`), on input that holds an encoding.
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
/-- `r.done()` on a fully read input returns nil. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.reader.done.spec : Prop :=
  ∀ (r : Loc),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      readerSt r [] }}
    (App (Val (r @!! go.GoType.PointerType reader.ty @!! go!"done")) (Val #()))
  {{ RET #interface.nil; readerSt r [] }}

end spec

end Perennial
