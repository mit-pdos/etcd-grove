/-
(hraft_robust R3) The spec of `disk.(*reader).bytes` (`codec.go`), on input that holds an encoding.
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
/-- `r.bytes()` on input that starts with `encBytes cs` returns a fresh copy of `cs` and leaves the rest. -/
abbrev github_com.hashicorp.raft.examples.hraftnet.disk.reader.bytes.spec : Prop :=
  ∀ (r : Loc) (cs rest : List w8), cs.length < 2 ^ 63 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
      readerSt r (encBytes cs ++ rest) }}
    (App (Val (r @!! go.GoType.PointerType reader.ty @!! go!"bytes")) (Val #()))
  {{ (o : GoSlice), RET #o; readerSt r rest ∗ o ↦* cs ∗ ownSliceCap w8 o (DFrac.own 1) }}

end spec

end Perennial
