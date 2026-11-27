/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/inproc/ReadAll.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
`snapstore.ReadAll`'s spec (stage 3).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft.examples.snapstore

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `ReadAll(r)` (stage 3; hr3's `Restore`, the transports) on a reader that never fails
(`streamReaderOk`, with `io.EOF`'s value `eof`) of the stream `b`: a fresh slice holding `b` and nil
(the stream is exhausted). -/
abbrev github_com.hashicorp.raft.examples.snapstore.ReadAll.spec : Prop :=
  ∀ (src : GoInterfaceOk) (R : List w8 → IProp GF) (b : List w8) (eof : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗
        globalAddr io.EOF ↦□ eof ∗ github_com.hashicorp.raft.streamReaderOk src R eof ∗ R b }}
      (App (Val (@! github_com.hashicorp.raft.examples.snapstore.ReadAll)) (Val #(GoInterface.ok src)))
    {{ (sl : GoSlice), RET (PairV #sl #interface.nil); sl ↦* b ∗ R [] }}

end spec

end Perennial
