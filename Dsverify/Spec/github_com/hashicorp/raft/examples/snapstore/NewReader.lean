/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/inproc/NewReader.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
`snapstore.NewReader`'s spec (stage 3).
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

/-- `NewReader(b)` (stage 3; `snapstore`'s `Open`, the transports): a `*Reader` over a
copy of the bytes `b` (`b` left as it was): a reader that never fails (`streamReaderOk`, with
`io.EOF`'s value `eof`), whose `Close` returns nil (`readCloserOk`), at the start of the stream, and
whose dynamic type is not an `io.WriterTo`. -/
abbrev github_com.hashicorp.raft.examples.snapstore.NewReader.spec : Prop :=
  ∀ (sl : GoSlice) (dq : DFrac) (b : List w8) (eof : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗
        globalAddr io.EOF ↦□ eof ∗ sl ↦*{dq} b }}
      (App (Val (@! github_com.hashicorp.raft.examples.snapstore.NewReader)) (Val #sl))
    {{ (rd : Loc), RET #rd; sl ↦*{dq} b ∗
        ∃ R : List w8 → IProp GF,
          github_com.hashicorp.raft.readCloserOk
            ⟨go.GoType.PointerType Reader.ty, #rd⟩ R eof ∗ R b ∗
          ⌜go.typeSetContains (go.GoType.PointerType Reader.ty) io.WriterTo.ty = false⌝ }}

end spec

end Perennial
