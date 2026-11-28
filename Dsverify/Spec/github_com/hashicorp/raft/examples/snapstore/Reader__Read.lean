/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/inproc/Reader__Read.lean (241f27e),
into snapstore (the `Reader` moved there: examples/snapstore/reader.go).
-/
/-
`snapstore.Reader.Read`'s spec (stage 3, package-internal).
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

/-- `rd.Read(p)` on a non-empty `p` (`streamReaderOk`'s `Read`): moves the first `n` bytes still to
come into `p` and returns `(n, nil)`, or returns `(0, io.EOF)` at the end. -/
abbrev github_com.hashicorp.raft.examples.snapstore.Reader.Read.spec : Prop :=
  ∀ (rd : Loc) (p : GoSlice) (buf cs : List w8) (eof : GoInterface),
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ globalAddr io.EOF ↦□ eof ∗
        readerSt rd cs ∗ p ↦* buf ∗ ⌜0 < buf.length⌝ }}
      (App (Val (rd @!! go.GoType.PointerType Reader.ty @!! go!"Read")) (Val #p))
    {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
        ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ buf.length ∧ sint.nat n ≤ cs.length ∧
          (err = interface.nil ∨ (err = eof ∧ sint.nat n = cs.length))⌝ ∗
        p ↦* (cs.take (sint.nat n) ++ buf.drop (sint.nat n)) ∗ readerSt rd (cs.drop (sint.nat n)) }}

end spec

end Perennial
