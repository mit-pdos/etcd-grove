/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/countingReader__Read.lean (241f27e).
-/
/-
``(*countingReader).Read(p)``'s spec (stage 3, raft-internal, snap: package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.SnapDefs

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.gprot github_com.hashicorp.raft.proto

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

/-- `(*countingReader).Read(p)`: reads from its reader (a reader that never fails, `streamReaderOk`) and counts the bytes under its mutex: the inner reader's behaviour. -/
abbrev github_com.hashicorp.raft.countingReader.Read.spec : Prop :=
  ∀ (cr : Loc) (src : GoInterfaceOk) (R : List w8 → IProp GF) (eof : GoInterface) (p : GoSlice)
    (buf cs : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗
     countingReaderIs cr (GoInterface.ok src) ∗ streamReaderOk src R eof ∗ ⌜0 < buf.length⌝ ∗
     R cs ∗ p ↦* buf }}
    (App (Val (cr @!! go.GoType.PointerType countingReader.ty @!! go!"Read")) (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ⌜0 ≤ sint.Z n ∧ sint.nat n ≤ buf.length ∧ sint.nat n ≤ cs.length ∧
        (err = interface.nil ∨ (err = eof ∧ sint.nat n = cs.length))⌝ ∗
      p ↦* (cs.take (sint.nat n) ++ buf.drop (sint.nat n)) ∗ R (cs.drop (sint.nat n)) }}

end spec

end Perennial
