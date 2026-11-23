/-
Specs of `message`'s internal functions that its proofs take as hypotheses of one another (CLAUDE.md,
"Import tiers": a proof sees a sibling through its spec): `BufRead.specB` (`BufRead` with the
payload's bound, for `ReadUnmarshal`) and `BufWrite.specTooLong` (`BufWrite` on data too long, for
`MarshalWriteFlush`), out of the proof files `BufRead.lean` and `BufWrite.lean`.
-/
module

public import Dsverify.Proof.rabia.internal.message.FrameDeps

@[expose] public section

noncomputable section

namespace Perennial.rabia.internal.message

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : rabia.internal.message.Assumptions]

/-- `BufRead.spec` with the payload's bound (the header is a `uint32`): internal, for
`ReadUnmarshal` (`frameIs` speaks of payloads below `2^32`). -/
abbrev BufRead.specB : Prop :=
  ∀ (br : Loc) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → IProp GF) (R : List w8) (sl : GoSlice) (ds : List w8),
  {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗
      EtcdGrove.bufio.ownBufReader br ri connPre S E R ∗ sl ↦* ds }}
    (App (App (Val (@! BufRead)) (Val #br)) (Val #sl))
  {{ (n : w64) (e : GoInterface), RET (PairV #n #e);
      (⌜e = interface.nil⌝ ∗ ∃ bs, ⌜n = W64 bs.length ∧ bs.length ≤ ds.length ∧
          bs.length < 2 ^ 32⌝ ∗
        sl ↦* (bs ++ ds.drop bs.length) ∗
        EtcdGrove.bufio.ownBufReader br ri connPre S E (R ++ frame bs)) ∨
      (⌜e ≠ interface.nil⌝ ∗ ∃ (R' ds' : List w8), ⌜R <+: R'⌝ ∗ sl ↦* ds' ∗
        EtcdGrove.bufio.ownBufReader br ri connPre S E R') }}

/-- `BufWrite` on data of `2^32` bytes or more (N8): a non-nil error, nothing written (the writer
is not touched). -/
abbrev BufWrite.specTooLong : Prop :=
  ∀ (bw : Loc) (sl : GoSlice) (dq : DFrac) (bs : List w8),
    2 ^ 32 ≤ bs.length →
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.internal.message ∗ sl ↦*{dq} bs }}
      (App (App (Val (@! BufWrite)) (Val #bw)) (Val #sl))
    {{ (e : GoInterface), RET #e; ⌜e ≠ interface.nil⌝ ∗ sl ↦*{dq} bs }}

end spec

end Perennial.rabia.internal.message
