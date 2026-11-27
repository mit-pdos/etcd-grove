/-
Log entries across the hraft kit transport (notes/dsv-hraft.md, S4): the sender's read-only raft
entries (`aeReq`'s `logPtr`s) as the contents a conversion copies (`logsOwn`, `entsMatch`), and the
receiver's fresh copies (`logsOwn` of a decoded request's conversion) as read-only raft entries again.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.rpctransport.Trans

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProofMode

namespace github_com.hashicorp.raft.examples.hraftnet.rpctransport

open github_com.hashicorp.raft github_com.hashicorp.raft.proto github_com.hashicorp.raft.gprot

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- The sender: `aeReq`'s entries (read-only `logPtr`s at indexes `prev+1..`) are read-only contents
`vs` matching `ents`. -/
theorem logPtrs_logsOwn (sl : GoSlice) (ptrs : List Loc) (prev : Nat) (ents : RLog) :
    sl ↦*□ ptrs ∗ ⌜ptrs.length = ents.length⌝ ∗
      ([∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr p (prev + 1 + j) e) ⊢
    ∃ vs : List EntV, logsOwn (GF := GF) sl DfracDiscarded vs ∗ ⌜entsMatch vs prev ents⌝ := by
  sorry

/-- The receiver: fresh entries (`fromAppendReq`'s, owned) matching `ents` become read-only
`logPtr`s, as `aeReq` asks. -/
theorem logsOwn_logPtrs (sl : GoSlice) (vs : List EntV) (prev : Nat) (ents : RLog)
    (h : entsMatch vs prev ents) :
    logsOwn (GF := GF) sl (DFrac.own 1) vs ⊢ |==> ∃ ptrs : List Loc, sl ↦*□ ptrs ∗
      ⌜ptrs.length = ents.length⌝ ∗
      ([∗list] j ↦ p ∈ ptrs, ∃ e, ⌜ents[j]? = some e⌝ ∗ logPtr p (prev + 1 + j) e) := by
  sorry

end lemmas

end github_com.hashicorp.raft.examples.hraftnet.rpctransport

end Perennial
