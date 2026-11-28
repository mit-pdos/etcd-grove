/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Store__List.lean (241f27e).
-/
/-
`snapstore.Store.List`'s spec (stage 3, package-internal).
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.snapstore.Base

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std
open github_com.hashicorp.raft github_com.hashicorp.raft.examples.snapstore

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.snapstore.Assumptions]

/-- `st.List()`: atomically, the latest's metadata (0 or 1 pointers). -/
abbrev github_com.hashicorp.raft.examples.snapstore.Store.List.spec : Prop :=
  ∀ (st : Loc) (γ : GName) (eof : GoInterface) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ isStore st γ eof ∗
      (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ old, ownLatest γ old ∗
        (ownLatest γ old ={∅,⊤ \ ↑storeN}=∗ ∀ (sl : GoSlice) (ps : List Loc),
          sl ↦* ps -∗
          (match old with
            | none => iprop(⌜ps = []⌝)
            | some (m, _) => iprop(∃ p : Loc, ⌜ps = [p]⌝ ∗ p ↦ m)) -∗
          Φ (PairV #sl #interface.nil))) ⊢
    WP (App (Val (st @!! go.GoType.PointerType Store.ty @!! go!"List")) (Val #())) {{ Φ }}

end spec

end Perennial
