/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/examples/snapstore/Store__Open.lean (241f27e).
-/
/-
`snapstore.Store.Open`'s spec (stage 3, package-internal).
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

/-- `st.Open(id)`: atomically, the latest's metadata and a reader over a copy of its bytes if its
id is `id`, else an error (`openPost`). -/
abbrev github_com.hashicorp.raft.examples.snapstore.Store.Open.spec : Prop :=
  ∀ (st : Loc) (γ : GName) (eof : GoInterface) (id : GoString) (Φ : val → IProp GF),
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.snapstore ∗ isStore st γ eof ∗
      (|={⊤,∅}=> ▷ ∃ old, ownLatest γ old ∗
        (ownLatest γ old ={∅,⊤}=∗ ∀ v : val, openPost old id eof v -∗ Φ v)) ⊢
    WP (App (Val (st @!! go.GoType.PointerType Store.ty @!! go!"Open")) (Val #id)) {{ Φ }}

end spec

end Perennial
