/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__Set.lean (241f27e).
-/
/-
`raft.(*InmemStore).Set`'s spec: sets `st.bytes` at the key to the contents of a read-only
slice, with the client's stable-store view `kvView`. As `isStableStore`'s `Set`.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.InmemStoreBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]

open github_com.hashicorp.raft in
/-- `i.Set(key, val)` sets `st.bytes[key] := val`'s contents; returns `nil`. -/
abbrev github_com.hashicorp.raft.InmemStore.Set.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (key vs : GoSlice) (kb vb : List w8),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      key ↦*□ kb ∗ vs ↦*□ vb) -∗
    (|NC={⊤,∅}=> ▷ ∃ st, kvView γs st ∗
      (kvView γs { st with bytes := st.bytes.insert kb vb } ={∅,⊤}=∗ Φ #interface.nil)) -∗
    WP (App (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"Set")) (Val #key))
      (Val #vs)) {{ Φ }}

end spec

end Perennial
