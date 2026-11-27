/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__SetUint64.lean (241f27e).
-/
/-
`raft.(*InmemStore).SetUint64`'s spec: sets `st.ints` at the key, with the client's stable-store
view `kvView` (the write lock needs no token). As `isStableStore`'s `SetUint64`.
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
/-- `i.SetUint64(key, v)` sets `st.ints[key] := v`; returns `nil`. -/
abbrev github_com.hashicorp.raft.InmemStore.SetUint64.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (st : StableAbs) (key : GoSlice) (kb : List w8) (v : w64),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      kvView γs st ∗ key ↦*□ kb) -∗
    (kvView γs { st with ints := st.ints.insert kb v } -∗ Φ #interface.nil) -∗
    WP (App (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"SetUint64")) (Val #key))
      (Val #v)) {{ Φ }}

end spec

end Perennial
