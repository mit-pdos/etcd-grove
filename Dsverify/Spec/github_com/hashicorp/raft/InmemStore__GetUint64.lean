/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__GetUint64.lean (241f27e).
-/
/-
`raft.(*InmemStore).GetUint64`'s spec: reads `st.ints` at the key (`0` if absent), with the
client's stable-store view `kvView` (the read lock paid for by the thread's `rtok`). As
`isStableStore`'s `GetUint64`.
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
/-- `i.GetUint64(key)` returns `(st.ints[key] or 0, nil)`. -/
abbrev github_com.hashicorp.raft.InmemStore.GetUint64.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (st : StableAbs) (key : GoSlice) (kb : List w8) (tid : Nat),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      kvView γs st ∗ key ↦*□ kb ∗ rtok tid) -∗
    (kvView γs st -∗ rtok tid -∗ Φ (PairV #((st.ints.lookup kb).getD (W64 0)) #interface.nil)) -∗
    WP (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"GetUint64")) (Val #key))
      {{ Φ }}

end spec

end Perennial
