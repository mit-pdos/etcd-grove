/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__Get.lean (241f27e).
-/
/-
`raft.(*InmemStore).Get`'s spec: reads `st.bytes` at the key, with the client's stable-store
view `kvView` (the read lock paid for by the thread's `rtok`): a stored value is returned
as a read-only slice with a nil error; a missing key, or a stored nil slice (whose contents are
`[]`), gives `(nil, errors.New("not found"))`.

This is `isStableStore`'s `Get` with one difference, the found case: it does not assume the
contents are non-empty. A key `Set` to a non-nil empty slice is returned as found with `[]`
(the code tests `val == nil`, not `len(val) == 0`), which the contract's
`⌜st.bytes.lookup kb = some vb ∧ vb ≠ []⌝` case excludes and its not-found case does not cover
(see the report: the contract's `Get` is not provable as stated).
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
/-- `i.Get(key)`: `(val, nil)` for a stored `val`, else `(nil, errors.New("not found"))`. -/
abbrev github_com.hashicorp.raft.InmemStore.Get.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (st : StableAbs) (key : GoSlice) (kb : List w8) (tid : Nat),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      kvView γs st ∗ key ↦*□ kb ∗ rtok tid) -∗
    (kvView γs st -∗ rtok tid -∗
      ((∀ vb, ⌜st.bytes.lookup kb = some vb⌝ -∗
          ∀ s : GoSlice, s ↦*□ vb -∗ Φ (PairV #s #interface.nil)) ∧
       (⌜∀ vb, st.bytes.lookup kb = some vb → vb = []⌝ -∗
          ∀ err : GoInterface, isNotFoundErr err -∗ Φ (PairV #(Perennial.zero_val GoSlice) #err)))) -∗
    WP (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"Get")) (Val #key))
      {{ Φ }}

end spec

end Perennial
