/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__DeleteRange.lean (241f27e).
-/
/-
`raft.(*InmemStore).DeleteRange`'s spec: logically atomic. The caller's atomic update sees the
log contents `L`, with `min` (≥ 2) inside it and `max` its last index, and gets
`L.take (min - 1)` back: the suffix from `min` is deleted. The linearization point is after the
deletion loop and the index fix-ups, inside the write critical section. As `isLogStore`'s
`DeleteRange` (without the durable-prefix premise).
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

open github_com.hashicorp.raft proto in
/-- `i.DeleteRange(min, max)` deletes the entries at `min..max` (stage 3: any range, a prefix by
compaction, everything by an install's discard, a suffix by a truncation), atomically; the last
index is some value afterwards (`min - 1`, wrapping when `min = 0`, or `0`); returns `nil`. -/
abbrev github_com.hashicorp.raft.InmemStore.DeleteRange.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (mn mx : w64),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      ⌜uint.nat mx < 2 ^ 64 - 1⌝) -∗
    (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, inmemLogs γs A ∗
      (∀ hi' : w64, inmemLogs γs (A.delete (uint.nat mn) (uint.nat mx) hi')
        ={∅,⊤ \ ↑storeN}=∗ Φ #interface.nil)) -∗
    WP (App (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"DeleteRange"))
      (Val #mn)) (Val #mx)) {{ Φ }}

end spec

end Perennial
