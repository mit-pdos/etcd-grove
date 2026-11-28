/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Spec/github_com/hashicorp/raft/InmemStore__StoreLogs.lean (241f27e).
-/
/-
`raft.(*InmemStore).StoreLogs`'s spec: logically atomic. The caller's atomic update sees the log
contents `L` (with the stored entries starting right after it, `|L| + 1 = first`) and gets
`L ++ es` back; the store's linearization point is after the insertion loop, inside the write
critical section. The entries are passed as pointers with persistent `logPtr` facts (never
written again), as `isLogStore`'s `StoreLogs` (without the durable-prefix premise).
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
/-- `i.StoreLogs(sl)` inserts the entries `es` (pointed to by `ptrs`, at indexes `first..`),
atomically (stage 3: the contents are a partial map, `LogAbs`; the last index written is raised);
returns `nil`. -/
abbrev github_com.hashicorp.raft.InmemStore.StoreLogs.spec : Prop :=
  ∀ (γs : InmemNames) (i : Loc) (sl : GoSlice) (dq : DFrac) (ptrs : List Loc) (first : Nat)
    (es : RLog),
  ⊢ ∀ Φ : val → IProp GF,
    iprop(isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isInmemStore γs i ∗
      ⌜ptrs.length = es.length ∧ first + es.length ≤ 2 ^ 64⌝ ∗ sl ↦*{dq} ptrs ∗
      ([∗list] k ↦ p ∈ ptrs, ∃ e, ⌜es[k]? = some e⌝ ∗ logPtr p (first + k) e)) -∗
    (|NC={⊤ \ ↑storeN,∅}=> ▷ ∃ A, inmemLogs γs A ∗
      (inmemLogs γs (A.store first es) ={∅,⊤ \ ↑storeN}=∗ (sl ↦*{dq} ptrs -∗ Φ #interface.nil))) -∗
    WP (App (Val (i @!! go.GoType.PointerType InmemStore.ty @!! go!"StoreLogs")) (Val #sl))
      {{ Φ }}

end spec

end Perennial
