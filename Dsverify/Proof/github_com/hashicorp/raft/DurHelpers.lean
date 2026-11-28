/-
(hraft_robust R4a) Helpers of the term, vote and follower proofs: namespace facts for the masks of
`srvDurInv` (`durN`) under the cells' openings, and

**`sync/atomic`'s `LoadUint64` and `StoreUint64` with a crash-token atomic update**:
Perennial's specs (`sync.atomic.LoadUint64.spec`, `StoreUint64.spec`) take a plain atomic update
(`|={⊤,∅}=>`), in which a client cannot open an invariant shared with later generations
(`srvDurInv`, `inv_nc_acc`). These are the same specs with `|NC={⊤,∅}=>`, proved as Perennial's are,
over the same models (`TrustedCode/sync/atomic.lean`: one byte atomic), with `wp_atomic_nc` at the
atomic step. A local workaround: the general change (the atomics' atomic updates as crash-token
updates, as the channels' are) belongs in Perennial (`notes/perennial-changes.md`).
-/
module

public import Perennial.Proof.sync.atomic.Link
public import Perennial.GooseLang.NotCrashed
public import Dsverify.Proof.github_com.hashicorp.raft.core.Helpers
public import Dsverify.Proof.github_com.hashicorp.raft.core.Crash

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : sync.atomic.Assumptions]

/-- `sync.atomic.LoadUint64` with a crash-token atomic update. -/
theorem sync.atomic.wp_LoadUint64_nc (addr : Loc) (dq : DFrac) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|NC={⊤,∅}=> ▷ ∃ v : w64, addr ↦{dq} v ∗ (addr ↦{dq} v ={∅,⊤}=∗ Φ #v)) -∗
      WP (App (Val (@! sync.atomic.LoadUint64)) (Val #addr)) {{ Φ }} := by
  wp_start as _
  iapply wp_atomic_nc _ _ rfl
  iintro Hnc
  imod HΦ $$ Hnc with ⟨Hnc, HΦ⟩
  iframe Hnc
  imodintro
  icases HΦ with ⟨%v, Haddr, HΦ⟩
  wp_apply_core wp_load_bytes_typed _ _ addr dq v $$ Haddr
  iintro Haddr
  iapply HΦ $$ Haddr

/-- `sync.atomic.StoreUint64` with a crash-token atomic update. -/
theorem sync.atomic.wp_StoreUint64_nc (addr : Loc) (v : w64) :
    ⊢ ∀ Φ : val → IProp GF, isPkgInit (PROP := IProp GF) pkg_id.sync.atomic -∗
      (|NC={⊤,∅}=> ▷ ∃ oldv : w64, addr ↦ oldv ∗ (addr ↦ v ={∅,⊤}=∗ Φ #())) -∗
      WP (App (App (Val (@! sync.atomic.StoreUint64)) (Val #addr)) (Val #v)) {{ Φ }} := by
  wp_start as _
  wp_bind (SwapBytes _ _ _)
  iapply wp_atomic_nc _ _ rfl
  iintro Hnc
  imod HΦ $$ Hnc with ⟨Hnc, HΦ⟩
  iframe Hnc
  imodintro
  icases HΦ with ⟨%oldv, Haddr, HΦ⟩
  wp_apply_core wp_swap_bytes_typed _ _ addr oldv v $$ Haddr
  iintro Haddr
  imod HΦ $$ Haddr with HΦ
  imodintro
  wp_pures
  iexact HΦ

end proof

namespace github_com.hashicorp.raft

open proto gprot

/-- Two distinct namespaces of raft are disjoint: `raftN.@x` stays inside `E` minus `raftN.@y`. -/
theorem raftN_sub_diff {x y : String} (hxy : x ≠ y) {E : CoPset} (h : (↑(raftN.@x) : CoPset) ⊆ E) :
    (↑(raftN.@x) : CoPset) ⊆ E \ ↑(raftN.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨h p hp, fun h' => ndot_ne_disjoint raftN hxy p ⟨hp, h'⟩⟩

/-- The protocol invariant's namespace stays inside `E` minus a namespace of raft. -/
theorem gprotN_sub_diff (y : String) {E : CoPset} (h : (↑gprotN : CoPset) ⊆ E) :
    (↑gprotN : CoPset) ⊆ E \ ↑(raftN.@y) := by
  intro p hp
  rw [LawfulSet.mem_diff]
  exact ⟨h p hp, fun h' => (LawfulSet.mem_diff.mp (gprotN_diff_raft y p hp)).2 h'⟩

theorem durN_diff_termN : (↑durN : CoPset) ⊆ ⊤ \ ↑termN :=
  raftN_sub_diff (by decide) (fun _ _ => CoPset.mem_full)
theorem durN_diff_cidxN : (↑durN : CoPset) ⊆ ⊤ \ ↑cidxN :=
  raftN_sub_diff (by decide) (fun _ _ => CoPset.mem_full)
theorem gprotN_diff_termN_durN : (↑gprotN : CoPset) ⊆ (⊤ \ ↑termN) \ ↑durN :=
  gprotN_sub_diff "dur" gprotN_diff_termN
theorem gprotN_diff_cidxN_durN : (↑gprotN : CoPset) ⊆ (⊤ \ ↑cidxN) \ ↑durN :=
  gprotN_sub_diff "dur" gprotN_diff_cidxN
theorem gprotN_diff_durN : (↑gprotN : CoPset) ⊆ ⊤ \ ↑durN := gprotN_diff_raft "dur"

end github_com.hashicorp.raft

end Perennial
