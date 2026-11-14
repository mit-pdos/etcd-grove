/- Lean-first (no Rocq counterpart).

# The member's raft-like fields (W4c U5)

What the operations generating the WAL calls need of the member's raft-like fields (`term`, `vote`,
`commit`, `base`, `last`, `terms`) so that no call they make panics: **the term is below `2^63`**
(`tEntWf`/`tOpWf` of the entries and snapshots they save, which take the member's term) and **so is every
term `terms` records** (`opOwnSnap`'s snapshot takes `terms[a]`): `tMemFields t M`. Nothing else: every
index computation is guarded by `last < maxIndex = 2^62` (`opEntries`, `opResend`, `opRecvSnap` return
first otherwise) or by an explicit comparison (`opCommit`'s `last > commit`, `opEntries`' `last > floor`),
and `save` asks nothing of the entries' indices against the WAL's history.

`tMemFields` is kept by every operation (`tMemFields_insert`/`_delete`; `opResend` raises the term to a
re-sent entry's, below `2^63` by `tEntWf`; `opTerm` raises it only below `2^62`). A restart's `resume` must
establish it: the read term below `2^63`, which the tester's history does not record yet (`tOpWf` bounds
no hard state); see `notes/wal-units/ops.md`.

`memSaveRes_post`: `save`'s successful postcondition gives `memSaveRes` back at the new oracle (the
persistent half kept from before the call: `memSaveRes_pers`).
-/
module

public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.MemberRep
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.OrLen

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProofMode github_com.mit_pdos.etcd_grove.examples.etcd.wal Fs WalFs

section pure
variable [GooseExts]

/-- Every term `terms` records is below `2^63`. -/
def tTermsOk (M : GMap w64 w64) : Prop := ∀ k x, M !! k = some x → uint.nat x < 2 ^ 63

/-- **The member's raft-like fields' facts**: the term and every recorded term below `2^63`. -/
def tMemFields (t : w64) (M : GMap w64 w64) : Prop := uint.nat t < 2 ^ 63 ∧ tTermsOk M

theorem tTermsOk_insert {M : GMap w64 w64} (hM : tTermsOk M) (k x : w64) (hx : uint.nat x < 2 ^ 63) :
    tTermsOk (<[k := x]> M) := by
  intro k' x' h
  rcases (GMap.lookup_insert_Some M k k' x x').1 h with ⟨-, rfl⟩ | ⟨-, h⟩
  · exact hx
  · exact hM k' x' h

theorem tTermsOk_delete {M : GMap w64 w64} (hM : tTermsOk M) (k : w64) : tTermsOk (GMap.delete k M) := by
  intro k' x' h
  rw [GMap.lookup_delete_iff] at h
  split at h
  · cases h
  · exact hM k' x' h

theorem tTermsOk_empty : tTermsOk (∅ : GMap w64 w64) := by
  intro k x h; simp at h

/-- A map whose every value is `t` or one of `M`'s. -/
def tTermsFrom (t : w64) (M M' : GMap w64 w64) : Prop := ∀ k x, M' !! k = some x → x = t ∨ M !! k = some x

theorem tTermsFrom_ok {t : w64} {M M' : GMap w64 w64} (h : tTermsFrom t M M') (ht : tMemFields t M) :
    tTermsOk M' := by
  intro k x hk
  rcases h k x hk with rfl | h
  · exact ht.1
  · exact ht.2 k x h

theorem tTermsFrom_refl (t : w64) (M : GMap w64 w64) : tTermsFrom t M M := fun _ _ h => Or.inr h

theorem tTermsFrom_insert {t : w64} {M M' : GMap w64 w64} (h : tTermsFrom t M M') (k : w64) :
    tTermsFrom t M (<[k := t]> M') := by
  intro k' x' hk
  rcases (GMap.lookup_insert_Some M' k k' t x').1 hk with ⟨-, rfl⟩ | ⟨-, hk⟩
  · exact Or.inl rfl
  · exact h k' x' hk

theorem tTermsFrom_delete {t : w64} {M M' : GMap w64 w64} (h : tTermsFrom t M M') (k : w64) :
    tTermsFrom t M (GMap.delete k M') := by
  intro k' x' hk
  rw [GMap.lookup_delete_iff] at hk
  split at hk
  · cases hk
  · exact h k' x' hk

end pure

section rep
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

/-- `memSaveRes`'s persistent part (the invariants and the WAL's persistent facts but the mark). -/
def memSavePers (W : WalGS GF) (e : TEnv) (γ : TGS) : IProp GF :=
  iprop(osInv (GF := GF) ∗ osSharedInv (GF := GF) e.R ∗ TInv (W := W) e γ ∗
      DurFs.durInv (GF := GF) γ.γd e.orFile ∗
      WalFs.walAreaOk (W := W) walCodec walRaftMr e.R e.jr (tArea e.root) ∗
      WalFs.walNamed (W := W) (tWalDir e.root))

instance memSavePers_persistent (W : WalGS GF) (e : TEnv) (γ : TGS) :
    Persistent (memSavePers (GF := GF) W e γ) := by
  unfold memSavePers; infer_instance

theorem memSaveRes_pers (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (v : oracle) (o os : TOracle)
    (c : TCand) (d : WalDur) (qc : Qp) :
    memSaveRes W e γ m w v o os c d qc ⊢ memSaveRes W e γ m w v o os c d qc ∗ memSavePers W e γ := by
  iintro H
  iunfold memSaveRes at H
  icases H with ⟨#H1, #H2, #H3, #H4, H5, H6, H7, H8, H9, H10, H11, H12, #H13, H14, #H15, #H16⟩
  isplitl
  · iunfold memSaveRes; iframe; iframe H1 H2 H3 H4 H13 H15 H16
  · iunfold memSavePers; iframe H1 H2 H3 H4 H13 H15

/-- **`save`'s success gives the member's resources back** at the new oracle, with the same
candidate. -/
theorem memSaveRes_post (W : WalGS GF) (e : TEnv) (γ : TGS) (m w : Loc) (o : TOracle) (c : TCand)
    (qc : Qp) (h : THs) (es : List TEnt) :
    memSavePers W e γ ∗ memSavePost W e γ m w o c qc h es true ⊢
      ∃ (v' : oracle) (os' : TOracle) (d' : WalDur),
        memSaveRes W e γ m w v' (tSaveO o h es) os' c d' qc ∗
        ⌜tMemOk (tSaveO o h es) c d' ∧ tMemHs (tSaveO o h es) d'⌝ := by
  iintro ⟨#Hp, Hpost⟩
  iunfold memSavePers at Hp
  icases Hp with ⟨#H1, #H2, #H3, #H4, #H13, #H15⟩
  iunfold memSavePost at Hpost
  simp only [↓reduceIte]
  icases Hpost with ⟨H6, H7, H8, H9, ⟨%v', H10, ⟨%os', H11⟩, ⟨%d', H12, H14, H16, %Hok, #H17⟩⟩⟩
  iexists v', os', d'
  isplitl
  · iunfold memSaveRes; iframe; iframe H1 H2 H3 H4 H13 H15 H17
  · ipureintro; exact Hok

end rep

end etcd_wal
end EtcdGrove
end Perennial
