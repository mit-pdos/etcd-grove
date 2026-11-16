/- Lean-first (no Rocq counterpart).

# `Repair`'s small facts (W7 of `notes/wal-fsext-plan.md`; the W7-W12 log, fourteenth session)

* `repairFile_unique`: the records a `RepairFile` reads are determined by the bytes (the reader is a
  function): the decoder loop's `RepairFile` (from `walLastOpen`'s layout) and the registration's (from the
  layout `walInvRegisterPendLaw` hands out) are the same, so `LastOffset()` at the truncation is the
  registered tail's write position.
* The `.broken` name: `f.Name() + ".broken"` is `child dir (gL.name ++ ".broken")`, a valid name ending in
  `.wal.broken` (`walNameP_broken`: no `.wal` name).
* `walInvBody_keyExcl`/`walInv_keyExcl`: a WAL directory's key `walDirKey dir j X` says `X` holds no
  `.wal.broken` name (`DirClaimsOk`'s `DirClaimExcl`), so the `.broken` name is in the claim `.except X`.
* `WalOut.delClaim_addClaim`: a pseudo-key lent and given back leaves the record as it was.
-/
module

public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.RepairDecode
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.BrokenLend

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace Perennial
namespace EtcdGrove
namespace WalFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs WalEnc

section pure
variable [GooseExts]

/-- **A `RepairFile`'s records are the bytes'** (see the file header). -/
theorem repairFile_unique {C : WalCodec} (hC : C.Ok) {bs : List w8} {rs rs' : List WalRec}
    (hf : RepairFile C bs rs) (hf' : RepairFile C bs rs') : rs = rs' := by
  suffices h : ∀ (n : Nat) (xs ys ys' : List WalRec), ys.length + ys'.length ≤ n →
      rs = xs ++ ys → rs' = xs ++ ys' → ys = ys' by
    exact h _ [] rs rs' (Nat.le_refl _) rfl rfl
  intro n
  induction n with
  | zero =>
    intro xs ys ys' hl _ _
    have e1 : ys = [] := List.length_eq_zero_iff.1 (by omega)
    have e2 : ys' = [] := List.length_eq_zero_iff.1 (by omega)
    rw [e1, e2]
  | succ n ih =>
    intro xs ys ys' hl h1 h2
    cases ys with
    | nil =>
      cases ys' with
      | nil => rfl
      | cons y' t' =>
        exfalso
        rw [List.append_nil] at h1
        subst h1
        exact hf.stop _ _ _ (repairAt_next hC hf' h2)
    | cons y t =>
      cases ys' with
      | nil =>
        exfalso
        rw [List.append_nil] at h2
        subst h2
        exact hf'.stop _ _ _ (repairAt_next hC hf h1)
      | cons y' t' =>
        have e1 := repairAt_next hC hf h1
        have e2 := repairAt_next hC hf' h2
        rw [e1] at e2
        injection e2 with hy _ _
        subst hy
        congr 1
        exact ih (xs ++ [y]) t t' (by simp only [List.length_cons] at hl; omega)
          (by rw [h1]; simp) (by rw [h2]; simp)

/-- The `.broken` name of a segment's name. -/
def repBroken (b : GoString) : GoString := b ++ go!".broken"

theorem child_repBroken (dir b : GoString) : child dir b ++ go!".broken" = child dir (repBroken b) := by
  simp [child, repBroken, List.append_assoc]

theorem repBroken_suffix (sq ix : Nat) : go!".wal.broken" <:+ repBroken (walFileName sq ix) := by
  unfold repBroken walFileName
  exact ⟨hex16 sq ++ go!"-" ++ hex16 ix, by simp [List.append_assoc]⟩

theorem repBroken_nameOk {b : GoString} (hb : NameOk b) : NameOk (repBroken b) := by
  obtain ⟨hne, -, -, hsl, hnul⟩ := hb
  have hlen : 2 < (repBroken b).length := by
    have : 0 < b.length := List.length_pos_iff.2 hne
    simp [repBroken]
  refine ⟨fun h => by rw [h] at hlen; simp at hlen, fun h => by rw [h] at hlen; simp at hlen,
    fun h => by rw [h] at hlen; simp at hlen, ?_, ?_⟩
  · intro h
    simp only [repBroken, List.mem_append] at h
    rcases h with h | h
    · exact hsl h
    · revert h; decide
  · intro h
    simp only [repBroken, List.mem_append] at h
    rcases h with h | h
    · exact hnul h
    · revert h; decide

/-- A pseudo-key lent and given back. -/
theorem WalOut.delClaim_addClaim (o : WalOut) (k : Ino × NameSet) (hk : k ∉ o.D) :
    (o.addClaim k).delClaim k = o := by
  unfold WalOut.addClaim WalOut.delClaim
  simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte]
  rw [List.filter_eq_self.2]
  intro a ha
  simp only [decide_eq_true_eq]
  intro h; subst h; exact hk ha

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
  [W : WalGS GF]

/-- **A WAL directory's key: its left-out names hold no `.wal.broken` name** (see the file header). -/
theorem walInvBody_keyExcl (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (s : AbsDiskState) (dir : GoString) (j : Ino) (X : List GoString) :
    ⊢ walInvBody (L := L) (W := W) C Mr R jr r s -∗ walDirKey (W := W) dir j X -∗
      ⌜∀ b ∈ X, ¬ go!".wal.broken" <:+ b⌝ ∗ walInvBody (L := L) (W := W) C Mr R jr r s := by
  iintro Hb #Hkey
  unfold walInvBody
  icases Hb with ⟨%Ls, %cl, %n, %F, Hg, %Har, Hcl0, #Hcm, Hlays, %Hok, %Hco, HCR,
    Htl, %Han, %Hnm, Hpk, ⟨%K, %cp, Hdk, Hcp, %Hdko⟩, %HAt, Hnms, %Hbd⟩
  icases walDirKey_lookup K dir j X $$ Hdk Hkey with %HK
  obtain ⟨lay, hj1, hl, hlj, hjjr, hX, honce, hcoh, hexcl⟩ := Hdko.1 dir j X HK
  rw [← hlj]
  obtain ⟨l1, l2, hcl, -, -⟩ := honce
  have hm : (lay.j, NameSet.except X, hj1) ∈ cl := by rw [hcl, hlj]; simp
  obtain ⟨X2, hj2, hD2, hx2⟩ := Hdko.2.2 dir lay hl
  obtain ⟨hXe, -⟩ := hD2.eq_of_mem hX hm
  rw [← hXe] at hx2
  isplitr
  · ipureintro; exact hx2.not_broken
  iexists Ls, cl, n, F
  iframe Hg Hcl0 Hcm Hlays HCR Htl Hpk Hnms
  isplitr
  · ipureintro; exact Har
  isplitr
  · ipureintro; exact Hok
  isplitr
  · ipureintro; exact Hco
  isplitr
  · ipureintro; exact Han
  isplitr
  · ipureintro; exact Hnm
  isplitl [Hdk Hcp]
  · iexists K, cp; iframe Hdk Hcp; ipureintro; exact Hdko
  ipureintro; exact ⟨HAt, Hbd⟩

/-- `walInvBody_keyExcl` at any step. -/
theorem walInv_keyExcl (C : WalCodec) (Mr : WalMarshal) (R : Roots) (jr : Ino) (r : GoString)
    (E : CoPset) (hE : ↑walN ⊆ E) (dir : GoString) (j : Ino) (X : List GoString) :
    ⊢ walInv (L := L) (W := W) C Mr R jr r -∗ notCrashed (hC := L.goose_crashGS) -∗
      walDirKey (W := W) dir j X ={E}=∗
      notCrashed (hC := L.goose_crashGS) ∗ ⌜∀ b ∈ X, ¬ go!".wal.broken" <:+ b⌝ := by
  iintro #Hinv Hnc #Hk
  imod walInv_open C Mr R jr r E hE $$ Hinv Hnc with ⟨⟨%s, Hb⟩, Hnc, Hcl⟩
  icases walInvBody_keyExcl C Mr R jr r s dir j X $$ Hb Hk with ⟨%hx, Hb⟩
  imod Hcl $$ [Hb] with -
  · iexists s; iexact Hb
  imodintro
  iframe Hnc
  ipureintro; exact hx

end iris

end WalFs
end EtcdGrove
end Perennial

end
