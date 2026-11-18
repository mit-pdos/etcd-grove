/-
**A pool of reader slots with deposits** (auth-schema-srv A6, 2026-11-18; the realization's ticket pool and
reserved pool, `notes/auth-schema-srv-handoff.md`, "A6 realization design"). Generic: `N` slots, each a
token `tok` (a backend reader slot, `rdTok`) with a share `sh` (of the backend's open token, lent to
`readTx.RLock`). A slot is free (`tok ∗ sh` in the pool), acquiring (`sh` and `tok` with the reader, its
deposit `dep d` in the pool under a ghost map entry the reader holds), or held (`tok` with the reader's read
lock, `sh` back in the pool, a receipt `ownToks γh 1`). The readers' resources `R` are counted by `Rs`
(`Rs a`: `a` of them deposited), whose bound (`Rs a ∗ R ⊢ ⌜a + 1 ≤ N⌝`) guarantees a free slot.

Release (`pool_release`): with a resource `Z` that refutes every deposit, no slot is acquiring, and the pool
gives back the share of every slot; the readers holding a slot still give it back (`poolRel_rel`).
Lean-first (no Rocq counterpart).
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Ghost.All
public import Perennial.GooseLang.Lifting
public import Perennial.Proof.TokSet
public import Perennial.Ghost.GhostMap

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace authReal

open Iris Iris.BI Iris.ProofMode

section pool
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

theorem rep_succ (P : IProp GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate (n + 1) (), P) ⊣⊢ P ∗ [∗list] _x ∈ List.replicate n (), P := by
  rw [List.replicate_succ]; exact BigSepL.bigSepL_cons

theorem rep_zero (P : IProp GF) : ⊢ [∗list] _x ∈ List.replicate 0 (), P := by
  rw [List.replicate_zero]; exact BigSepL.bigSepL_nil.2

theorem rep_add (P : IProp GF) (a b : Nat) :
    ([∗list] _x ∈ List.replicate a (), P) ∗ ([∗list] _x ∈ List.replicate b (), P) ⊢
      [∗list] _x ∈ List.replicate (a + b) (), P := by
  induction a with
  | zero => simp only [Nat.zero_add]; iintro ⟨-, H⟩; iexact H
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    iintro ⟨Ha, Hb⟩
    icases (rep_succ P a).1 $$ Ha with ⟨Hx, Ha⟩
    iapply (rep_succ P (a + b)).2
    iframe Hx
    iapply ih $$ [$Ha $Hb]

theorem rep_snd (P Q : IProp GF) (n : Nat) :
    ([∗list] _x ∈ List.replicate n (), iprop(P ∗ Q)) ⊢ [∗list] _x ∈ List.replicate n (), Q := by
  induction n with
  | zero => iintro -; iapply rep_zero
  | succ n ih =>
    iintro H
    icases (rep_succ _ n).1 $$ H with ⟨⟨-, Hq⟩, H⟩
    iapply (rep_succ Q n).2
    iframe Hq
    iapply ih $$ H

/-- **The pool's state** (to sit in an invariant): the acquiring slots' deposits (`m`, keys below `nx`),
the held count `kh` with its receipts' authority, the deposited resources (`Rs`), the held slots' shares
and the free slots. -/
def poolSt (γm γh : GName) (Rs : Nat → IProp GF) (dep : Option Qp → IProp GF) (tok sh : IProp GF)
    (N : Nat) : IProp GF :=
  iprop(∃ (m : GMap Nat (Option Qp)) (nx kh : Nat), ghostMapAuth γm 1 m ∗
    ([∗map] _k ↦ d ∈ m, dep d) ∗ Rs (kh + m.size) ∗ ownTokAuth γh kh ∗
    ([∗list] _x ∈ List.replicate kh (), sh) ∗
    ([∗list] _x ∈ List.replicate (N - (kh + m.size)) (), iprop(tok ∗ sh)) ∗
    ⌜kh + m.size ≤ N ∧ ∀ k, (m.lookup k).isSome → k < nx⌝)

/-- **The pool after its release**: only the held slots' receipts and resources (their shares were
collected), for the readers still holding a slot. -/
def poolRel (γh : GName) (Rs : Nat → IProp GF) : IProp GF :=
  iprop(∃ kh : Nat, Rs kh ∗ ownTokAuth γh kh)

/-- A fresh pool: every slot free, nothing deposited. -/
theorem pool_alloc (E : CoPset) (Rs : Nat → IProp GF) (dep : Option Qp → IProp GF) (tok sh : IProp GF) (N : Nat) :
    Rs 0 ∗ ([∗list] _x ∈ List.replicate N (), iprop(tok ∗ sh)) ⊢
      |={E}=> ∃ γm γh, poolSt γm γh Rs dep tok sh N := by
  iintro ⟨HR, Hf⟩
  imod (ghost_map_alloc_empty (K := Nat) (V := Option Qp)) with ⟨%γm, Hm⟩
  imod ownTokAuth_alloc with ⟨%γh, Hh⟩
  imodintro
  iexists γm, γh
  iunfold poolSt
  iexists ∅, 0, 0
  iframe Hm Hh
  rw [map_size_empty]
  simp only [Nat.add_zero, Nat.sub_zero]
  iframe HR Hf
  isplitl []
  · iapply (BigSepM.bigSepM_empty (Φ := fun (_ : Nat) (d : Option Qp) => dep d)).2; itrivial
  isplitl []
  · iapply rep_zero
  ipureintro
  refine ⟨Nat.zero_le _, fun k hk => ?_⟩
  simp at hk

/-- **Acquire** (`Racq`'s pool step): a resource `R` and a deposit in, a slot's token and share out, with
the receipt of the deposit. -/
theorem pool_acq (E : CoPset) (γm γh : GName) (Rs : Nat → IProp GF) (dep : Option Qp → IProp GF) (tok sh R : IProp GF)
    (N : Nat) (hRs : ∀ a, Rs a ∗ R ⊢ Rs (a + 1) ∗ ⌜a + 1 ≤ N⌝) (d : Option Qp) :
    poolSt γm γh Rs dep tok sh N ∗ R ∗ dep d ⊢
      |={E}=> poolSt γm γh Rs dep tok sh N ∗ tok ∗ sh ∗ ∃ k : Nat, ghostMapElem γm k (DFrac.own 1) d := by
  iintro ⟨Hp, HR, Hd⟩
  iunfold poolSt at Hp
  icases Hp with ⟨%m, %nx, %kh, Hm, Hds, HRs, Hh, Hsh, Hf, %Hb⟩
  icases hRs (kh + m.size) $$ [$HRs $HR] with ⟨HRs, %Hle⟩
  have hfresh : m.lookup nx = none := by
    cases h : m.lookup nx with
    | none => rfl
    | some v => exact absurd (Hb.2 nx (by simp [h])) (Nat.lt_irrefl _)
  have hsz : (m.insert nx d).size = m.size + 1 := map_size_insert_None m nx d hfresh
  have hfree : N - (kh + m.size) = (N - (kh + (m.size + 1))) + 1 := by omega
  rw [hfree]
  icases (rep_succ (iprop(tok ∗ sh)) _).1 $$ Hf with ⟨⟨Ht, Hs⟩, Hf⟩
  imod ghost_map_insert (γ := γm) nx d hfresh $$ Hm with ⟨Hm, Hk⟩
  imodintro
  iframe Ht Hs
  isplitl [Hm Hds Hd HRs Hh Hsh Hf]
  · iunfold poolSt
    iexists m.insert nx d, nx + 1, kh
    rw [hsz]
    iframe Hm Hh Hsh Hf
    isplitl [Hds Hd]
    · iapply (BigSepM.bigSepM_insert (Φ := fun (_ : Nat) (d : Option Qp) => dep d) hfresh).2
      iframe Hd Hds
    isplitl [HRs]
    · rw [show kh + (m.size + 1) = kh + m.size + 1 by omega]; iexact HRs
    ipureintro
    refine ⟨by omega, fun k hk => ?_⟩
    by_cases hkn : k = nx
    · omega
    · have : (m.lookup k).isSome := by
        rw [GMap.lookup_insert_ne m d (fun h : nx = k => hkn h.symm)] at hk; exact hk
      exact Nat.lt_succ_of_lt (Hb.2 k this)
  · iexists nx; iexact Hk

/-- **Observe** (`Robs`'s pool step): the receipt of a deposit and the slot's share back, the deposit out,
with the receipt of the held slot. -/
theorem pool_obs (E : CoPset) (γm γh : GName) (Rs : Nat → IProp GF) (dep : Option Qp → IProp GF) (tok sh : IProp GF)
    (N : Nat) (k : Nat) (d : Option Qp) :
    poolSt γm γh Rs dep tok sh N ∗ ghostMapElem γm k (DFrac.own 1) d ∗ sh ⊢
      |={E}=> poolSt γm γh Rs dep tok sh N ∗ dep d ∗ ownToks γh 1 := by
  iintro ⟨Hp, Hk, Hs⟩
  iunfold poolSt at Hp
  icases Hp with ⟨%m, %nx, %kh, Hm, Hds, HRs, Hh, Hsh, Hf, %Hb⟩
  ihave %Hl := ghost_map_lookup $$ Hm Hk
  icases (BigSepM.bigSepM_delete (Φ := fun (_ : Nat) (d : Option Qp) => dep d) Hl).1 $$ Hds with ⟨Hd, Hds⟩
  imod ghost_map_delete (γ := γm) (m := m) (k := k) (v := d) $$ Hm Hk with Hm
  imod ownTokAuth_S γh kh $$ Hh with ⟨Hh, Hr⟩
  have hsz : (m.delete k).size = m.size - 1 := map_size_delete_Some m k d Hl
  have hpos : 0 < m.size := Nat.pos_of_ne_zero (map_size_ne_0_lookup_2 m Hl)
  imodintro
  iframe Hd Hr
  iunfold poolSt
  iexists m.delete k, nx, kh + 1
  rw [hsz, show kh + 1 + (m.size - 1) = kh + m.size by omega]
  iframe Hm Hds HRs Hh Hf
  isplitl [Hsh Hs]
  · iapply (rep_succ sh kh).2; iframe Hs Hsh
  ipureintro
  refine ⟨by omega, fun k' hk' => Hb.2 k' ?_⟩
  by_cases hkk : k' = k
  · subst hkk; rw [GMap.lookup_delete] at hk'; cases hk'
  · rw [GMap.lookup_delete_ne m (fun h : k = k' => hkk h.symm)] at hk'; exact hk'

/-- **Release a slot** (`Rrel`'s pool step): the held slot's receipt and token back, a resource `R` out. -/
theorem pool_rel (E : CoPset) (γm γh : GName) (Rs : Nat → IProp GF) (dep : Option Qp → IProp GF) (tok sh R : IProp GF)
    (N : Nat) (hRs : ∀ a, Rs (a + 1) ⊢ Rs a ∗ R) :
    poolSt γm γh Rs dep tok sh N ∗ ownToks γh 1 ∗ tok ⊢ |={E}=> poolSt γm γh Rs dep tok sh N ∗ R := by
  iintro ⟨Hp, Hr, Ht⟩
  iunfold poolSt at Hp
  icases Hp with ⟨%m, %nx, %kh, Hm, Hds, HRs, Hh, Hsh, Hf, %Hb⟩
  icombine Hh Hr gives %Hkh
  obtain ⟨kh', rfl⟩ : ∃ kh', kh = kh' + 1 := ⟨kh - 1, by omega⟩
  imod ownTokAuth_delete_S γh kh' $$ Hh Hr with Hh
  icases (rep_succ sh kh').1 $$ Hsh with ⟨Hs, Hsh⟩
  rw [show kh' + 1 + m.size = kh' + m.size + 1 by omega]
  icases hRs (kh' + m.size) $$ HRs with ⟨HRs, HR⟩
  imodintro
  iframe HR
  iunfold poolSt
  iexists m, nx, kh'
  iframe Hm Hds HRs Hh Hsh
  isplitl [Hf Ht Hs]
  · rw [show N - (kh' + m.size) = (N - (kh' + m.size + 1)) + 1 by omega]
    iapply (rep_succ (iprop(tok ∗ sh)) _).2
    iframe Hf Ht Hs
  ipureintro
  exact ⟨by omega, Hb.2⟩

/-- **Release the pool**: with a resource `Z` that refutes every deposit, no slot is acquiring; every slot's
share comes back (`N` of them), and the pool keeps only the held slots' receipts (`poolRel`). -/
theorem pool_release (E : CoPset) (γm γh : GName) (Rs : Nat → IProp GF) (dep : Option Qp → IProp GF) (tok sh Z : IProp GF)
    (N : Nat) (hZ : ∀ d, dep d ∗ Z ⊢ False) :
    poolSt γm γh Rs dep tok sh N ∗ Z ⊢
      |={E}=> poolRel γh Rs ∗ Z ∗ ([∗list] _x ∈ List.replicate N (), sh) := by
  iintro ⟨Hp, HZ⟩
  iunfold poolSt at Hp
  icases Hp with ⟨%m, %nx, %kh, Hm, Hds, HRs, Hh, Hsh, Hf, %Hb⟩
  by_cases h0 : m.size = 0
  · rw [h0]
    simp only [Nat.add_zero]
    imodintro
    iframe HZ
    isplitl [HRs Hh]
    · iunfold poolRel; iexists kh; iframe HRs Hh
    -- the free slots' shares and the held ones'
    ihave Hf := rep_snd tok sh _ $$ Hf
    ihave H := rep_add sh kh (N - kh) $$ [$Hsh $Hf]
    rw [show kh + (N - kh) = N by omega]
    iexact H
  · obtain ⟨k, v, hk⟩ := (map_size_ne_0_lookup m).mp h0
    icases (BigSepM.bigSepM_delete (Φ := fun (_ : Nat) (d : Option Qp) => dep d) hk).1 $$ Hds with ⟨Hd, -⟩
    iexfalso
    iapply hZ v $$ [$Hd $HZ]

end pool

end authReal
end EtcdGrove
end Perennial
