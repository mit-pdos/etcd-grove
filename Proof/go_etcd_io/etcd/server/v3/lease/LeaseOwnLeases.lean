/-
**The owner's live set is what `Leases()` lists** (mvccfull's Prove, 2026-11-10). Lean-first (no
Rocq counterpart).

`leaseOwn_leases`: the lease owner (`leaseOwn γl L I`) holds a lower bound `m` of the lessor's
history at its last index (`lessorLb γl m`, what `lessor.Leases.spec` takes); while the owner keeps
its resource nobody appends to the history (an append takes the owner's half of its authority), so
the lease map a later `Leases()` saw at an index no earlier than `m` (`leaseMapAt γl i ls`) is the
owner's: its ids, each once, are exactly the live set `L`. In a module of its own, so that adding it
leaves `InvLessor` (and its importers) as they were.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.InvLessor

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **The owner's live set is the lease map `Leases()` returns**: at a lower bound `m` of the
history the owner gives, a lease map at an index no earlier than `m` has the ids of `L`, each once
(the owner's resource given back). -/
theorem leaseOwn_leases (γl : GName) (L : List w64) (I : GMap LeaseItem w64) :
    leaseOwn (GF := GF) γl L I ⊢ ∃ m : Nat, lessorLb γl m ∗
      (∀ (i : Nat) (ls : List (Loc × w64)), ⌜m ≤ i⌝ -∗ leaseMapAt γl i ls -∗
        leaseOwn γl L I ∗
          ⌜(ls.map Prod.snd).Nodup ∧ ∀ id : w64, id ∈ ls.map Prod.snd ↔ id ∈ L⌝) := by
  unfold leaseOwn leaseClosers
  iintro ⟨Hf, %lp, %γga, %γcl, %C, %im, #Hp, %HC, Him, HI, %HIL, %HIS, Hcs, %γr, %hs, %Sm, #Hpr,
    Ha, %Hlast, HSm⟩
  obtain ⟨T, hT⟩ := Hlast
  have hne : hs ≠ [] := by rintro rfl; simp at hT
  have hlen : 0 < hs.length := List.length_pos_iff.2 hne
  ihave #Hlb := monoListLbOwn_get γr.1 _ hs $$ Ha
  iexists hs.length - 1
  isplitr
  · iunfold lessorLb
    iexists γr, hs; iframe Hpr Hlb; ipureintro; omega
  iintro %i %ls %hi Hmap
  iunfold leaseMapAt at Hmap
  icases Hmap with ⟨%σ, %Hσ, Hat⟩
  iunfold lessorAt at Hat
  icases Hat with ⟨%γr', #Hpr', #Hidx⟩
  ihave %Hγ := lessorPinR_agree γl γr γr' $$ [Hpr Hpr']
  · iframe Hpr Hpr'
  subst Hγ
  ihave %Hhi := mono_list_auth_idx_lookup γr.1 _ hs i σ $$ Ha Hidx
  have hil : i < hs.length := (List.getElem?_eq_some_iff.1 Hhi).1
  have hi' : i = hs.length - 1 := by omega
  have hσ : σ = (C, I, T) := by
    rw [List.getLast?_eq_getElem?, ← hi', Hhi] at hT
    exact Option.some.inj hT
  subst hσ
  isplitl
  · iframe Hf
    iexists lp, γga, γcl, C, im
    iframe Hp Him HI Hcs
    isplitr; · ipureintro; exact HC
    isplitr; · ipureintro; exact HIL
    isplitr; · ipureintro; exact HIS
    iexists γr, hs, Sm; iframe Hpr Ha HSm; ipureintro; exact ⟨T, hT⟩
  ipureintro
  refine ⟨Hσ.1, fun id => ?_⟩
  rw [HC id, List.mem_map]
  constructor
  · rintro ⟨⟨l, id'⟩, hm, rfl⟩
    have := (Hσ.2 _ l).1 hm
    simp only at this
    simp [this]
  · intro h
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.1 h
    exact ⟨(l, id), (Hσ.2 id l).2 hl, rfl⟩

end proof

end lease
end EtcdGrove
end Perennial
