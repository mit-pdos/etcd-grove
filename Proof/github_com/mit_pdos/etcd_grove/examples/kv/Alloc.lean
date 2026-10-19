/-
Lean-first (no Rocq counterpart).

# Allocating the store's ghost state (2026-10-10)

What a cluster's set-up gives the replicas' `NewStorage` and `New`:

* `kvStorInv_alloc`: the storage registry's invariant, from the authority of an empty
  ghost map at the registry's name (allocated first, `ghost_map_alloc_empty`, and made the
  `KVStor` instance).
* `kvInv_alloc`: the store's invariant over raft's full committed log, from what raft's
  allocation (`ownRaftGhost_alloc`, `Protocol/Facts.lean`) hands the client -- its half of
  the empty log, the authority of the fresh-data tokens and (2026-10-14, stage R) that of
  the fresh read-context tokens -- with the client's half
  of the value (empty) and the replicas' sequence-number tokens at `S0` (for `New`, each
  at 0: `S0 = gsetToGmap (W64 0) ids`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kv.Lemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section alloc
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]
variable [KVStor GF]

/-- The storage registry's invariant, with no storage registered yet. -/
theorem kvStorInv_alloc (E : CoPset) :
    ⊢ ghostMapAuth (KVStor.kvStorName (GF := GF)) 1 (∅ : GMap Loc MemStorRec) ={E}=∗
      kvStorInv (GF := GF) := by
  iintro Ha
  unfold kvStorInv
  iapply inv_alloc
  inext
  unfold kvStorInvBody
  iexists ∅
  iframe Ha
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- The store's invariant over raft's full committed log `γ` (2026-10-14, stage R; until
then the client log), at the empty log: from the client's share of raft's allocation (its half
of the empty log, the authorities of the fresh-data and fresh read-context tokens), the
invariant, the client's half of the value and the sequence-number tokens of `S0` (`New` takes
`id ↪[γr.seq] 0`). -/
theorem kvInv_alloc (E : CoPset) (γ : RaftNames) (S0 : GMap w64 w64) :
    ⊢ rLog (GF := GF) γ [] -∗ ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) -∗
      ghostMapAuth γ.reRdFresh 1 (∅ : GMap (List w8) Unit) ={E}=∗
      ∃ γr : KVNames, ⌜γr.raft = γ⌝ ∗ kvInv γr ∗ kvVal γr [] ∗
        [∗map] id ↦ s ∈ S0, id ↪[γr.seq] s := by
  iintro Hcl HM HF
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γv, Hv⟩
  icases ghostVar_halves γv ([] : List w8) $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc (GF := GF) S0 with ⟨%γs, HS, Hels⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := List w8) with ⟨%γm, HMi⟩
  imod ghost_map_alloc_empty (GF := GF) (K := List w8) (V := GName × GName) with ⟨%γo, HO⟩
  imod inv_alloc kvN E (kvInvBody (GF := GF) ⟨γ, γv, γs, γm, γo⟩)
    $$ [Hcl Hv1 HM HF HS HMi HO] with #Hinv
  · inext
    unfold kvInvBody
    iexists [], [], ∅, ∅, _, ∅, ∅
    isplitl
    · unfold kvCore
      simp only [show kvFold (firstOcc []) = ([] : List w8) from rfl]
      iframe Hcl Hv1 HM HF HS HMi HO
      isplitr
      · iapply (BigSepL2.bigSepL2_nil (Φ := fun _ e o => entDataIs (GF := GF) γ e o)).2
        iempintro
      ipureintro
      refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · intro d h; simp at h
      · intro i s d h; simp at h
      · intro c h; simp at h
      · intro d γp h; simp at h
      · intro d h; simp at h
    · iapply BigSepM.bigSepM_empty.2
      itrivial
  imodintro
  iexists ⟨γ, γv, γs, γm, γo⟩
  isplitr
  · ipureintro; rfl
  unfold kvInv kvVal
  iframe Hinv Hv2 Hels

end alloc

end EtcdGrove
end Perennial
