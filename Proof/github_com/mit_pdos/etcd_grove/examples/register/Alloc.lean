/-
Lean-first (no Rocq counterpart).

# Allocating the register's ghost state (2026-10-10)

What a cluster's set-up gives the replicas' `NewStorage` and `New`:

* `regStorInv_alloc`: the storage registry's invariant, from the authority of an empty
  ghost map at the registry's name (allocated first, `ghost_map_alloc_empty`, and made the
  `RegStor` instance).
* `regInv_alloc`: the register's invariant over raft's client log, from what raft's
  allocation (`ownRaftGhost_alloc`, `Protocol/Facts.lean`) hands the client -- its half of
  the empty client log, the authority of the fresh-data tokens and (2026-10-13) that of
  the read contexts -- with the client's half
  of the value (empty) and the replicas' sequence-number tokens at `S0` (for `New`, each
  at 0: `S0 = gsetToGmap (W64 0) ids`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.register.Lemmas

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
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.register.Assumptions]
variable [RegStor GF]

/-- The storage registry's invariant, with no storage registered yet. -/
theorem regStorInv_alloc (E : CoPset) :
    ⊢ ghostMapAuth (RegStor.regStorName (GF := GF)) 1 (∅ : GMap Loc MemStorRec) ={E}=∗
      regStorInv (GF := GF) := by
  iintro Ha
  unfold regStorInv
  iapply inv_alloc
  inext
  unfold regStorInvBody
  iexists ∅
  iframe Ha
  iapply BigSepM.bigSepM_empty.2
  itrivial

/-- The register's invariant over raft's client log `γ`, at the empty log: from the
client's share of raft's allocation, the invariant, the client's half of the value and the
sequence-number tokens of `S0` (`New` takes `id ↪[γr.seq] 0`). -/
theorem regInv_alloc (E : CoPset) (γ : RaftNames) (S0 : GMap w64 w64) :
    ⊢ cLog (GF := GF) γ [] -∗ ghostMapAuth γ.reFresh 1 (∅ : GMap (List w8) Unit) -∗
      ghostMapAuth γ.reReads 1 (∅ : GMap (List w8) (List raftpb.Entry)) ={E}=∗
      ∃ γr : RegNames, ⌜γr.raft = γ⌝ ∗ regInv γr ∗ regVal γr [] ∗
        [∗map] id ↦ s ∈ S0, id ↪[γr.seq] s := by
  iintro Hcl HM HR
  imod ghostVar_alloc (GF := GF) ([] : List w8) with ⟨%γv, Hv⟩
  icases ghostVar_halves γv ([] : List w8) $$ Hv with ⟨Hv1, Hv2⟩
  imod ghost_map_alloc (GF := GF) S0 with ⟨%γs, HS, Hels⟩
  imod ghost_map_alloc_empty (GF := GF) (K := w64 × w64) (V := List w8) with ⟨%γm, HMi⟩
  imod inv_alloc regN E (regInvBody (GF := GF) ⟨γ, γv, γs, γm⟩) $$ [Hcl Hv1 HM HR HS HMi] with #Hinv
  · inext
    unfold regInvBody
    iexists [], ∅, ∅, _, ∅
    simp only [show regFold [] = ([] : List w8) from rfl]
    iframe Hcl Hv1 HM HR HS HMi
    ipureintro
    refine ⟨?_, ?_, ?_⟩
    · intro d h; simp at h
    · intro i s d h; simp at h
    · intro c Lc h; simp at h
  imodintro
  iexists ⟨γ, γv, γs, γm⟩
  isplitr
  · ipureintro; rfl
  unfold regInv regVal
  iframe Hinv Hv2 Hels

end alloc

end EtcdGrove
end Perennial
