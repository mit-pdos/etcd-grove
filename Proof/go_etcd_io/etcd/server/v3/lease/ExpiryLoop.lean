/-
The expiry loop's facts (prove-ps2-newlessor3, 2026-11-21): what `revokeExpiredLeases` sends on
`expiredC` (`expired_slice`), and the loop's resources (`loopRes`). Lean-first.
-/
module

public import Proof.go_etcd_io.etcd.server.v3.lease.GuardLaws
public import Proof.go_etcd_io.etcd.server.v3.lease.LessorBackend

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace lease

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.lease

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.lease.Assumptions]

/-- **The leases the expiry loop found**, leases of the map `M` whose ids are live (`L`) and
granted: each not nil, its `ID` read-only, with the grant guard of its id after a step. -/
theorem expired_slice (γl : GName) (GA : w64 → IProp GF) (L : List w64) (M : GMap w64 Loc)
    (ps : List Loc) (HL : ∀ id : w64, id ∈ L ↔ (M.lookup id).isSome)
    (hps : ∀ p ∈ ps, ∃ id, M.lookup id = some p) :
    lessorGuard γl GA ∗ □ ([∗list] id ∈ L, leaseGranted γl id) ∗
      ([∗map] _id ↦ l ∈ M, isLeaseObj γl l) ∗ ([∗map] id ↦ l ∈ M, lsF go!"ID" l ↦□ id) ⊢
      ▷ [∗list] p ∈ ps, ⌜p ≠ null⌝ ∗ ∃ id : w64, lsF go!"ID" p ↦□ id ∗ GA id := by
  iintro ⟨#Hg, #Hgr, #Hlo, #Hid⟩
  iapply BigSepL.bigSepL_later.2
  have key : □ (lessorGuard (GF := GF) γl GA ∗ □ ([∗list] id ∈ L, leaseGranted γl id) ∗
      ([∗map] _id ↦ l ∈ M, isLeaseObj γl l) ∗ ([∗map] id ↦ l ∈ M, lsF go!"ID" l ↦□ id)) ⊢
      [∗list] p ∈ ps, ▷ (⌜p ≠ null⌝ ∗ ∃ id : w64, lsF go!"ID" p ↦□ id ∗ GA id) := by
    apply BigSepL.bigSepL_intro
    intro k p hk
    obtain ⟨id, hid⟩ := hps p (List.mem_of_getElem? hk)
    have hL : id ∈ L := (HL id).2 (by rw [hid]; rfl)
    obtain ⟨n, hn, hLn⟩ := List.mem_iff_getElem.mp hL
    have hLn' : L[n]? = some id := by rw [List.getElem?_eq_getElem hn, hLn]
    iintro #⟨#Hg, #Hgr, #Hlo, #Hid⟩
    ihave #Hgi := BigSepL.bigSepL_lookup hLn' $$ Hgr
    ihave #Hloi := BigSepM.bigSepM_lookup hid $$ Hlo
    ihave #Hidi := BigSepM.bigSepM_lookup hid $$ Hid
    ihave HGA := guard_of_granted γl GA id $$ [$Hg $Hgi]
    iunfold isLeaseObj at Hloi
    icases Hloi with ⟨%Hnn, -⟩
    inext
    isplitr
    · ipureintro; exact Hnn
    iexists id
    iframe Hidi HGA
  iapply key
  imodintro
  iframe #

end lemmas

end lease
end EtcdGrove
end Perennial
