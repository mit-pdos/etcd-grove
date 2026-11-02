/-
Lean-first (no Rocq counterpart).

# The applier's configuration facts (2026-10-29, track C)

What `applyConf` and `applyEntry` use: every committed conf entry is shaped (`rkv_confShaped`, from
the store's invariant, `confShaped_of_ops`); the rule's decision on a decoded entry
(`kvrRule_decoded`); a rejected entry extends the node's skipped range (`skippedIn_snoc`); the
configuration's well-formedness for `validConf` (`confAt_wf`, and `nil`'s empty membership,
`confStateIs_nil`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.Defs

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

open Classical in
/-- The rule's decision on an entry that decodes to `o`. -/
theorem kvrRule_decoded (pre : List LogEntry) (m : Membership) (e : LogEntry) (o : ConfChangeIM)
    (h : ccDecode e = some o) :
    kvrRule pre m e = if ConfOk o m then some o else none := by
  unfold kvrRule; rw [h]

/-- `nil`'s configuration (the zero `ConfState`) is the empty membership. -/
theorem confStateIs_nil : confStateIs (ConfStateM.mk [] [] [] [] false) Membership.empty := by
  have h : elements (∅ : GSet w64) = [] :=
    List.eq_nil_of_length_eq_zero (by rw [GMap.length_elements, GMap.size_empty])
  unfold confStateIs Membership.empty
  simp [h]

end pure

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- **Every committed conf entry is shaped** (the store's invariant, `confShaped_of_ops`). -/
theorem rkv_confShaped (γr : RNames) (l : List LogEntry) (E : CoPset) (hE : ↑rkvN ⊆ E) :
    ⊢ rkvInv (GF := GF) γr -∗ isCommittedLogLb γr.cluster l ={E}=∗
      ⌜∀ e ∈ l, e.isConfChange → ConfShaped e⌝ := by
  unfold rkvInv rkvInvBody
  iintro #Hinv #Hl
  iinv Hinv with ⟨%ops, %nn, %Mi, %RS, %RMi, %O, %U, >Hcore, Hslots⟩ Hclose
  iunfold kvCore at Hcore
  icases Hcore with ⟨Hops, Hrest⟩
  ihave %Hp := ownCommittedOps_lb_prefix γr.cluster ops l $$ [$Hops $Hl]
  icases Hrest with ⟨Hval, Hrc, Hopn, HMi, HRS, HRMi, HO, %HMint, %HMod, %Hsh⟩
  imod Hclose $$ [Hops Hval Hrc Hopn HMi HRS HRMi HO Hslots] with -
  · inext
    iexists ops, nn, Mi, RS, RMi, O, U
    iframe Hslots
    unfold kvCore
    iframe
    ipureintro; exact ⟨HMint, HMod, Hsh⟩
  imodintro
  ipureintro
  exact confShaped_of_ops l ops Hp Hsh

/-- A configuration raft reached is one `validConf` reads: well formed and restorable. -/
theorem confAt_wf (γ : Cluster) (k : Nat) (m : Membership) :
    confAt (GF := GF) γ k m ⊢ ⌜m.WellFormed ∧ m.Restorable⌝ := by
  iintro #H
  ihave %Hv := confAt_valid γ k m $$ H
  ihave %Hr := confAt_restorable γ k m $$ H
  ipureintro; exact ⟨Membership.WellFormed.of_valid Hv, Hr⟩

/-- A rejected conf entry extends the skipped range. -/
theorem skippedIn_snoc (γ : Cluster) (l : List LogEntry) (a k : Nat) (hak : a ≤ k) :
    skippedIn (GF := GF) γ l a k ∗ confDecided γ k .skip ⊢ skippedIn γ l a (k + 1) := by
  iintro ⟨#H, #Hd⟩
  unfold skippedIn
  have hr : List.range' a (k + 1 - a) = List.range' a (k - a) ++ [k] := by
    rw [show k + 1 - a = (k - a) + 1 by omega, List.range'_concat]
    congr 2; omega
  rw [hr]
  iapply BigSepL.bigSepL_snoc.2
  iframe H
  iintro %e %_
  iexact Hd

end laws

end kvreconf
end EtcdGrove
end Perennial
