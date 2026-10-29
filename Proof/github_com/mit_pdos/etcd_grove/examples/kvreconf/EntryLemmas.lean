/-
Lean-first (no Rocq counterpart).

# A committed entry that is not a conf change (2026-10-29, track C)

`applyEntry`'s other cases: past an entry that is no conf change, the applier's view of the node
moves for free (`appNode_noConf`: nothing to skip); an entry of no type the store knows (neither
normal nor conf) leaves the replicated state (`repOwn_other`). And a decoded `ConfChangeV2` frozen
read-only (`kvr_ownConfChangeV2_persist`, as raft's internal `ownConfChangeV2_persist`), which
`applyConf` takes.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ApplyConfLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.PureLemmas

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvreconf

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvreconf.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions]
variable [StorageModel GF] [AllG GF]

/-- Past an entry that is no conf change, the view of the node moves. -/
theorem appNode_noConf (RA : RaftAssume (GF := GF)) (γr : RNames) (n : Loc) (l : List LogEntry)
    (k : Nat) (e : LogEntry) (m : Membership) (hk : l[k]? = some e) (hc : ¬ e.isConfChange) :
    appNode RA γr n l k m ⊢ appNode RA γr n l (k + 1) m := by
  iintro Hn
  unfold appNode
  icases Hn with (⟨%v, Hv, #Hdl, #Hsk, %Hvm⟩ | #Hst)
  · ileft
    iexists v
    iframe Hv Hdl
    isplitl
    · unfold skippedIn
      have hr : List.range' v.applied (k + 1 - v.applied) =
          List.range' v.applied (k - v.applied) ++ [k] := by
        rw [show k + 1 - v.applied = (k - v.applied) + 1 by omega, List.range'_concat]
        congr 2; omega
      rw [hr]
      iapply BigSepL.bigSepL_snoc.2
      iframe Hsk
      iintro %e' %He'
      obtain ⟨h1, h2⟩ := He'
      rw [hk] at h1; cases h1
      exact absurd h2 hc
    · ipureintro; exact ⟨Hvm.1, by omega⟩
  · iright; iexact Hst

/-- An entry of no type the store knows leaves the replicated state. -/
theorem repOwn_other (RA : RaftAssume (GF := GF)) (γr : RNames) (n r : Loc) (ap : List LogEntry)
    (idx : w64) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8))
    (e : LogEntry) (ht : e.type ≠ W32 0) (hc : ¬ e.isConfChange)
    (hlen : (ap.length : Int) + 1 < 2 ^ 61) :
    isCommittedLogLb γr.cluster (ap ++ [e]) ∗ repOwn RA γr n r ap idx csp m mA A ⊢
      repOwn RA γr n r (ap ++ [e]) idx csp m mA A := by
  iintro ⟨#Hce, Hown⟩
  iunfold repOwn at Hown
  iNamed Hown
  have Hod : odOf e = none := by
    unfold odOf; rw [if_neg]; rintro ⟨h, _⟩; exact ht h
  have Hlh : logHist (ap ++ [e]) = logHist ap := by rw [logHist_snoc, Hod]; rfl
  unfold repOwn
  iexists mK, K, c
  iframe HmK HK HmA HA Hcs Hidx HcsO Hce
  isplitr
  · ipureintro; simp; omega
  isplitr
  · ipureintro; rw [Hlh]; exact Hval
  isplitr
  · ipureintro; rw [Hlh]; exact HA
  icases Hcfg with (⟨%Hcs, #Hca⟩ | Hs)
  · ileft
    isplitr
    · ipureintro; exact Hcs
    rw [List.length_append, List.length_singleton]
    iapply kvr_confAt_normal γr.cluster (ap ++ [e]) ap.length e m (by simp) hc
    iframe Hce Hca
  · iright; iexact Hs

/-- A conf change frozen read-only (see the file header). -/
theorem kvr_ownConfChangeV2_persist (p : Loc) (dq : DFrac) (m : ConfChangeV2M) :
    ownConfChangeV2 (GF := GF) p dq m ⊢ |==> ownConfChangeV2 p DFrac.discard m := by
  iintro H
  iunfold ownConfChangeV2 at H
  iNamed H
  imod (typedPointsto_dfractional (GF := GF) _ pt).dfractional_persist _ $$ HT with #HT
  imod (typedPointsto_dfractional (GF := GF) _ chs).dfractional_persist _ $$ HCh with #HCh
  imod (ownSlice_dfractional (GF := GF) _ _).dfractional_persist _ $$ Hch with #Hch
  imod (typedPointsto_dfractional (GF := GF) _ cs).dfractional_persist _ $$ HC with #HC
  imodintro
  iunfold ownConfChangeV2
  iexists pt, chs, ls, cs, uf
  isplitr
  · ipureintro; exact Hnn
  iframe HT cT HCh Hch Hccs HC Hcs Hpb

end laws

end kvreconf
end EtcdGrove
end Perennial
