/-
Lean-first (no Rocq counterpart).

# A committed conf entry decided (2026-10-29, track C)

`applyConf`'s two outcomes on the applier's configuration facts (`repOwn`'s, as `cfgAt`) and its
view of the node (`appNode`), at the entry's position `k`:

- rejected (`validConf` says no: `¬ ConfOk o m`): the rule decides `skip` (`kvr_confAt_conf`), the
  configuration stays, the node's skipped range grows (`conf_reject`);
- accepted: the rule decides `apply o`, and `node.ApplyConfChange` (`RaftAssume`'s, running or
  stopped) answers the configuration after it, or `nil` with the node stopped (`wp_conf_apply`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ConfLemmas

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

/-- `repOwn`'s configuration facts at `k` entries applied: the configuration `c` (at `csp`) denotes
`m`, raft's configuration there; or `nil`, the empty membership, the node stopped. -/
def cfgAt (RA : RaftAssume (GF := GF)) (γr : RNames) (n : Loc) (csp : Loc) (c : ConfStateM)
    (m : Membership) (k : Nat) : IProp GF :=
  iprop((⌜confStateIs c m⌝ ∗ confAt γr.cluster k m) ∨
    (⌜csp = null ∧ m = Membership.empty⌝ ∗ RA.nodeStopped n γr.cluster kvrRaftN))

instance cfgAt_persistent (RA : RaftAssume (GF := GF)) (γr : RNames) (n csp : Loc)
    (c : ConfStateM) (m : Membership) (k : Nat) : Persistent (cfgAt RA γr n csp c m k) := by
  unfold cfgAt; infer_instance

instance kvr_ownConfChangeV2_discard_persistent (p : Loc) (m : ConfChangeV2M) :
    Persistent (ownConfChangeV2 (GF := GF) p DFrac.discard m) := by
  unfold ownConfChangeV2; infer_instance

instance ownConfChangeI_discard_persistent (c : GoInterface) (o : ConfChangeIM) :
    Persistent (ownConfChangeI (GF := GF) c DFrac.discard (some o)) := by
  cases o <;> simp only [ownConfChangeI] <;> infer_instance

/-- The configuration `validConf` reads is well formed and restorable. -/
theorem cfgAt_wf (RA : RaftAssume (GF := GF)) (γr : RNames) (n csp : Loc) (dq : DFrac)
    (c : ConfStateM) (m : Membership) (k : Nat) :
    cfgAt RA γr n csp c m k ∗ csOpt csp dq c ⊢ ⌜confStateIs c m ∧ m.WellFormed ∧ m.Restorable⌝ := by
  iintro ⟨Hc, Ho⟩
  unfold cfgAt
  icases Hc with (⟨%Hcs, #Hca⟩ | ⟨%Hn, -⟩)
  · ihave %H := confAt_wf γr.cluster k m $$ Hca
    ipureintro; exact ⟨Hcs, H⟩
  · obtain ⟨Hp, Hm⟩ := Hn
    subst Hp Hm
    unfold csOpt
    icases Ho with (%Hz | Ho)
    · obtain ⟨-, Hz⟩ := Hz
      subst Hz
      ipureintro
      exact ⟨confStateIs_nil, Membership.wellFormed_empty, Membership.restorable_empty⟩
    · icases csPts_nn null dq c false $$ Ho with ⟨-, %Hnn⟩
      exfalso; exact Hnn rfl

/-- **A rejected conf entry** (see the file header). -/
theorem conf_reject (RA : RaftAssume (GF := GF)) (γr : RNames) (vs : List w64) (n : Loc)
    (l : List LogEntry) (e : LogEntry) (o : ConfChangeIM) (csp : Loc) (c : ConfStateM)
    (m : Membership) (k : Nat) (E : CoPset) (hk : l[k]? = some e) (hd : ccDecode e = some o)
    (hno : ¬ ConfOk o m) (hE : ↑kvrConfN ⊆ E) :
    ⊢ kvrCluster γr vs -∗ isCommittedLogLb γr.cluster l -∗ cfgAt RA γr n csp c m k -∗
      appNode RA γr n l k m ={E}=∗ cfgAt RA γr n csp c m (k + 1) ∗ appNode RA γr n l (k + 1) m := by
  iintro #Hcl #Hl #Hc Hn
  unfold cfgAt
  icases Hc with (⟨%Hcs, #Hca⟩ | ⟨%Hs, #Hst⟩)
  · iunfold kvrCluster at Hcl
    icases Hcl with ⟨#Hic, #Hpol, -⟩
    imod kvr_confAt_conf γr.cluster kvrRaftN E l k e m hk (ccDecode_isConfChange hd) hE
      $$ [$Hic $Hpol $Hl $Hca] with ⟨%m', %Hstep, #Hd, #Hca'⟩
    rw [kvrRule_decoded _ _ _ _ hd, if_neg hno] at Hstep
    simp only [ConfDecision.ofRule, ConfDecision.step, Option.some.injEq] at Hstep
    subst Hstep
    rw [kvrRule_decoded _ _ _ _ hd, if_neg hno]
    simp only [ConfDecision.ofRule]
    isplitr
    · ileft; iframe Hca'; ipureintro; exact Hcs
    unfold appNode
    icases Hn with (⟨%v, Hv, #Hdl, #Hsk, %Hvm⟩ | #Hst)
    · ileft
      iexists v
      iframe Hv Hdl
      isplitl
      · iapply skippedIn_snoc γr.cluster l v.applied k Hvm.2
        iframe Hsk Hd
      · ipureintro; exact ⟨Hvm.1, by omega⟩
    · iright; iexact Hst
  · imodintro
    isplitr
    · iright; iframe Hst; ipureintro; exact Hs
    unfold appNode
    iright; iexact Hst

/-- **An accepted conf entry applied to the node** (see the file header). -/
theorem wp_conf_apply (RA : RaftAssume (GF := GF)) (γr : RNames) (vs : List w64) (id : w64)
    (n : Loc) (l : List LogEntry) (e : LogEntry) (o : ConfChangeIM) (c : GoInterface) (csp : Loc)
    (cs0 : ConfStateM) (m : Membership) (k : Nat) (hk : l[k]? = some e)
    (hd : ccDecode e = some o) (hok : ConfOk o m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γr.cluster kvrRaftN id ∗
        kvrCluster γr vs ∗ isCommittedLogLb γr.cluster l ∗ ownConfChangeI c DFrac.discard (some o) ∗
        cfgAt RA γr n csp cs0 m k ∗ appNode RA γr n l k m }}
      (App (Val #(methods node.ty.PointerType go!"ApplyConfChange" #n)) (Val #c))
    {{ (csp' : Loc), RET #csp'; ∃ (m' : Membership) (c' : ConfStateM),
        csOpt csp' DFrac.discard c' ∗ cfgAt RA γr n csp' c' m' (k + 1) ∗
        appNode RA γr n l (k + 1) m' }} := by
  iintro %Φ ⟨#Hraft, #Hnode, #Hcl, #Hl, #Hcc, #Hc, Hn⟩ HΦ
  -- the stopped answer: `nil`, the empty membership
  ihave #Hnil : iprop(□ (RA.nodeStopped n γr.cluster kvrRaftN -∗
      ∃ (m' : Membership) (c' : ConfStateM), csOpt null DFrac.discard c' ∗
        cfgAt RA γr n null c' m' (k + 1) ∗ appNode RA γr n l (k + 1) m')) $$ []
  · imodintro
    iintro #Hst
    iexists Membership.empty, ConfStateM.mk [] [] [] [] false
    unfold csOpt cfgAt appNode
    isplitr
    · ileft; ipureintro; exact ⟨rfl, rfl⟩
    isplitr
    · iright; iframe Hst; ipureintro; exact ⟨rfl, rfl⟩
    iright; iexact Hst
  unfold cfgAt
  icases Hc with (⟨%Hcs, #Hca⟩ | ⟨-, #Hst⟩)
  rotate_left
  · wp_apply RA.ApplyConfChange_stoppedSpec n γr.cluster kvrRaftN id c DFrac.discard o
      $$ [$Hraft $Hnode $Hcc $Hst] as -
    iapply HΦ
    iapply Hnil $$ Hst
  unfold appNode
  icases Hn with (⟨%v, Hv, #Hdl, #Hsk, %Hvm⟩ | #Hst)
  rotate_left
  · wp_apply RA.ApplyConfChange_stoppedSpec n γr.cluster kvrRaftN id c DFrac.discard o
      $$ [$Hraft $Hnode $Hcc $Hst] as -
    iapply HΦ
    iapply Hnil $$ Hst
  -- the store's decision: `apply o`
  ihave #Hcl' := Hcl
  iunfold kvrCluster at Hcl'
  icases Hcl' with ⟨#Hic, #Hpol, -⟩
  imod kvr_confAt_conf γr.cluster kvrRaftN ⊤ l k e m hk (ccDecode_isConfChange hd)
    (fun _ _ => CoPset.mem_full) $$ [$Hic $Hpol $Hl $Hca] with ⟨%m', %Hstep, #Hd, #Hca'⟩
  rw [kvrRule_decoded _ _ _ _ hd, if_pos hok] at Hstep
  simp only [ConfDecision.ofRule, ConfDecision.step] at Hstep
  rw [kvrRule_decoded _ _ _ _ hd, if_pos hok]
  rw [show ConfDecision.ofRule (some o) = .apply o from rfl]
  obtain ⟨Hvm, Hva⟩ := Hvm
  iapply wp_fupd
  wp_apply RA.ApplyConfChange_spec n γr.cluster kvrRaftN id c o o l k e v m' Hva hk
    (ccDecode_isConfChange hd) (by rw [Hvm]; exact Hstep) (by rw [Hvm]; exact Hstep)
    $$ [$Hraft $Hnode $Hic $Hd $Hcc $Hv $Hdl $Hsk] as %csp' Hr
  icases Hr with (⟨%cs, Hcs', Hv', %Hcsm⟩ | ⟨%Hnull, #Hst, -⟩)
  · imod csPts_persist csp' (DFrac.own 1) cs true $$ Hcs' with #Hcs'
    imodintro
    iapply HΦ
    iexists m', cs
    isplitr
    · unfold csOpt; iright; iapply csPts_weaken csp' DFrac.discard cs true $$ Hcs'
    isplitr
    · ileft; iframe Hca'; ipureintro; exact Hcsm
    ileft
    iexists ⟨k + 1, m'⟩
    iframe Hv' Hdl
    isplitl
    · iapply skippedIn_noConf
      intro j e' h1 h2; simp only at h1 h2; omega
    · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
  · subst Hnull
    imodintro
    iapply HΦ
    iapply Hnil $$ Hst

end laws

end kvreconf
end EtcdGrove
end Perennial
