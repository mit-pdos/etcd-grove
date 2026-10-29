/-
Lean-first (no Rocq counterpart).

# A committed conf entry decided (2026-10-29, track C)

`applyConf`'s two outcomes on the applier's configuration facts (`repOwn`'s, as `cfgAt`) and its
view of the node (`appNode`), at the entry's position `k`:

- rejected (`validConf` says no: `¬ ConfOk o m`): the rule decides `skip` (`kvr_confAt_conf`), the
  configuration stays, the node's skipped range grows (`conf_reject`);
- accepted: the rule decides `apply o`, and `node.ApplyConfChange` (raft's `node.ApplyConfChange.spec`) answers the
  configuration after it; its stopped answer is refuted by the applier's `nodeRunning` (`wp_conf_apply`).
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

/-- `repOwn`'s configuration facts at `k` entries applied: the configuration `c` denotes `m`,
raft's configuration there. -/
def cfgAt (γr : RNames) (c : ConfStateM) (m : Membership) (k : Nat) : IProp GF :=
  iprop(⌜confStateIs c m⌝ ∗ confAt γr.cluster k m)

instance cfgAt_persistent (γr : RNames) (c : ConfStateM) (m : Membership) (k : Nat) :
    Persistent (cfgAt (GF := GF) γr c m k) := by
  unfold cfgAt; infer_instance

instance kvr_ownConfChangeV2_discard_persistent (p : Loc) (m : ConfChangeV2M) :
    Persistent (ownConfChangeV2 (GF := GF) p DFrac.discard m) := by
  unfold ownConfChangeV2; infer_instance

instance ownConfChangeI_discard_persistent (c : GoInterface) (o : ConfChangeIM) :
    Persistent (ownConfChangeI (GF := GF) c DFrac.discard (some o)) := by
  cases o <;> simp only [ownConfChangeI] <;> infer_instance

/-- The configuration `validConf` reads is well formed and restorable. -/
theorem cfgAt_wf (γr : RNames) (c : ConfStateM) (m : Membership) (k : Nat) :
    cfgAt (GF := GF) γr c m k ⊢ ⌜confStateIs c m ∧ m.WellFormed ∧ m.Restorable⌝ := by
  unfold cfgAt
  iintro ⟨%Hcs, #Hca⟩
  ihave %H := confAt_wf γr.cluster k m $$ Hca
  ipureintro; exact ⟨Hcs, H⟩

/-- **A rejected conf entry** (see the file header). -/
theorem conf_reject (γr : RNames) (vs : List w64) (n : Loc)
    (l : List LogEntry) (e : LogEntry) (o : ConfChangeIM) (c : ConfStateM)
    (m : Membership) (k : Nat) (E : CoPset) (hk : l[k]? = some e) (hd : ccDecode e = some o)
    (hno : ¬ ConfOk o m) (hE : ↑kvrConfN ⊆ E) :
    ⊢ kvrCluster γr vs -∗ isCommittedLogLb γr.cluster l -∗ cfgAt γr c m k -∗
      appNode γr n l k m ={E}=∗ cfgAt γr c m (k + 1) ∗ appNode γr n l (k + 1) m := by
  iintro #Hcl #Hl #Hc Hn
  unfold cfgAt
  icases Hc with ⟨%Hcs, #Hca⟩
  iunfold kvrCluster at Hcl
  icases Hcl with ⟨#Hic, #Hpol, -⟩
  imod kvr_confAt_conf γr.cluster kvrRaftN E l k e m hk (ccDecode_isConfChange hd) hE
    $$ [$Hic $Hpol $Hl $Hca] with ⟨%m', %Hstep, #Hd, #Hca'⟩
  rw [kvrRule_decoded _ _ _ _ hd, if_neg hno] at Hstep
  simp only [ConfDecision.ofRule, ConfDecision.step, Option.some.injEq] at Hstep
  subst Hstep
  rw [kvrRule_decoded _ _ _ _ hd, if_neg hno]
  simp only [ConfDecision.ofRule]
  isplitr
  · iframe Hca'; ipureintro; exact Hcs
  unfold appNode
  icases Hn with ⟨%v, Hv, #Hdl, #Hsk, %Hvm⟩
  iexists v
  iframe Hv Hdl
  isplitl
  · iapply skippedIn_snoc γr.cluster l v.applied k Hvm.2
    iframe Hsk Hd
  · ipureintro; exact ⟨Hvm.1, by omega⟩

/-- **An accepted conf entry applied to the node** (see the file header): the applier's fraction
of `nodeRunning` refutes the stopped answer. -/
theorem wp_conf_apply (wp_ACC : node.ApplyConfChange.spec (GF := GF) (hG := hG)) (γr : RNames) (vs : List w64) (id : w64)
    (n : Loc) (q : Qp) (l : List LogEntry) (e : LogEntry) (o : ConfChangeIM) (c : GoInterface)
    (cs0 : ConfStateM) (m : Membership) (k : Nat) (hk : l[k]? = some e)
    (hd : ccDecode e = some o) (hok : ConfOk o m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γr.cluster kvrRaftN id ∗
        kvrCluster γr vs ∗ isCommittedLogLb γr.cluster l ∗ ownConfChangeI c DFrac.discard (some o) ∗
        cfgAt γr cs0 m k ∗ appNode γr n l k m ∗ nodeRunning n γr.cluster kvrRaftN q }}
      (App (Val #(methods node.ty.PointerType go!"ApplyConfChange" #n)) (Val #c))
    {{ (csp' : Loc), RET #csp'; ∃ (m' : Membership) (c' : ConfStateM),
        ⌜GMap.size m'.ids < 2 ^ 61⌝ ∗ csOpt csp' DFrac.discard c' ∗ cfgAt γr c' m' (k + 1) ∗
        appNode γr n l (k + 1) m' ∗ nodeRunning n γr.cluster kvrRaftN q }} := by
  iintro %Φ ⟨#Hraft, #Hnode, #Hcl, #Hl, #Hcc, #Hc, Hn, Hlive⟩ HΦ
  unfold cfgAt
  icases Hc with ⟨%Hcs, #Hca⟩
  unfold appNode
  icases Hn with ⟨%v, Hv, #Hdl, #Hsk, %Hvm⟩
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
  wp_apply wp_ACC n γr.cluster kvrRaftN id c o o l k e v m' Hva hk
    (ccDecode_isConfChange hd) (by rw [Hvm]; exact Hstep) (by rw [Hvm]; exact Hstep)
    $$ [$Hraft $Hnode $Hic $Hd $Hcc $Hv $Hdl $Hsk] as %csp' %cs Hr
  icases Hr with (⟨Hcs', Hv', %Hcsm⟩ | ⟨%Hnull, #Hst⟩)
  · imod csPts_persist csp' (DFrac.own 1) cs true $$ Hcs' with #Hcs'
    imodintro
    iapply HΦ
    iexists m', cs
    iframe Hlive
    isplitr
    · ipureintro; obtain ⟨m'', h1, h2⟩ := hok; rw [h1] at Hstep; cases Hstep; exact h2
    isplitr
    · unfold csOpt; iright; iapply csPts_weaken csp' DFrac.discard cs true $$ Hcs'
    isplitr
    · iframe Hca'; ipureintro; exact Hcsm
    iexists ⟨k + 1, m'⟩
    iframe Hv' Hdl
    isplitl
    · iapply skippedIn_noConf
      intro j e' h1 h2; simp only at h1 h2; omega
    · ipureintro; exact ⟨rfl, Nat.le_refl _⟩
  · iexfalso
    iapply nodeRunning_stopped n γr.cluster kvrRaftN q
    iframe Hlive Hst

end laws

end kvreconf
end EtcdGrove
end Perennial
