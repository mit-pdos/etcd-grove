/-
Lean-first (no Rocq counterpart).

# The applier's lemmas over the store's invariant (2026-11-01, durability stage II (f))

kvreconf's `ReadLemmas` (`kvr_read_minted`), `ConfLemmas` (`rkv_confShaped`), `ApplyConfLemmas`
(`cfgAt`, `conf_reject`, `wp_conf_apply`) and `EntryLemmas` (`appNode_noConf`, `repOwn_other`) at
kvdurable's predicates (`rkvInv`, `kdCluster`, `appNode`, `repOwn`: the same bodies at `KdNames`);
their proofs are kvreconf's. The lemmas of those files that name none of the store's predicates are
used from kvreconf.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.DefsLaws
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ReadLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ApplyConfLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.EntryLemmas
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvreconf.ConfStep

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (decodeReadCtxB MintOk ConfOk ConfShaped odOf logHist kvFold AppliedOk kvrRule kvrRule_step
  kvrRule_decoded)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section laws
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- **Past a committed conf entry** (see the file header): the store's decision, recorded, and the
configuration after it. -/
theorem kd_confAt_conf (γ : Cluster) (N : Namespace) (E : CoPset) (l : List LogEntry) (k : Nat)
    (e : LogEntry) (m : Membership) (hk : l[k]? = some e) (he : e.isConfChange)
    (hE : ↑kdConfN ⊆ E) :
    ⊢ isCluster (GF := GF) γ N ∗ confPolicy γ kdConfN kvrRule ∗ isCommittedLogLb γ l ∗
        confAt γ k m ={E}=∗
      ∃ m', ⌜(ConfDecision.ofRule (kvrRule (l.take k) m e)).step m = some m'⌝ ∗
        confDecided γ k (ConfDecision.ofRule (kvrRule (l.take k) m e)) ∗ confAt γ (k + 1) m' := by
  obtain ⟨m', hm'⟩ := kvrRule_step (l.take k) m e
  iintro ⟨#Hc, #Hp, #Hl, #Hm⟩
  imod confPolicy_decide γ N kdConfN E kvrRule l k e m m' hk he hE hm' $$ [$Hc $Hp $Hl $Hm] with #Hd
  imodintro
  ihave H := confAt_decided γ k m _ $$ [$Hm $Hd]
  icases H with ⟨%m'', %h'', #H''⟩
  iexists m''
  iframe Hd H''
  ipureintro; exact h''

/-- **A read state's context is the one minted where it decodes to** (see the file header). -/
theorem kd_read_minted (γ : KdNames) (c c0 : List w8) (i : w64) (rp s : w64) (key : List w8)
    (E : CoPset) (HE : ↑kdRkvN ⊆ E) (Hd : decodeReadCtxB c = some (rp, s, key)) :
    ⊢ rkvInv (GF := GF) γ -∗ readStateOk γ.r.cluster kdRaftN c i -∗
      (rp, s) ↪[γ.r.rmint]□ c0 ={E}=∗ ⌜c0 = c⌝ := by
  unfold rkvInv rkvInvBody
  iintro #Hinv #Hok #Hmint
  iinv Hinv with ⟨%ops, %nn, %Mi, %RS, %RMi, %O, %U, >Hcore, Hslots⟩ Hclose
  iunfold kvCore at Hcore
  icases Hcore with ⟨Hops, Hval, Hrc, Hopn, HMi, HRS, HRMi, HO, %HMint, %HMod, %Hsh⟩
  ihave %HcU := readStateOk_used γ.r.cluster kdRaftN c i U $$ [$Hok $Hrc]
  obtain ⟨⟨r1, s1⟩, Hk⟩ := HMint.2.2.2 c HcU
  obtain ⟨_, _, _, key1, Hkl, Hc⟩ := HMint.2.1 r1 s1 c Hk
  rw [Hc, kvreconf.decodeReadCtxB_readCtxB _ _ _ Hkl] at Hd
  cases Hd
  icases ghost_map_lookup $$ HRMi Hmint with %H0
  rw [Hk] at H0
  cases H0
  imod Hclose $$ [Hops Hval Hrc Hopn HMi HRS HRMi HO Hslots] with -
  · inext
    iexists ops, nn, Mi, RS, RMi, O, U
    iframe Hslots
    unfold kvCore
    iframe
    ipureintro; exact ⟨HMint, HMod, Hsh⟩
  imodintro
  ipureintro; rfl

/-- **Every committed conf entry is shaped** (the store's invariant, `kvreconf.confShaped_of_ops`). -/
theorem kd_confShaped (γ : KdNames) (l : List LogEntry) (E : CoPset) (hE : ↑kdRkvN ⊆ E) :
    ⊢ rkvInv (GF := GF) γ -∗ isCommittedLogLb γ.r.cluster l ={E}=∗
      ⌜∀ e ∈ l, e.isConfChange → ConfShaped e⌝ := by
  unfold rkvInv rkvInvBody
  iintro #Hinv #Hl
  iinv Hinv with ⟨%ops, %nn, %Mi, %RS, %RMi, %O, %U, >Hcore, Hslots⟩ Hclose
  iunfold kvCore at Hcore
  icases Hcore with ⟨Hops, Hrest⟩
  ihave %Hp := ownCommittedOps_lb_prefix γ.r.cluster ops l $$ [$Hops $Hl]
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
  exact kvreconf.confShaped_of_ops l ops Hp Hsh

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

/-- `repOwn`'s configuration facts at `k` entries applied: the configuration `c` denotes `m`,
raft's configuration there. -/
def cfgAt (γ : KdNames) (c : ConfStateM) (m : Membership) (k : Nat) : IProp GF :=
  iprop(⌜confStateIs c m⌝ ∗ confAt γ.r.cluster k m)

instance cfgAt_persistent (γ : KdNames) (c : ConfStateM) (m : Membership) (k : Nat) :
    Persistent (cfgAt (GF := GF) γ c m k) := by
  unfold cfgAt; infer_instance


/-- The configuration `validConf` reads is well formed and restorable. -/
theorem cfgAt_wf (γ : KdNames) (c : ConfStateM) (m : Membership) (k : Nat) :
    cfgAt (GF := GF) γ c m k ⊢ ⌜confStateIs c m ∧ m.WellFormed ∧ m.Restorable⌝ := by
  unfold cfgAt
  iintro ⟨%Hcs, #Hca⟩
  ihave %H := confAt_wf γ.r.cluster k m $$ Hca
  ipureintro; exact ⟨Hcs, H⟩

/-- **A rejected conf entry** (see the file header). -/
theorem conf_reject (γ : KdNames) (vs : List w64) (n : Loc)
    (l : List LogEntry) (e : LogEntry) (o : ConfChangeIM) (c : ConfStateM)
    (m : Membership) (k : Nat) (E : CoPset) (hk : l[k]? = some e) (hd : ccDecode e = some o)
    (hno : ¬ ConfOk o m) (hE : ↑kdConfN ⊆ E) :
    ⊢ kdCluster γ vs -∗ isCommittedLogLb γ.r.cluster l -∗ cfgAt γ c m k -∗
      appNode γ n l k m ={E}=∗ cfgAt γ c m (k + 1) ∗ appNode γ n l (k + 1) m := by
  iintro #Hcl #Hl #Hc Hn
  unfold cfgAt
  icases Hc with ⟨%Hcs, #Hca⟩
  iunfold kdCluster at Hcl
  icases Hcl with ⟨#Hic, #Hpol, -⟩
  imod kd_confAt_conf γ.r.cluster kdRaftN E l k e m hk (ccDecode_isConfChange hd) hE
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
  · iapply skippedIn_snoc γ.r.cluster l v.applied k Hvm.2
    iframe Hsk Hd
  · ipureintro; exact ⟨Hvm.1, by omega⟩

/-- **An accepted conf entry applied to the node** (see the file header): the applier's fraction
of `nodeRunning` refutes the stopped answer. -/
theorem wp_conf_apply (wp_ACC : node.ApplyConfChange.spec (GF := GF) (hG := hG)) (γ : KdNames) (vs : List w64) (id : w64)
    (n : Loc) (q : Qp) (l : List LogEntry) (e : LogEntry) (o : ConfChangeIM) (c : GoInterface)
    (cs0 : ConfStateM) (m : Membership) (k : Nat) (hk : l[k]? = some e)
    (hd : ccDecode e = some o) (hok : ConfOk o m) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗ isNode n γ.r.cluster kdRaftN id ∗
        kdCluster γ vs ∗ isCommittedLogLb γ.r.cluster l ∗ ownConfChangeI c DFrac.discard (some o) ∗
        cfgAt γ cs0 m k ∗ appNode γ n l k m ∗ nodeRunning n γ.r.cluster kdRaftN q }}
      (App (Val #(methods node.ty.PointerType go!"ApplyConfChange" #n)) (Val #c))
    {{ (csp' : Loc), RET #csp'; ∃ (m' : Membership) (c' : ConfStateM),
        ⌜GMap.size m'.ids < 2 ^ 61⌝ ∗ csOpt csp' DFrac.discard c' ∗ cfgAt γ c' m' (k + 1) ∗
        appNode γ n l (k + 1) m' ∗ nodeRunning n γ.r.cluster kdRaftN q }} := by
  iintro %Φ ⟨#Hraft, #Hnode, #Hcl, #Hl, #Hcc, #Hc, Hn, Hlive⟩ HΦ
  unfold cfgAt
  icases Hc with ⟨%Hcs, #Hca⟩
  unfold appNode
  icases Hn with ⟨%v, Hv, #Hdl, #Hsk, %Hvm⟩
  -- the store's decision: `apply o`
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨#Hic, #Hpol, -⟩
  imod kd_confAt_conf γ.r.cluster kdRaftN ⊤ l k e m hk (ccDecode_isConfChange hd)
    (fun _ _ => CoPset.mem_full) $$ [$Hic $Hpol $Hl $Hca] with ⟨%m', %Hstep, #Hd, #Hca'⟩
  rw [kvrRule_decoded _ _ _ _ hd, if_pos hok] at Hstep
  simp only [ConfDecision.ofRule, ConfDecision.step] at Hstep
  rw [kvrRule_decoded _ _ _ _ hd, if_pos hok]
  rw [show ConfDecision.ofRule (some o) = .apply o from rfl]
  obtain ⟨Hvm, Hva⟩ := Hvm
  iapply wp_fupd
  wp_apply wp_ACC n γ.r.cluster kdRaftN id c o o l k e v m' Hva hk
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
    iapply nodeRunning_stopped n γ.r.cluster kdRaftN q
    iframe Hlive Hst

/-- Past an entry that is no conf change, the view of the node moves. -/
theorem appNode_noConf (γ : KdNames) (n : Loc) (l : List LogEntry)
    (k : Nat) (e : LogEntry) (m : Membership) (hk : l[k]? = some e) (hc : ¬ e.isConfChange) :
    appNode (GF := GF) γ n l k m ⊢ appNode γ n l (k + 1) m := by
  iintro Hn
  unfold appNode
  icases Hn with ⟨%v, Hv, #Hdl, #Hsk, %Hvm⟩
  · iexists v
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

/-- An entry of no type the store knows leaves the replicated state. -/
theorem repOwn_other (γ : KdNames) (r : Loc) (ap : List LogEntry)
    (idx : w64) (csp : Loc) (m : Membership) (mA : Loc) (A : GMap (List w8) (List w8))
    (e : LogEntry) (ht : e.type ≠ W32 0) (hc : ¬ e.isConfChange)
    (hlen : (ap.length : Int) + 1 < 2 ^ 61) :
    isCommittedLogLb (GF := GF) γ.r.cluster (ap ++ [e]) ∗ repOwn γ r ap idx csp m mA A ⊢
      repOwn γ r (ap ++ [e]) idx csp m mA A := by
  iintro ⟨#Hce, Hown⟩
  iunfold repOwn at Hown
  iNamed Hown
  have Hod : odOf e = none := by
    unfold odOf; rw [if_neg]; rintro ⟨h, _⟩; exact ht h
  have Hlh : logHist (ap ++ [e]) = logHist ap := by rw [kvreconf.logHist_snoc, Hod]; rfl
  unfold repOwn
  iexists mK, K, c
  iframe HmK HK HmA HA Hcs Hidx HcsO Hce
  isplitr
  · ipureintro; simp; omega
  isplitr
  · ipureintro; rw [Hlh]; exact Hval
  isplitr
  · ipureintro; rw [Hlh]; exact HA
  isplitr
  · ipureintro; exact Hcsm
  isplitr
  · ipureintro; exact Hsz
  rw [List.length_append, List.length_singleton]
  iapply kvreconf.kvr_confAt_normal γ.r.cluster (ap ++ [e]) ap.length e m (by simp) hc
  iframe Hce Hcfg

/-- A conf change frozen read-only (see the file header). -/
theorem kd_ownConfChangeV2_persist (p : Loc) (dq : DFrac) (m : ConfChangeV2M) :
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

end kvdurable
end EtcdGrove
end Perennial
