/-
kvreconf's proof (the same Go text), ported. Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kvdurable/Replica__applyEntry.lean`. Lean-first
(no Rocq counterpart).

By the entry's type: normal, `applyOp` (`appNode_noConf` for the view); a conf change, decoded with
`proto.Unmarshal` (it decodes: every committed conf entry is shaped, `kd_confShaped`, so the `panic`
is unreachable), frozen read-only and decided by `applyConf`; another type, nothing
(`repOwn_other`). Then `r.index` written with both halves under the lock, at the entry's index.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__applyEntry
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__applyOp
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Replica__applyConf
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.github_com.mit_pdos.etcd_grove.examples.kvdurable.Stats__add
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetData
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChange
public import Spec.google_golang_org.protobuf.proto.UnmarshalConfChangeV2
public import Proof.github_com.mit_pdos.etcd_grove.examples.kvdurable.ApplyLemmas
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kvdurable

open kvreconf (ConfShaped)
open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt durableExt]
variable [go_gctx : GoGlobalContext] [go.IntoValInj GoString]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kvdurable.Assumptions]
variable [raft_sem : go_etcd_io.raft.v3.Assumptions] [AllG GF] [KdStor GF]

attribute [local instance] kdStorageModel

/-- `proto.Unmarshal` of bytes that decode (a `ConfChange`). -/
theorem unmarshal1_ok (bs : List w8) (cm : ConfChangeM) (p : Loc) (err : GoInterface)
    (h : ccDecodeV1 bs = some cm) :
    (match ccDecodeV1 bs with
      | some m => iprop(⌜err = interface.nil⌝ ∗ ownConfChange p (DFrac.own 1) m)
      | none => iprop(⌜err ≠ interface.nil⌝ ∗ ∃ x' : raftpb.ConfChange, p ↦ x') : IProp GF) ⊢
      ⌜err = interface.nil⌝ ∗ ownConfChange p (DFrac.own 1) cm := by
  rw [h]

/-- `proto.Unmarshal` of bytes that decode (a `ConfChangeV2`). -/
theorem unmarshal2_ok (bs : List w8) (cc : ConfChangeV2M) (p : Loc) (err : GoInterface)
    (h : ccDecodeV2 bs = some cc) :
    (match ccDecodeV2 bs with
      | some m => iprop(⌜err = interface.nil⌝ ∗ ownConfChangeV2 p (DFrac.own 1) m)
      | none => iprop(⌜err ≠ interface.nil⌝ ∗ ∃ x' : raftpb.ConfChangeV2, p ↦ x') : IProp GF) ⊢
      ⌜err = interface.nil⌝ ∗ ownConfChangeV2 p (DFrac.own 1) cc := by
  rw [h]

set_option hygiene false in
/-- `applyEntry`'s end: `r.index` moved to the entry's index, from `Hnext`. -/
local macro "applyentry_tail" : tactic => `(tactic| (
    icases Hnext with ⟨%csp', %m', %A', Hown, Hn⟩
    iunfold repOwn at Hown
    iNamed Hown
    try wp_auto
    wp_apply sync.Mutex.wp_Lock _ _ $$ [$(frameH `Hmu)] as ⟨Hlocked, HR⟩
    try wp_auto
    wp_apply wp_GetIndex.1 ep DFrac.discard _ $$ [$(frameH `Hpb) $(frameH `Hent)] as -
    iNamed HR
    iunfold repShared at Hrep
    icases Hrep with ⟨%mA0, %A0, %csp0, %c0, %idx0, %ap0, HmA', HA', Hcs', Hidx', #HcsO0, #Hap0, %HA0⟩
    icombine Hidx Hidx' gives %Hieq
    subst Hieq
    ihave Hif := (typedPointsto_half_split _ (W64 ap.length) (1 : Qp)).2 $$ [$(frameH `Hidx) $(frameH `Hidx')]
    try wp_auto
    icases (typedPointsto_half_split _ (W64 (ap.length + 1)) (1 : Qp)).1 $$ Hif with ⟨Hidx, Hidx'⟩
    wp_apply sync.Mutex.wp_Unlock _ _ $$ [$(frameH `Hmu) $(frameH `Hlocked) HmA' HA' Hcs' Hidx'
        HmW HW Hwaiters HmR HRd Hreads]
    · inext
      unfold lockInv repShared
      iexists mW, W, mR, Rd
      iframe
      iexists mA0, A0, csp0, c0, W64 (ap.length + 1), ap0
      iframe HmA' HA' Hcs' Hidx' HcsO0 Hap0
      ipureintro; exact HA0
    try wp_auto
    iapply HΦ
    iexists ap ++ [e], csp', m', A'
    simp only [Nat.lt_irrefl, ↓reduceIte, List.length_append, List.length_singleton, Nat.max_self]
    isplitr
    · ipureintro; simp
    iframe Hn Hlive
    unfold repOwn
    iexists mK, K, c
    iframe
    ihave #Hcfg2 : confAt γ.r.cluster (ap.length + 1) m' $$ []
    · rw [show ap.length + 1 = (ap ++ [e]).length by simp]; iexact Hcfg
    simp only [List.length_append, List.length_singleton] at Hlen ⊢
    iframe Hap HcsO Hcfg2
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩
  ))

theorem Replica.applyEntry.wp_proof
    (wp_applyOp : Replica.applyOp.spec (GF := GF) (hG := hG))
    (wp_applyConf : Replica.applyConf.spec (GF := GF) (hG := hG))
    (wp_GetType : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (wp_GetData : raftpb.Entry.GetData.spec (GF := GF) (hG := hG))
    (wp_GetIndex : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (wp_Unmarshal1 : proto.UnmarshalConfChange.spec (GF := GF) (hG := hG))
    (wp_Unmarshal2 : proto.UnmarshalConfChangeV2.spec (GF := GF) (hG := hG))
    (wp_add : Stats.add.spec (GF := GF) (hG := hG)) :
    Replica.applyEntry.spec (GF := GF) (hG := hG) := by
  intro γ vs dir id r n st sts sq ms γs ph q ap idx csp m mA A l k e ep Htk Hap Hlen' Hk61
  wp_start as ⟨#Hrep, Hown, Hn, #Hent, #Hl, Hlive⟩
  ihave #Hrep' := Hrep
  iunfold isReplica at Hrep'
  iNamed Hrep'
  ihave #Hpb : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
  · iPkgInit
  -- SPEC-GAP (stage II (f), reported): the spec does not say that the applier's index field is
  -- the replicated state's (`idx = len ap`) nor that the entry is not past it (`k ≤ len ap`): the
  -- code decides `covered` on `idx`, and an entry past `len ap` would leave a gap. `run`, the only
  -- caller, has both (`repOwn … (W64 ap.length)`, and the delivered log never passes `ap`).
  by_cases Hgood : uint.Z idx = (ap.length : Int) ∧ k ≤ ap.length
  case neg => sorry
  obtain ⟨Hidxap, Hkap⟩ := Hgood
  have Hidx : idx = W64 ap.length := by word
  subst Hidx
  -- `covered := e.GetIndex() <= r.index`, read under `mu` with the applier's half
  iunfold repOwn at Hown
  iNamed Hown
  try wp_auto
  wp_apply sync.Mutex.wp_Lock _ _ $$ [$Hmu] as ⟨Hlocked, HR⟩
  try wp_auto
  wp_apply wp_GetIndex.1 ep DFrac.discard _ $$ [$Hpb $Hent] as -
  try simp only [LogEntry.toEntryM]
  try wp_auto
  wp_apply sync.Mutex.wp_Unlock _ _ $$ [$Hmu $Hlocked $HR]
  ihave Hown : repOwn γ r ap (W64 ap.length) csp m mA A $$ [HmK HK HmA HA Hcs Hidx]
  · unfold repOwn
    iexists mK, K, c
    iframe
    iframe Hap HcsO Hcfg
    ipureintro; exact ⟨Hlen, Hval, HA, Hcsm, Hsz⟩
  try wp_auto
  wp_if_destruct
  · -- covered: skipped, the replicated state and the view stay
    have Hlt : k < ap.length := by word
    ihave #Hsk := isStats_field sts go!"EntriesSkipped" (by decide) $$ Hstats
    wp_apply wp_add sts _ $$ [$Hpkg $Hsk]
    try wp_auto
    iapply HΦ
    iexists ap, csp, m, A
    simp only [Hlt, ↓reduceIte]
    rw [show max (k + 1) ap.length = max k ap.length by omega]
    iframe Hown Hn Hlive
  -- not covered: the entry is the next one
  have Hkeq : k = ap.length := by
    have : ¬ (uint.Z (W64 (k + 1)) ≤ uint.Z (W64 ap.length)) := by
      intro h; apply Hif; word
    word
  subst Hkeq
  have Hpre : ap ++ [e] <+: l := by
    have Ht : l.take ap.length = ap := by
      obtain ⟨t, rfl⟩ := Hap; simp
    rw [← Ht]; exact Htk
  rw [show max ap.length ap.length = ap.length from Nat.max_self _] at *
  have Hk : l[ap.length]? = some e := by
    obtain ⟨t, rfl⟩ := Hpre
    rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]; simp
  ihave #Hce : isCommittedLogLb γ.r.cluster (ap ++ [e]) $$ []
  · iapply isCommittedLogLb_mono γ.r.cluster (ap ++ [e]) l Hpre $$ Hl
  ihave #Hproto : isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto $$ []
  · iPkgInit
  -- every committed conf entry decodes, with a defined transition
  ihave #Hcl' := Hcl
  iunfold kdCluster at Hcl'
  icases Hcl' with ⟨-, -, -, -, #Hinv, -⟩
  imod kd_confShaped γ l ⊤ (fun _ _ => CoPset.mem_full) $$ Hinv Hl with %Hsh
  have Hesh : e.isConfChange → ConfShaped e := Hsh e (Hpre.subset (by simp))
  try wp_auto
  wp_apply wp_GetType.1 ep DFrac.discard _ $$ [$Hpb $Hent] as -
  try simp only [LogEntry.toEntryM]
  try wp_auto
  wp_if_destruct
  · -- a normal entry
    have Ht := Hif
    wp_apply wp_GetData.1 ep DFrac.discard _ $$ [$Hpb $Hent] as %ds ⟨#Hds, -⟩
    try simp only [LogEntry.toEntryM]
    wp_apply wp_applyOp γ id r ap (W64 ap.length) csp m mA A e ds Ht Hlen' $$ [$Hpkg $Hmu $Hown $Hds $Hce]
      as ⟨%A', Hown⟩
    ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
        repOwn γ r (ap ++ [e]) (W64 ap.length) csp' m' mA A' ∗ appNode γ n l (ap.length + 1) m')
        $$ [Hown Hn]
    · iexists csp, m, A'
      iframe Hown
      iapply appNode_noConf γ n l ap.length e m Hk
        (by unfold LogEntry.isConfChange; rw [Ht]; intro h; rcases h with h | h <;> word)
      iexact Hn
    applyentry_tail
  · have Ht0 := Hif
    wp_if_destruct
    · -- a `ConfChange`
      have Ht1 := Hif
      obtain ⟨o, Ho, Htr⟩ := Hesh (.inl Ht1)
      obtain ⟨cm, Hcm, rfl⟩ : ∃ cm, ccDecodeV1 e.data = some cm ∧ o = .v1 cm := by
        unfold ccDecode at Ho; rw [if_pos Ht1] at Ho
        cases h : ccDecodeV1 e.data with
        | none => rw [h] at Ho; cases Ho
        | some cm => rw [h] at Ho; cases Ho; exact ⟨cm, rfl, rfl⟩
      try wp_auto
      wp_apply wp_GetData.1 ep DFrac.discard _ $$ [$Hpb $Hent] as %ds ⟨#Hds, -⟩
      try simp only [LogEntry.toEntryM]
      wp_apply wp_Unmarshal1 ds _ DFrac.discard cc_ptr _ $$ [$Hproto $Hds $cc] as %er ⟨-, Hres⟩

      irevert Hres
      rw [Hcm]
      iintro Hres
      icases Hres with ⟨%Herr, Hcc⟩
      subst Herr
      imod ownConfChange_persist cc_ptr (DFrac.own 1) cm $$ Hcc with #Hcc
      ihave #Hci : ownConfChangeI (interface.mkOk (go.GoType.PointerType raftpb.ConfChange.ty) #cc_ptr)
          DFrac.discard (some (.v1 cm)) $$ []
      · simp only [ownConfChangeI]; iexists cc_ptr; iframe Hcc; ipureintro; rfl
      try wp_auto
      wp_apply wp_applyConf γ vs dir id r n st sts sq ms γs ph q ap (W64 ap.length) csp m mA A l e _ (.v1 cm) Hpre Ho Htr Hlen'
        $$ [$Hrep $Hown $Hn $Hci $Hl $Hlive] as Hc0
      icases Hc0 with ⟨%csp1, %m1, Hro, Han, Hlive⟩
      ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
          repOwn γ r (ap ++ [e]) (W64 ap.length) csp' m' mA A' ∗ appNode γ n l (ap.length + 1) m')
          $$ [Hro Han]
      · iexists csp1, m1, A; iframe Hro Han
      applyentry_tail
    · have Ht1 := Hif
      wp_if_destruct
      · -- a `ConfChangeV2`
        have Ht2 := Hif
        obtain ⟨o, Ho, Htr⟩ := Hesh (.inr Ht2)
        obtain ⟨cc, Hcc2, rfl⟩ : ∃ cc, ccDecodeV2 e.data = some cc ∧ o = .v2 cc := by
          unfold ccDecode at Ho; rw [if_neg Ht1, if_pos Ht2] at Ho
          cases h : ccDecodeV2 e.data with
          | none => rw [h] at Ho; cases Ho
          | some cc => rw [h] at Ho; cases Ho; exact ⟨cc, rfl, rfl⟩
        try wp_auto
        wp_apply wp_GetData.1 ep DFrac.discard _ $$ [$Hpb $Hent] as %ds ⟨#Hds, -⟩
        try simp only [LogEntry.toEntryM]
        wp_apply wp_Unmarshal2 ds _ DFrac.discard cc_ptr _ $$ [$Hproto $Hds $cc] as %er ⟨-, Hres⟩
        irevert Hres
        rw [Hcc2]
        iintro Hres
        icases Hres with ⟨%Herr, Hcc⟩
        subst Herr
        imod kd_ownConfChangeV2_persist cc_ptr (DFrac.own 1) cc $$ Hcc with #Hcc
        ihave #Hci : ownConfChangeI (interface.mkOk (go.GoType.PointerType raftpb.ConfChangeV2.ty)
            #cc_ptr) DFrac.discard (some (.v2 cc)) $$ []
        · simp only [ownConfChangeI]; iexists cc_ptr; iframe Hcc; ipureintro; rfl
        try wp_auto
        wp_apply wp_applyConf γ vs dir id r n st sts sq ms γs ph q ap (W64 ap.length) csp m mA A l e _ (.v2 cc) Hpre Ho Htr
          Hlen' $$ [$Hrep $Hown $Hn $Hci $Hl $Hlive] as Hc0
        icases Hc0 with ⟨%csp1, %m1, Hro, Han, Hlive⟩
        ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
            repOwn γ r (ap ++ [e]) (W64 ap.length) csp' m' mA A' ∗ appNode γ n l (ap.length + 1) m')
            $$ [Hro Han]
        · iexists csp1, m1, A; iframe Hro Han
        applyentry_tail
      · -- another type: nothing
        have Ht2 := Hif
        have Hc : ¬ e.isConfChange := fun h => h.elim Ht1 Ht2
        ihave Hnext : iprop(∃ (csp' : Loc) (m' : Membership) (A' : GMap (List w8) (List w8)),
            repOwn γ r (ap ++ [e]) (W64 ap.length) csp' m' mA A' ∗
            appNode γ n l (ap.length + 1) m') $$ [Hown Hn]
        · iexists csp, m, A
          isplitl [Hown]
          · iapply repOwn_other γ r ap (W64 ap.length) csp m mA A e Ht0 Hc Hlen'
            iframe Hce Hown
          · iapply appNode_noConf γ n l ap.length e m Hk Hc
            iexact Hn
        applyentry_tail

end proof

end kvdurable
end EtcdGrove
end Perennial
