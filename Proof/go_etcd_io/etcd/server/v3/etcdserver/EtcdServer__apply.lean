/-
Proof of `Spec/EtcdServer__apply.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__apply
public import Spec.go_uber_org.zap.Logger__Debug
public import Spec.go_uber_org.zap.Int
public import Spec.go_uber_org.zap.Uint64
public import Spec.go_uber_org.zap.Stringer
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__ConsistentIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentApplyingIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.cindex.consistentIndex__SetConsistentIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setAppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setTerm
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyConfChange
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVApply
public import Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetId
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members
public import Proof.go_etcd_io.raft.v3.FrameH

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.cindex
  go_etcd_io.etcd.server.v3.storage go_etcd_io.etcd.server.v3.etcdserver

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- Loading `ci` changes only `k`, and not `ciEff`. -/
theorem stLoaded_facts (γ : ApplyNames) (st : ApplyState) :
    (stLoaded γ st).pending = st.pending ∧ (stLoaded γ st).p = st.p ∧
      (stLoaded γ st).eff = st.eff ∧ ciEff γ (stLoaded γ st).k = ciEff γ st.k := by
  unfold stLoaded
  split
  · rename_i h
    refine ⟨rfl, rfl, rfl, ?_⟩
    unfold ciEff
    rw [ite_eq_left h]
    split <;> rfl
  · exact ⟨rfl, rfl, rfl, rfl⟩

set_option hygiene false in
/-- A conf change, after `applyConfChange` (`xj` unchanged: no KV effect): the KV model's step,
the applied index (`setAppliedIndex`) and term (both conf-change branches: applied, or
skipped by the consistent index). -/
local macro "cc_kv_applied" : tactic => `(tactic| (
    (try wp_auto)
    wp_apply hGI $$ [He] as -
    · iframe He
    icases srvApplyKV_idxCert s E ρ.wait xj $$ HKV with ⟨HKV, #Hcert⟩
    ihave %Hlxj := idxCert_len E.γ.idx xj.log $$ Hcert
    have hcc0 : kvEntry γr.kv.c0 xj.chain xj.log m = xj.log :=
      kvEntry_nonwrite _ _ _ m (Or.inr (Or.inl (by rw [h1]; decide)))
    imod kv_applied_step E γr (A ++ ms.take (sint.nat j)) m xj (by rw [hcc0]; exact Hlxj)
      $$ Hkvi Hka HlbJ with ⟨%Hpe, Hka⟩
    ihave ⟨Hka, #HkL⟩ := kvApplied_next γr (A ++ ms.take (sint.nat j)) m xj xj m.index hiA
      hcc0.symm Hpe.2.1 $$ Hka
    imod applied_predeposit s E γr aw m.index xj.log xj.log (by omega) (List.prefix_refl _)
      $$ Hainv Hao Hlog HkL with Hpre
    wp_apply (hSet1 s E γr aw m.index xj.log) $$ [Hpre] as ⟨Hao, -, #Hlog'⟩
    · iframe #; iframe Hpre
    (try wp_auto)
    wp_apply hGT $$ [He] as -
    · iframe He
    wp_apply hSet2 $$ [$(frameH `Hat)]
    (try wp_auto)
  ))

set_option hygiene false in
/-- A conf change's response (both conf-change branches, either value of the loop's
`shouldStop`): `GetId`, the cluster's members, the `Trigger` of the wait (no waiter), the next
iteration up to its witnesses. -/
local macro "cc_respond" : tactic => `(tactic| (
    (try wp_auto)
    wp_apply (wp_ownCCV1_GetId hId cc_ptr DFrac.discard cm' (ccIdOf m.data)
      (by rw [hIdEq, ccIdOf_of_decode Hdec])) $$ [Hcc] as Hcc
    · iframe Hcc
    (try wp_auto)
    wp_apply hMem sv.cluster $$ [] as %msl -
    · iframe #
    (try wp_auto)
    wp_alloc rsp as Hrsp
    (try wp_auto)
    ihave #Hwok2 := Hwok
    iunfold waitInv at Hwok2
    icases Hwok2 with ⟨⟨%RD0, Hwok2⟩, -⟩
    iunfold isWait at Hwok2
    icases Hwok2 with ⟨%wi, %hw, -, #Htrig, -⟩
    simp only [hw]
    (try wp_auto)
    wp_apply Htrig
    · iright; iright
      iunfold waitTrig
      iintro %Ψ HR
      iexfalso
      iapply Hccf $$ HR
    (try wp_auto)
    wp_apply hGI $$ [He] as -
    · iframe He
    wp_apply hGT $$ [He] as -
    · iframe He
    (try wp_auto)
    wp_for_post
    iframe
  ))

set_option maxHeartbeats 800000 in
theorem EtcdServer.apply.wp_proof
    (hDebug : zap.Logger.Debug.spec (GF := GF) (hG := hG))
    (hInt : zap.Int'.spec (GF := GF) (hG := hG))
    (hU64 : zap.Uint64.spec (GF := GF) (hG := hG))
    (hStr : zap.Stringer.spec (GF := GF) (hG := hG))
    (hCI : consistentIndex.ConsistentIndex.spec (GF := GF) (hG := hG))
    (hSAI : consistentIndex.SetConsistentApplyingIndex.spec (GF := GF) (hG := hG))
    (hSCI : consistentIndex.SetConsistentIndex.spec (GF := GF) (hG := hG))
    (hGI : raftpb.Entry.GetIndex.spec (GF := GF) (hG := hG))
    (hGT : raftpb.Entry.GetTerm.spec (GF := GF) (hG := hG))
    (hGTy : raftpb.Entry.GetType.spec (GF := GF) (hG := hG))
    (hAEN : EtcdServer.applyEntryNormal.spec (GF := GF) (hG := hG))
    (hSet1 : EtcdServer.setAppliedIndex.spec (GF := GF) (hG := hG))
    (hSet2 : EtcdServer.setTerm.spec (GF := GF) (hG := hG))
    (hMU : pbutil.MustUnmarshalMessage.spec (GF := GF) (hG := hG))
    (hACC : EtcdServer.applyConfChange.spec (GF := GF) (hG := hG))
    (hId : raftpb.ConfChange.GetId.spec (GF := GF) (hG := hG))
    (hMem : membership.RaftCluster.Members.spec (GF := GF) (hG := hG)) :
    EtcdServer.apply.spec (GF := GF) (hG := hG) := by
  have hGI := wp_entryAt_GetIndex hGI
  have hGT := wp_entryAt_GetTerm hGT
  have hGTy := wp_entryAt_GetType hGTy
  intro s γ ci TM E ρ b es ents ms f0 ep cs rac st a at0 x γr A γp hne hfrom hok hEok
  wp_start as ⟨#Hsrv, #Hbw, #Hes, #Hents, Hst, Hbe, Happ, Hcs, Hlr, Hgr, HKV, Hao, #Hlog0, #Hbc,
    #HWP, #HWA0, Hfs, Hka, HRS, #Hkb⟩
  ihave #Hsrv0 := Hsrv
  ihave #Pmem : isPkgInit (PROP := IProp GF)
      pkg_id.go_etcd_io.etcd.server.v3.etcdserver.api.membership $$ []
  · iPkgInit
  iunfold isServer at Hsrv
  icases Hsrv with ⟨%Hrd, #Hsci, ⟨%sv, #Hfl⟩, #Hat, -, #Hrn⟩
  ihave #Hat' := Hat
  iunfold srvAtomics at Hat'
  icases Hat' with ⟨#Hainv, -, #Hkvi⟩
  iunfold kvBatch at Hkb
  icases Hkb with ⟨#HlbB, %HkB⟩
  iunfold batchCommittedIdx at Hbc
  ihave #Hsci' := Hsci
  iunfold isServerCI at Hsci'
  icases Hsci' with ⟨#Hcif, #Hci, #Hinv⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, %HE, %HEo, #Hhook, #Hls, #Hlok, #Hfc, #Hals,
    #Hcl, #Hrc, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
  obtain ⟨γB, HROeq, -⟩ := HEo.2.2
  ihave #Hzap : isPkgInit (PROP := IProp GF) pkg_id.go_uber_org.zap $$ []
  · iPkgInit
  ihave %Hesl := ownSlice_len _ _ _ $$ Hes
  ihave #Hents2 := Hents
  iunfold entriesAt at Hents2
  icases Hents2 with ⟨%Hel, #Hent⟩
  have Hlen : ms.length = sint.nat es.len := by rw [← Hel]; exact Hesl.1
  wp_auto
  wp_apply hInt as %fl1 -
  wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fl1]
  isplitr
  · ipureintro; rfl
  iintro %fsl1 ⟨-, -⟩
  wp_auto
  wp_apply hDebug $$ []
  · ipureintro; exact Hlgnn
  irename i => cnt
  irename i => iv
  rename_i ivp
  ipersist s
  ipersist raftAdvancedC
  ipersist ep
  ipersist es
  obtain ⟨Hf0pos, Hf0n, Hms⟩ := hfrom
  obtain ⟨Hpend, Hp0⟩ := hok
  have Hf0m1 : uint.Z (f0 - 1) = uint.Z f0 - 1 := by word
  rw [Hf0m1] at Hp0
  ihave HI : (∃ (j : w64) (st' : ApplyState) (a' t' : w64) (csl : Loc) (sb : Bool)
        (ai at' ivv : w64) (xj : apply.ApplyKV) (aw : w64),
      "cnt" ∷ i_ptr ↦ j ∗ "iv" ∷ ivp ↦ ivv ∗ "shouldStop" ∷ shouldStop_ptr ↦ sb ∗
      "appliedi" ∷ appliedi_ptr ↦ ai ∗ "appliedt" ∷ appliedt_ptr ↦ at' ∗
      "Hst" ∷ applyThread γ st' ∗ "Hbe" ∷ applyBackend γ ci b ∗ "Happ" ∷ ciApplying ci a' t' ∗
      "Hcs" ∷ epConfState ep csl ∗ "Hlr" ∷ srvLgReader s ∗ "Hgr" ∷ srvGoRes s ∗ "Hfs" ∷ srvFS s ∗
      "HKV" ∷ srvApplyKV s E ρ.wait xj ∗
      "Hao" ∷ srvAppliedOwn γr aw ∗
      "#Hlog" ∷ appliedLogAt γr aw xj.log ∗
      -- (2026-10-19, D21 M3) the write tokens taken through `aw`
      "#HWA" ∷ srvWTAt γp aw ∗
      "Hka" ∷ kvApplied γr.raft γr.kv (A ++ ms.take (sint.nat j)) xj ∗
      "HRS" ∷ srvRest E γr (A ++ ms.take (sint.nat j)) ∗
      "%Hxs" ∷ ⌜entriesStep (ciEff γ st.k) (ms.take (sint.nat j)) x xj⌝ ∗
      "Hphi" ∷ (∀ (appliedt appliedi : w64) (shouldStop : Bool),
        srvFS s ∗ (∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
          applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
          epConfState ep csl ∗ srvLgReader s ∗ srvGoRes s ∗ srvAppliedOwn γr appliedi ∗
          srvWTAt γp appliedi ∗
          (∃ x' : apply.ApplyKV, srvApplyKV s E ρ.wait x' ∗ ⌜entriesStep (ciEff γ st.k) ms x x'⌝ ∗
            appliedLogAt γr appliedi x'.log ∗ kvApplied γr.raft γr.kv (A ++ ms) x' ∗
            srvRest E γr (A ++ ms)) ∗
          ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
            (ms.getLast?).map EntryModel.term = some appliedt ∧
            loopOk γ st' appliedi ∧
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi) ∧
            shouldStop = false⌝) -∗
        Φ (PairV (PairV #appliedt #appliedi) #shouldStop)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z es.len⌝ ∗
      "%Hstj" ∷ ⌜st'.pending = false ∧
        uint.Z st'.p = max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z j) ∧
        uint.Z (ciEff γ st'.k) = (if sint.Z j = 0 then uint.Z (ciEff γ st.k)
          else max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z j))⌝ ∗
      "%Hlast" ∷ ⌜∀ m : EntryModel, 0 < sint.nat j → ms[sint.nat j - 1]? = some m →
        m.index = ai ∧ m.term = at'⌝ ∗
      "%Haw" ∷ ⌜uint.Z aw = uint.Z f0 - 1 + sint.Z j⌝ ∗ "%Hsb" ∷ ⌜sb = false⌝ : IProp GF)
    $$ [cnt iv shouldStop appliedi appliedt Hst Hbe Happ Hcs Hlr Hgr Hfs HKV Hao HΦ Hka HRS]
  · iexists (W64 0), st, a, at0, cs, false, (W64 0), (W64 0), (W64 0), x, f0 - 1
    simp only [named, show sint.nat (W64 0) = 0 from rfl, List.take_zero,
      List.append_nil]
    iframe
    iframe Hlog0
    isplitr
    · iexact HWA0
    ipureintro
    refine ⟨rfl, by word, ⟨Hpend, ?_, ?_⟩, fun m h => absurd h (by simp), by rw [Hf0m1]; simp, by simp⟩
    · rw [Hp0]; simp
    · simp
  wp_for HI
  wp_if_destruct
  · -- the `j`-th entry
    have hjl : sint.nat j < ms.length := by rw [Hlen]; word
    list_elem ents (sint.nat j) as e
    list_elem ms (sint.nat j) as m
    ihave #He := Hent $$ %(sint.nat j) %e %m %He_lookup %Hm_lookup
    obtain ⟨hmidx, hmtyp⟩ := Hms (sint.nat j) m Hm_lookup
    -- the KV model (unit T1): the entry is the next of the committed raft log
    have hmem : m ∈ ms := List.mem_of_getElem? Hm_lookup
    -- the entry's premise at the KV's log, from its shape and the log's smallness (D19c's move)
    icases srvApplyKV_small s E ρ.wait xj $$ HKV with ⟨%Hsmall, HKV⟩
    have hOk1 : m.typ = W32 0 → entryOk xj m := fun ht =>
      entryOk_of_shape xj m (hEok m hmem) ht Hsmall.1 Hsmall.2
    have hjn' : ((sint.nat j : Nat) : Int) = sint.Z j := by
      unfold sint.nat; exact Int.toNat_of_nonneg Hj.1
    have hlenA : (A ++ ms.take (sint.nat j)).length = A.length + sint.nat j := by
      rw [List.length_append, List.length_take]; omega
    have hiA : uint.Z m.index = uint.Z γr.raft.ai0 + (A ++ ms.take (sint.nat j)).length + 1 := by
      have := HkB.1; rw [hlenA]; push_cast; omega
    have hawA : uint.Z aw = uint.Z γr.raft.ai0 + (A ++ ms.take (sint.nat j)).length := by
      have := HkB.1; rw [hlenA]; push_cast; omega
    have htk : A ++ ms.take (sint.nat j + 1) = A ++ ms.take (sint.nat j) ++ [m] := by
      rw [List.append_assoc, List.take_add_one, Hm_lookup]; rfl
    have hpfx : A ++ ms.take (sint.nat j) ++ [m] <+: A ++ ms := by
      rw [← htk]; exact (List.prefix_append_right_inj A).mpr (List.take_prefix _ _)
    ihave #HlbJ : iprop(srvRLogLb γr.raft (A ++ ms.take (sint.nat j) ++ [m])) $$ []
    · iapply srvRLogLb_mono γr.raft _ _ hpfx $$ HlbB
    ihave #Hewo : iprop(entryWaitOk ρ E m) $$ []
    · iunfold batchWaitOk at Hbw
      iapply Hbw
      ipureintro; exact List.mem_of_getElem? Hm_lookup
    ihave #Hcm : iprop(committedAtLeast γr m.index) $$ []
    · iapply Hbc
      ipureintro; exact List.mem_of_getElem? Hm_lookup
    have hjs : sint.nat (j + W64 1) = sint.nat j + 1 := by
      show (sint.Z (j + W64 1)).toNat = (sint.Z j).toNat + 1
      have : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      rw [this]; omega
    have htk2 : A ++ ms.take (sint.nat (j + W64 1)) = A ++ ms.take (sint.nat j) ++ [m] := by
      rw [hjs]; exact htk
    have hconf : m.typ ≠ W32 0 → batchStep (ciEff γ st.k) m xj xj := by
      intro hn; unfold batchStep; rw [ite_eq_right hn]
    have Hlt : sint.Z j < sint.Z es.len := by
      first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
    (try wp_auto)
    simp only [show (0 ≤ sint.Z j ∧ sint.Z j < sint.Z es.len) from ⟨Hj.1, Hlt⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index es (sint.Z j) ents DFrac.discard e Hj.1 $$ [] as -
    · iframe Hes; ipureintro; exact He_lookup
    (try wp_auto)
    simp only [show (0 ≤ sint.Z j ∧ sint.Z j < sint.Z es.len) from ⟨Hj.1, Hlt⟩, _root_.and_self,
      ↓reduceIte]
    wp_apply wp_load_slice_index es (sint.Z j) ents DFrac.discard e Hj.1 $$ [] as -
    · iframe Hes; ipureintro; exact He_lookup
    (try wp_auto)
    -- `index := s.consistIndex.ConsistentIndex()`
    ihave #Hcipkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.etcdserver.cindex $$ []
    · iPkgInit
    ihave #Hrpkg : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3.raftpb $$ []
    · iPkgInit
    wp_apply_core (wp_ci_get hCI γ ci b st' Hstj.1) $$ [Hst Hbe]
      [cnt iv shouldStop appliedi appliedt Happ Hcs Hlr Hgr Hfs HKV Hao Hphi e Hka HRS]
    · iframe Hcipkg Hci Hinv Hst Hbe
    iintro ⟨Hst, Hbe⟩
    obtain ⟨hlp, hlpp, hlpe, hlc⟩ := stLoaded_facts γ st'
    wp_pure
    wp_pure
    wp_pure
    wp_alloc index_ptr as index
    wp_pure
    wp_pure
    wp_pure
    wp_store
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_pure
    wp_load
    wp_pure
    wp_pure
    -- the Go step resolving `zap.Uint64` gives a time receipt (D19b), for which the budget gives
    -- the entry's write token
    wp_bind (App (Val (GoInstruction (FuncResolve _ _))) (Val _))
    iapply wp_go_step_receipt'
    case hv => exact isPanic_intoVal _
    inext
    iintro Hr -
    iapply wp_value'
    -- (2026-10-19, D21 M3) the token's count, past the entry's index
    have hma : uint.Z m.index = uint.Z aw + 1 := by omega
    imod srvWTPool_take_at s E γp ρ.wait xj aw (by have := hma; word) $$ HWP Hr HWA HKV
      with ⟨Hwt, #HWA1, HKV⟩
    ihave #HWA2 : srvWTAt γp m.index $$ []
    · rw [show m.index = aw + W64 1 by
        apply BitVec.eq_of_toNat_eq
        have h2 : uint.Z m.index = uint.Z (aw + W64 1) := by rw [hma]; word
        simp only [uint.Z] at h2
        exact_mod_cast h2]
      iexact HWA1
    (try wp_auto)
    -- the `Debug` log
    wp_apply hU64 as %fl2 -
    wp_apply hGI $$ [He] as -
    · iframe He
    wp_apply hU64 as %fl3 -
    wp_apply hGT $$ [He] as -
    · iframe He
    wp_apply hU64 as %fl4 -
    wp_apply hGTy $$ [He] as -
    · iframe He
    (try wp_auto)
    wp_apply hStr as %fl5 -
    wp_apply wp_slice_literal (V := go_uber_org.zap.zapcore.Field) [fl2, fl3, fl4, fl5]
    isplitr
    · ipureintro; rfl
    iintro %fsl2 ⟨-, -⟩
    (try wp_auto)
    wp_apply hDebug $$ []
    · ipureintro; exact Hlgnn
    (try wp_auto)
    simp only [api.membership.ApplyV2storeOnly, api.membership.ApplyBoth]
    (try wp_auto)
    wp_apply hGI $$ [He] as -
    · iframe He
    (try wp_auto)
    wp_if_destruct
    · -- above `ci`: `ApplyBoth`
      have hgt : uint.Z (ciEff γ st'.k) < uint.Z m.index := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif) | word
      wp_apply hGI $$ [He] as -
      · iframe He
      wp_apply hGT $$ [He] as -
      · iframe He
      (try wp_auto)
      wp_apply hSAI $$ [Happ] as Happ
      · iframe Happ
      (try wp_auto)
      wp_apply hGTy $$ [He] as -
      · iframe He
      (try wp_auto)
      -- the arithmetic: the entry is the next to process
      obtain ⟨hpend', hp', hc'⟩ := Hstj
      have hjnat : (sint.nat j : Int) = sint.Z j := by
        unfold sint.nat; exact Int.toNat_of_nonneg Hj.1
      have hidxZ : uint.Z m.index = uint.Z f0 + sint.Z j := by rw [hmidx, hjnat]
      have hjlt : sint.Z j < (ms.length : Int) := by
        have := hjl; unfold sint.nat at this; omega
      have hce0 : uint.Z (ciEff γ st.k) ≤ uint.Z (ciEff γ st'.k) := by
        rw [hc']; split <;> omega
      have hpZ : uint.Z st'.p = uint.Z f0 - 1 + sint.Z j := by
        rw [hp']; omega
      have hip : m.index = st'.p + 1 := by
        apply BitVec.eq_of_toNat_eq
        have h1 := hidxZ; have h2 := hpZ
        simp only [uint.Z] at h1 h2 ⊢
        rw [BitVec.toNat_add]; simp; omega
      have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      rcases hmtyp with h0 | ⟨h1, hcc⟩
      · -- a normal entry
        simp only [h0, _root_.decide_true]
        (try wp_auto)
        -- (linkv-txn stage B1) the entry's registration, for the member's own ids
        ihave ⟨%ot, #Hreg⟩ := entryRegd_of_wait ρ E m h0 $$ [Hewo]
        · iframe Hewo; iapply isServer_waitIs $$ Hsrv0
        wp_apply (hAEN s γ ci TM E ρ b e m (stLoaded γ st') true xj γr ot aw
            (A ++ ms.take (sint.nat j))) $$ [Hst Hbe Happ Hlr Hgr Hfs HKV Hwt Hao Hka HRS]
          as ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x1, %out1, HKV, %Hstep1, -, Hpre, Hka, HRS⟩, Hpost⟩
        · rw [ite_eq_left rfl]
          iframe Hsrv0 Hewo He Hst Hbe Happ Hlr Hgr Hfs HKV Hwt Hao Hlog Hcm Hka HRS HlbJ
          isplitr
          · iexact Hreg
          isplitr
          · ipureintro
            exact ⟨hawA, (decide_eq_true ((HkB.2 m hmem).1 (by omega))).symm⟩
          isplitr
          · ipureintro; omega
          ipureintro
          refine ⟨⟨hlp ▸ hpend', hOk1 h0, h0⟩, ?_⟩
          rw [hlpp, hlc]
          refine ⟨hip, by omega, hgt⟩
        have hb1 : batchStep (ciEff γ st.k) m xj x1 := by
          unfold batchStep; rw [ite_eq_left h0]
          refine ⟨out1, ?_⟩
          rw [decide_eq_true (show uint.Z (ciEff γ st.k) < uint.Z m.index by omega)]
          exact Hstep1
        (try rw [ite_eq_left rfl])
        icases Hpost with ⟨Happ, %eff', Hst⟩
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        icases srvApplyKV_idxCert s E ρ.wait x1 $$ HKV with ⟨HKV, #Hcert⟩
        wp_apply (hSet1 s E γr aw m.index x1.log) $$ [Hpre] as ⟨Hao, -, #Hlog'⟩
        · iframe #; iframe Hpre
        (try wp_auto)
        wp_apply hGT $$ [He] as -
        · iframe He
        wp_apply hSet2 $$ [$Hat]
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hGT $$ [He] as -
        · iframe He
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, ⟨m.index, m.index, eff', false⟩, m.index, m.term, csl, sb,
          m.index, m.term, j, x1, m.index
        simp only [named]
        rw [htk2]
        iframe
        isplitr
        · iexact Hlog'
        isplitr
        · iexact HWA2
        ipureintro
        have hidx0 : m.index ≠ W64 0 := by
          intro h
          have h' : uint.Z m.index = 0 := by rw [h]; rfl
          omega
        refine ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj x1 Hm_lookup Hxs hb1,
          by omega, ⟨by simp, ?_, ?_⟩, ?_, by omega, by first | exact Hsb | simp⟩
        · rw [hj1]; omega
        · rw [ite_eq_right (by omega), hj1]
          have hce : ciEff γ m.index = m.index := by unfold ciEff; rw [ite_eq_right hidx0]
          rw [hce]; omega
        · intro m' _ hm'
          have : sint.nat (j + W64 1) - 1 = sint.nat j := by
            show (sint.Z (j + W64 1)).toNat - 1 = (sint.Z j).toNat
            rw [hj1]; omega
          rw [this, Hm_lookup] at hm'
          cases hm'
          exact ⟨rfl, rfl⟩
      · -- a conf change
        have hne0 : decide (m.typ = W32 0) = false := by rw [h1]; decide
        simp only [h1]
        ihave ⟨%Hnn, %d, #Hd, #Hds⟩ := entryAt_fields _ _ $$ He
        (try wp_auto)
        wp_apply (hMU.1 cc_ptr _ d m.data DFrac.discard hcc) $$ [cc] as ⟨⟨%cm, Hcc, %Hdec⟩, -⟩
        · iframe cc Hds
        ihave #Hccw : iprop((□ ∀ Ψ, reqWaitR ρ E (ccIdOf m.data) Ψ -∗ False) ∗
            ⌜ccBootOk ρ.raft.raft.reCfg m.data⌝) $$ []
        · have he : entryWaitOk ρ E m =
              iprop((□ ∀ Ψ, reqWaitR ρ E (ccIdOf m.data) Ψ -∗ False) ∗
                ⌜ccBootOk ρ.raft.raft.reCfg m.data⌝) := by
            unfold entryWaitOk; rw [ite_eq_right (by rw [h1]; decide)]
          rw [he]
          iexact Hewo
        icases Hccw with ⟨#Hccf, %Hcb⟩
        (try wp_auto)
        have hpre : (stLoaded γ st').pending = false ∧ m.index = (stLoaded γ st').p + 1 ∧
            uint.Z (stLoaded γ st').p < uint.Z m.index ∧
            uint.Z (ciEff γ (stLoaded γ st').k) < uint.Z m.index := by
          rw [hlp, hlpp, hlc]; exact ⟨hpend', hip, by omega, hgt⟩
        ihave #Hhook2 := Hhook
        iunfold hookSpec at Hhook2
        ihave #Hh := Hhook2 $$ %(stLoaded γ st') %m.index %m.term %b
        obtain ⟨HEP, HEf⟩ := HE
        icases srvApplyKV_ua s E ρ.wait xj $$ HKV with ⟨%ua, Hua, #Happlier, HKVk⟩
        wp_apply (hACC s cc_ptr ep cm csl true ci ua E ρ.raft
          iprop(applyThread γ (stLoaded γ st') ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b ∗
            ⌜(stLoaded γ st').pending = false ∧ m.index = (stLoaded γ st').p + 1 ∧
              uint.Z (stLoaded γ st').p < uint.Z m.index ∧
              uint.Z (ciEff γ (stLoaded γ st').k) < uint.Z m.index⌝)
          iprop(hookDone γ TM ∗ applyThread γ { stLoaded γ st' with k := m.index, pending := true } ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b)
          iprop(applyThread γ ⟨m.index, m.index, m.index, false⟩ ∗ ciApplying ci m.index m.term ∗
            applyBackend γ ci b)
          iprop(applyThread γ { { stLoaded γ st' with p := m.index } with k := m.index } ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b)
          m.index m.term γB sv.cluster _ (Hcb cm Hdec) HROeq) $$ [Hcc Hcs Hst Happ Hbe HRS Hua]
          as %removed %err ⟨%Hrem, Hua, ⟨%cm', %cs', Hcc, %hIdEq, Hcs⟩, HRS, Hpost⟩
        · rw [ite_eq_left rfl, HEP, HEf]
          iunfold srvRest at HRS
          iframe Hcif Hua Happlier Hrn Hcc Hcs Hcl HRS
          isplitr
          · isplitr
            · first | iexact Hh | (imodintro; iexact Hh) | (imodintro; imodintro; iexact Hh)
            isplitr
            · iintro ⟨Hhd, Hst, Happ, Hbe⟩
              imod (writes_done γ { stLoaded γ st' with k := m.index, pending := true } rfl) $$ Hinv Hst
                with ⟨Hst, Htok⟩
              iunfold hookDone at Hhd
              icases Hhd with ⟨%mm, Hmt, HTM⟩
              imodintro
              iframe Hst Happ Hbe
              iunfold batchLockInv
              iexists mm
              iframe
            · iintro ⟨Hst, Happ, Hbe, -⟩
              imod (skip_done γ (stLoaded γ st') m.index hpre.1 hpre.2.1 hpre.2.2.1) $$ Hinv Hst with Hst
              wp_apply_core (wp_ci_advance hSCI γ ci { stLoaded γ st' with p := m.index } m.index m.term
                hpre.1 (Int.le_refl _) hpre.2.2.2) $$ [Hst] [Happ Hbe]
              · iframe Hcipkg Hci Hinv Hst
              iintro Hst
              iframe
          iframe Hst Happ Hbe
          ipureintro; exact hpre
        ihave HKV := HKVk $$ Hua
        (try rw [ite_eq_left rfl])
        ihave Hpost' : iprop(∃ eff : w64, applyThread γ ⟨m.index, m.index, eff, false⟩ ∗
            ciApplying ci m.index m.term ∗ applyBackend γ ci b) $$ [Hpost]
        · icases Hpost with (⟨Hst, Happ, Hbe⟩ | ⟨Hst, Happ, Hbe⟩)
          · iexists m.index; iframe
          · iexists (stLoaded γ st').eff
            have hrec : ({ { stLoaded γ st' with p := m.index } with k := m.index } : ApplyState) =
                ⟨m.index, m.index, (stLoaded γ st').eff, false⟩ := by
              rw [← hpre.1]
            rw [hrec]
            iframe
        icases Hpost' with ⟨%eff', Hst, Happ, Hbe⟩
        -- (D22, 2026-10-23) the rest buckets: the conf change's effect, `v3` the entry's
        ihave HRS : iprop(srvRest E γr (A ++ ms.take (sint.nat j) ++ [m])) $$ [HRS]
        · rw [srvRest_snoc, restEntry_cc _ _ cm _ (by rw [h1]; decide) Hdec,
            decide_eq_true ((HkB.2 m hmem).1 (by omega))]
          iexact HRS
        cc_kv_applied
        subst Hsb Hrem
        (
        cc_respond
        iexists j + W64 1, ⟨m.index, m.index, eff', false⟩, m.index, m.term, cs', _,
          m.index, m.term, j, xj, m.index
        simp only [named]
        rw [htk2]
        iframe
        isplitr
        · iexact Hlog'
        isplitr
        · iexact HWA2
        ipureintro
        have hidx0 : m.index ≠ W64 0 := by
          intro h
          have h' : uint.Z m.index = 0 := by rw [h]; rfl
          omega
        have hb1 := hconf (by rw [h1]; decide)
        refine ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj xj Hm_lookup Hxs hb1,
          by omega, ⟨by simp, ?_, ?_⟩, ?_, by omega, by first | exact Hsb | simp⟩
        · rw [hj1]; omega
        · rw [ite_eq_right (by omega), hj1]
          have hce : ciEff γ m.index = m.index := by unfold ciEff; rw [ite_eq_right hidx0]
          rw [hce]; omega
        · intro m' _ hm'
          have : sint.nat (j + W64 1) - 1 = sint.nat j := by
            show (sint.Z (j + W64 1)).toNat - 1 = (sint.Z j).toNat
            rw [hj1]; omega
          rw [this, Hm_lookup] at hm'
          cases hm'
          exact ⟨rfl, rfl⟩)
    · -- at or below `ci`: `ApplyV2storeOnly`
      have hle : uint.Z m.index ≤ uint.Z (ciEff γ st'.k) := by
        first | omega | exact Int.not_lt.mp Hif | word
      obtain ⟨hpend', hp', hc'⟩ := Hstj
      have hjnat : (sint.nat j : Int) = sint.Z j := by
        unfold sint.nat; exact Int.toNat_of_nonneg Hj.1
      have hidxZ : uint.Z m.index = uint.Z f0 + sint.Z j := by rw [hmidx, hjnat]
      have hj1 : sint.Z (j + W64 1) = sint.Z j + 1 := by word
      have hc0 : uint.Z f0 + sint.Z j ≤ uint.Z (ciEff γ st.k) ∧
          uint.Z (ciEff γ st'.k) = uint.Z (ciEff γ st.k) := by
        by_cases hj0 : sint.Z j = 0
        · rw [ite_eq_left hj0] at hc'; omega
        · rw [ite_eq_right hj0] at hc'; omega
      have hpend'' : (stLoaded γ st').pending = false := by rw [hlp]; exact hpend'
      have hidx0 : m.index ≠ W64 0 := by
        intro h
        have h' : uint.Z m.index = 0 := by rw [h]; rfl
        omega
      have hlast' : ∀ (m' : EntryModel), 0 < sint.nat (j + W64 1) →
          ms[sint.nat (j + W64 1) - 1]? = some m' → m'.index = m.index ∧ m'.term = m.term := by
        intro m' _ hm'
        have : sint.nat (j + W64 1) - 1 = sint.nat j := by
          show (sint.Z (j + W64 1)).toNat - 1 = (sint.Z j).toNat
          rw [hj1]; omega
        rw [this, Hm_lookup] at hm'
        cases hm'
        exact ⟨rfl, rfl⟩
      have hstj' : uint.Z (stLoaded γ st').p = max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z (j + W64 1)) ∧
          uint.Z (ciEff γ (stLoaded γ st').k) = (if sint.Z (j + W64 1) = 0 then uint.Z (ciEff γ st.k)
            else max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z (j + W64 1))) := by
        rw [hlpp, hlc, ite_eq_right (by omega), hj1]; omega
      (try wp_auto)
      wp_apply hGTy $$ [He] as -
      · iframe He
      (try wp_auto)
      rcases hmtyp with h0 | ⟨h1, hcc⟩
      · -- a normal entry
        (try simp only [h0, _root_.decide_true])
        (try wp_auto)
        -- (linkv-txn stage B1) the entry's registration, for the member's own ids
        ihave ⟨%ot, #Hreg⟩ := entryRegd_of_wait ρ E m h0 $$ [Hewo]
        · iframe Hewo; iapply isServer_waitIs $$ Hsrv0
        wp_apply (hAEN s γ ci TM E ρ b e m (stLoaded γ st') false xj γr ot aw
            (A ++ ms.take (sint.nat j))) $$ [Hst Hbe Hlr Hgr Hfs HKV Hwt Hao Hka HRS]
          as ⟨Hbe, Hlr, Hgr, Hfs, ⟨%x1, %out1, HKV, %Hstep1, -, Hpre, Hka, HRS⟩, Hst⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Hsrv0 Hewo He Hst Hbe Hlr Hgr Hfs HKV Hwt Hao Hlog Hcm Hka HRS HlbJ
          isplitr
          · iexact Hreg
          isplitr
          · ipureintro
            exact ⟨hawA, (decide_eq_false (fun h =>
              (show ¬ uint.Z (ciEff γ st.k) < uint.Z m.index by omega) ((HkB.2 m hmem).2 h))).symm⟩
          isplitr
          · ipureintro; omega
          ipureintro; exact ⟨⟨hpend'', hOk1 h0, h0⟩, trivial⟩
        have hb1 : batchStep (ciEff γ st.k) m xj x1 := by
          unfold batchStep; rw [ite_eq_left h0]
          refine ⟨out1, ?_⟩
          rw [decide_eq_false (show ¬ uint.Z (ciEff γ st.k) < uint.Z m.index by omega)]
          exact Hstep1
        (try simp only [Bool.false_eq_true, ↓reduceIte])
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        icases srvApplyKV_idxCert s E ρ.wait x1 $$ HKV with ⟨HKV, #Hcert⟩
        wp_apply (hSet1 s E γr aw m.index x1.log) $$ [Hpre] as ⟨Hao, -, #Hlog'⟩
        · iframe #; iframe Hpre
        (try wp_auto)
        wp_apply hGT $$ [He] as -
        · iframe He
        wp_apply hSet2 $$ [$Hat]
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hGT $$ [He] as -
        · iframe He
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, stLoaded γ st', a', t', csl, sb, m.index, m.term, j, x1, m.index
        simp only [named]
        rw [htk2]
        iframe
        isplitr
        · iexact Hlog'
        isplitr
        · iexact HWA2
        ipureintro
        exact ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj x1 Hm_lookup Hxs hb1,
          by omega, ⟨hpend'', hstj'.1, hstj'.2⟩, hlast', by omega, by first | exact Hsb | simp⟩
      · -- a conf change
        (try simp only [h1])
        ihave ⟨%Hnn, %d, #Hd, #Hds⟩ := entryAt_fields _ _ $$ He
        (try wp_auto)
        wp_apply (hMU.1 cc_ptr _ d m.data DFrac.discard hcc) $$ [cc] as ⟨⟨%cm, Hcc, %Hdec⟩, -⟩
        · iframe cc Hds
        ihave #Hccw : iprop((□ ∀ Ψ, reqWaitR ρ E (ccIdOf m.data) Ψ -∗ False) ∗
            ⌜ccBootOk ρ.raft.raft.reCfg m.data⌝) $$ []
        · have he : entryWaitOk ρ E m =
              iprop((□ ∀ Ψ, reqWaitR ρ E (ccIdOf m.data) Ψ -∗ False) ∗
                ⌜ccBootOk ρ.raft.raft.reCfg m.data⌝) := by
            unfold entryWaitOk; rw [ite_eq_right (by rw [h1]; decide)]
          rw [he]
          iexact Hewo
        icases Hccw with ⟨#Hccf, %Hcb⟩
        (try wp_auto)
        icases srvApplyKV_ua s E ρ.wait xj $$ HKV with ⟨%ua, Hua, #Happlier, HKVk⟩
        wp_apply (hACC s cc_ptr ep cm csl false ci ua E ρ.raft
          iprop(True) iprop(True) iprop(True) iprop(True) m.index m.term γB sv.cluster _ (Hcb cm Hdec)
          HROeq) $$ [Hcc Hcs HRS Hua]
          as %removed %err ⟨%Hrem, Hua, ⟨%cm', %cs', Hcc, %hIdEq, Hcs⟩, HRS, -⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          iunfold srvRest at HRS
          iframe Hcif Hua Happlier Hrn Hcc Hcs Hcl HRS
          isplit <;> ipureintro <;> trivial
        ihave HKV := HKVk $$ Hua
        ihave HRS : iprop(srvRest E γr (A ++ ms.take (sint.nat j) ++ [m])) $$ [HRS]
        · rw [srvRest_snoc, restEntry_cc _ _ cm _ (by rw [h1]; decide) Hdec,
            decide_eq_false (fun h =>
              (show ¬ uint.Z (ciEff γ st.k) < uint.Z m.index by omega) ((HkB.2 m hmem).2 h))]
          iexact HRS
        cc_kv_applied
        subst Hsb Hrem
        (
        cc_respond
        iexists j + W64 1, stLoaded γ st', a', t', cs', _, m.index, m.term, j, xj, m.index
        simp only [named]
        rw [htk2]
        iframe
        isplitr
        · iexact Hlog'
        isplitr
        · iexact HWA2
        ipureintro
        have hb1 := hconf (by rw [h1]; decide)
        exact ⟨by rw [hjs]; exact entriesStep_take_succ _ ms _ m x xj xj Hm_lookup Hxs hb1,
          by omega, ⟨hpend'', hstj'.1, hstj'.2⟩, hlast', by omega, by first | exact Hsb | simp⟩)
  · -- the loop is done
    have hjn : sint.nat j = ms.length := by rw [Hlen]; word
    have hjZ : sint.Z j = (ms.length : Int) := by
      rw [← hjn]; unfold sint.nat; rw [Int.toNat_of_nonneg Hj.1]
    have hnpos : 0 < ms.length := List.length_pos_iff.mpr hne
    obtain ⟨mlast, hml⟩ : ∃ m, ms[ms.length - 1]? = some m :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hgl : ms.getLast? = some mlast := by
      rw [List.getLast?_eq_getElem?]; exact hml
    obtain ⟨hmi, hmt⟩ := Hlast mlast (by omega) (by rw [hjn]; exact hml)
    have hidx := (Hms (ms.length - 1) mlast hml).1
    have haw : aw = ai := by
      have h1 : uint.Z mlast.index = uint.Z f0 + ((ms.length - 1 : Nat) : Int) := hidx
      rw [hmi] at h1
      apply BitVec.eq_of_toNat_eq
      have h2 : uint.Z aw = uint.Z ai := by rw [Haw, h1, hjZ]; omega
      simp only [uint.Z] at h2
      exact_mod_cast h2
    subst haw
    ihave #Hlogf := Hlog
    iapply Hphi
    iframe Hfs
    iexists st', a', t', csl
    rw [hjn, List.take_of_length_le (Nat.le_refl _)] at Hxs
    iframe Hst Hbe Happ Hcs Hlr Hgr Hao HWA
    have htk' : ms.take (sint.nat j) = ms := by rw [hjn, List.take_of_length_le (Nat.le_refl _)]
    isplitl [HKV Hka HRS]
    · iexists xj; iframe HKV Hlogf
      isplitr
      · ipureintro; exact Hxs
      rw [htk']
      iframe Hka HRS
    ipureintro
    have hne0 : sint.Z j ≠ 0 := by omega
    rw [ite_eq_right hne0] at Hstj
    obtain ⟨hpend', hp', hc'⟩ := Hstj
    refine ⟨by rw [hgl]; simp [hmi], by rw [hgl]; simp [hmt], ⟨hpend', ?_⟩, ?_, Hsb⟩
    · rw [hp', hc', ← hmi, hidx, hjZ]; omega
    · rw [hc', ← hmi, hidx, hjZ]; omega

end proof

end EtcdGrove
end Perennial
