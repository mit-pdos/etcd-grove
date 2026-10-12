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
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetIndex
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetTerm
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.Entry__GetType
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyEntryNormal
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setAppliedIndex
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__setTerm
public import Spec.go_etcd_io.etcd.pkg.v3.pbutil.MustUnmarshalMessage
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyConfChange
public import EtcdDeps.Spec.go_etcd_io.raft.v3.raftpb.ConfChange__GetId
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.membership.RaftCluster__Members

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
  intro s γ ci TM b es ents ms f0 ep cs rac st a at0 hne hfrom hok
  wp_start as ⟨#Hsrv, #Hes, #Hents, Hst, Hbe, Happ, Hcs, Hlr⟩
  ihave #Hsrv0 := Hsrv
  iunfold isServer at Hsrv
  icases Hsrv with ⟨#Hsci, ⟨%sv, #Hfl⟩, #Hat⟩
  ihave #Hsci' := Hsci
  iunfold isServerCI at Hsci'
  icases Hsci' with ⟨#Hcif, #Hci, #Hinv⟩
  iunfold srvFieldsAt at Hfl
  icases Hfl with ⟨#Hlg, %Hlgnn, #Hw, #Hwok, #Hua, #Happlier, #Hhook, #Hls, #Hlok, #Hfc, #Hals,
    #Hcl, #Hq, #Hlgmu, #Hmid, #Hlead, #Het, #Htm, #Hnot, #Halm⟩
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
        (ai at' ivv : w64),
      "cnt" ∷ i_ptr ↦ j ∗ "iv" ∷ ivp ↦ ivv ∗ "shouldStop" ∷ shouldStop_ptr ↦ sb ∗
      "appliedi" ∷ appliedi_ptr ↦ ai ∗ "appliedt" ∷ appliedt_ptr ↦ at' ∗
      "Hst" ∷ applyThread γ st' ∗ "Hbe" ∷ applyBackend γ ci b ∗ "Happ" ∷ ciApplying ci a' t' ∗
      "Hcs" ∷ epConfStateAddr ep ↦ csl ∗ "Hlr" ∷ srvLgReader s ∗
      "Hphi" ∷ (∀ (appliedt appliedi : w64) (shouldStop : Bool),
        (∃ (st' : ApplyState) (a' at' : w64) (csl : Loc),
          applyThread γ st' ∗ applyBackend γ ci b ∗ ciApplying ci a' at' ∗
          epConfStateAddr ep ↦ csl ∗ srvLgReader s ∗
          ⌜(ms.getLast?).map EntryModel.index = some appliedi ∧
            (ms.getLast?).map EntryModel.term = some appliedt ∧
            loopOk γ st' appliedi ∧
            uint.Z (ciEff γ st'.k) = max (uint.Z (ciEff γ st.k)) (uint.Z appliedi)⌝) -∗
        Φ (PairV (PairV #appliedt #appliedi) #shouldStop)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z es.len⌝ ∗
      "%Hstj" ∷ ⌜st'.pending = false ∧
        uint.Z st'.p = max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z j) ∧
        uint.Z (ciEff γ st'.k) = (if sint.Z j = 0 then uint.Z (ciEff γ st.k)
          else max (uint.Z (ciEff γ st.k)) (uint.Z f0 - 1 + sint.Z j))⌝ ∗
      "%Hlast" ∷ ⌜∀ m : EntryModel, 0 < sint.nat j → ms[sint.nat j - 1]? = some m →
        m.index = ai ∧ m.term = at'⌝ : IProp GF)
    $$ [cnt iv shouldStop appliedi appliedt Hst Hbe Happ Hcs Hlr HΦ]
  · iexists (W64 0), st, a, at0, cs, false, (W64 0), (W64 0), (W64 0)
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, ⟨Hpend, ?_, ?_⟩, fun m h => absurd h (by simp)⟩
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
      [cnt iv shouldStop appliedi appliedt Happ Hcs Hlr Hphi e]
    · iframe Hcipkg Hci Hinv Hst Hbe
    iintro ⟨Hst, Hbe⟩
    obtain ⟨hlp, hlpp, hlpe, hlc⟩ := stLoaded_facts γ st'
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
        simp only [h0, decide_true]
        (try wp_auto)
        wp_apply (hAEN s γ ci TM b e m (stLoaded γ st') true) $$ [Hst Hbe Happ Hlr]
          as ⟨Hbe, Hlr, Hpost⟩
        · rw [ite_eq_left rfl]
          iframe Hsrv0 He Hst Hbe Happ Hlr
          ipureintro
          refine ⟨hlp ▸ hpend', ?_⟩
          rw [hlpp, hlc]
          refine ⟨hip, by omega, hgt⟩
        (try rw [ite_eq_left rfl])
        icases Hpost with ⟨Happ, %eff', Hst⟩
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hSet1 $$ [$Hat]
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
          m.index, m.term, j
        simp only [named]
        iframe
        ipureintro
        have hidx0 : m.index ≠ W64 0 := by
          intro h
          have h' : uint.Z m.index = 0 := by rw [h]; rfl
          omega
        refine ⟨by omega, ⟨by simp, ?_, ?_⟩, ?_⟩
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
        ihave #He2 := He
        iunfold entryAt at He2
        icases He2 with ⟨%Hnn, %pt, %pi, %pty, %d, #Ht, #Hpt, #Hi, #Hpi, #Hty, #Hpty, #Hd, #Hds⟩
        (try wp_auto)
        wp_apply (hMU.1 cc_ptr _ d m.data DFrac.discard hcc) $$ [cc] as ⟨⟨%v', %cid, Hcc, #Hcid⟩, -⟩
        · iframe cc Hds
        (try wp_auto)
        have hpre : (stLoaded γ st').pending = false ∧ m.index = (stLoaded γ st').p + 1 ∧
            uint.Z (stLoaded γ st').p < uint.Z m.index ∧
            uint.Z (ciEff γ (stLoaded γ st').k) < uint.Z m.index := by
          rw [hlp, hlpp, hlc]; exact ⟨hpend', hip, by omega, hgt⟩
        ihave #Hhook2 := Hhook
        iunfold hookSpec at Hhook2
        ihave #Hh := Hhook2 $$ %(stLoaded γ st') %m.index %m.term %b
        wp_apply (hACC s cc_ptr ep v' csl true ci sv.ua (batchLockInv γ TM)
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
          sv.hook m.index m.term) $$ [Hcc Hcs Hst Happ Hbe] as %removed %err ⟨⟨%v'', %cs', Hcc, %hIdEq, Hcs⟩, Hpost⟩
        · rw [ite_eq_left rfl]
          iframe Hcif Hua Happlier Hcc Hcs
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
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hSet1 $$ [$Hat]
        (try wp_auto)
        wp_apply hGT $$ [He] as -
        · iframe He
        wp_apply hSet2 $$ [$Hat]
        (try wp_auto)
        rcases sb with _ | _ <;> (
        (try wp_auto)
        wp_apply (hId cc_ptr v'' (DFrac.own 1) cid) $$ [Hcc] as Hcc
        · rw [hIdEq]; iframe Hcc Hcid
        (try wp_auto)
        wp_apply hMem as %msl -
        (try wp_auto)
        wp_alloc rsp as Hrsp
        (try wp_auto)
        ihave #Hwok2 := Hwok
        iunfold waitOk at Hwok2
        icases Hwok2 with ⟨%wi, %hw, #Htrig, -⟩
        simp only [hw]
        (try wp_auto)
        wp_apply Htrig
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hGT $$ [He] as -
        · iframe He
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, ⟨m.index, m.index, eff', false⟩, m.index, m.term, cs', _,
          m.index, m.term, j
        simp only [named]
        iframe
        ipureintro
        have hidx0 : m.index ≠ W64 0 := by
          intro h
          have h' : uint.Z m.index = 0 := by rw [h]; rfl
          omega
        refine ⟨by omega, ⟨by simp, ?_, ?_⟩, ?_⟩
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
        (try simp only [h0, decide_true])
        (try wp_auto)
        wp_apply (hAEN s γ ci TM b e m (stLoaded γ st') false) $$ [Hst Hbe Hlr]
          as ⟨Hbe, Hlr, Hst⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Hsrv0 He Hst Hbe Hlr
          ipureintro; exact ⟨hpend'', trivial⟩
        (try simp only [Bool.false_eq_true, ↓reduceIte])
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hSet1 $$ [$Hat]
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
        iexists j + W64 1, stLoaded γ st', a', t', csl, sb, m.index, m.term, j
        simp only [named]
        iframe
        ipureintro
        exact ⟨by omega, ⟨hpend'', hstj'.1, hstj'.2⟩, hlast'⟩
      · -- a conf change
        (try simp only [h1])
        ihave #He2 := He
        iunfold entryAt at He2
        icases He2 with ⟨%Hnn, %pt, %pi, %pty, %d, #Ht, #Hpt, #Hi, #Hpi, #Hty, #Hpty, #Hd, #Hds⟩
        (try wp_auto)
        wp_apply (hMU.1 cc_ptr _ d m.data DFrac.discard hcc) $$ [cc] as ⟨⟨%v', %cid, Hcc, #Hcid⟩, -⟩
        · iframe cc Hds
        (try wp_auto)
        wp_apply (hACC s cc_ptr ep v' csl false ci sv.ua (batchLockInv γ TM)
          iprop(True) iprop(True) iprop(True) iprop(True) sv.hook m.index m.term) $$ [Hcc Hcs]
          as %removed %err ⟨⟨%v'', %cs', Hcc, %hIdEq, Hcs⟩, -⟩
        · simp only [Bool.false_eq_true, ↓reduceIte]
          iframe Hcif Hua Happlier Hcc Hcs
          isplit <;> ipureintro <;> trivial
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hSet1 $$ [$Hat]
        (try wp_auto)
        wp_apply hGT $$ [He] as -
        · iframe He
        wp_apply hSet2 $$ [$Hat]
        (try wp_auto)
        rcases sb with _ | _ <;> (
        (try wp_auto)
        wp_apply (hId cc_ptr v'' (DFrac.own 1) cid) $$ [Hcc] as Hcc
        · rw [hIdEq]; iframe Hcc Hcid
        (try wp_auto)
        wp_apply hMem as %msl -
        (try wp_auto)
        wp_alloc rsp as Hrsp
        (try wp_auto)
        ihave #Hwok2 := Hwok
        iunfold waitOk at Hwok2
        icases Hwok2 with ⟨%wi, %hw, #Htrig, -⟩
        simp only [hw]
        (try wp_auto)
        wp_apply Htrig
        (try wp_auto)
        wp_apply hGI $$ [He] as -
        · iframe He
        wp_apply hGT $$ [He] as -
        · iframe He
        (try wp_auto)
        wp_for_post
        iframe
        iexists j + W64 1, stLoaded γ st', a', t', cs', _, m.index, m.term, j
        simp only [named]
        iframe
        ipureintro
        exact ⟨by omega, ⟨hpend'', hstj'.1, hstj'.2⟩, hlast'⟩)
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
    iapply Hphi
    iexists st', a', t', csl
    iframe
    ipureintro
    have hne0 : sint.Z j ≠ 0 := by omega
    rw [ite_eq_right hne0] at Hstj
    obtain ⟨hpend', hp', hc'⟩ := Hstj
    refine ⟨by rw [hgl]; simp [hmi], by rw [hgl]; simp [hmt], ⟨hpend', ?_⟩, ?_⟩
    · rw [hp', hc', ← hmi, hidx, hjZ]; omega
    · rw [hc', ← hmi, hidx, hjZ]; omega

end proof

end EtcdGrove
end Perennial
