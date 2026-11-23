/-
`(*Replica).handleCommit` against the model's `hCommit`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.EpBase
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.NewInstance
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Record
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Log
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.UpdateConflicts
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.UpdateCommitted

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- What `handleCommit` needs of the message and the state (from the invariant, see
`notes/prove-epaxos.md`). -/
structure CommitWf (i : Nat) (σ : RState) (m : Commit) : Prop where
  id : σ.id = i
  q0 : 0 ≤ zz m.replica
  q1 : zz m.replica < nR
  n0 : 0 ≤ zz m.inst
  n1 : toN m.inst + 1 < MAX_INSTANCE
  cmds : m.command ≠ []
  lb : toN m.replica = i → ((getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2.lb).isSome

set_option maxHeartbeats 4000000 in
set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 1000 in
theorem wp_handleCommit (hP : dlog.Logger.Printf.spec (GF := GF)) (hS : CmdStringSpec (GF := GF)) (γ : EpNames) (i : Nat) (r : Loc) (σ : RState) (c : Loc) (m : Commit)
    (rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (hw : CommitWf i σ m) :
    {{ pkgInit_epaxos (GF := GF) ∗ efld r go!"Replica" ↦□ rr ∗ isReplicaFw γ rr i L p Rext ∗
        ownRep γ i r σ ∗ ownCommit c m (DFrac.own 1) ∗
        [∗list] o ∈ (hCommit σ m).2, outOk γ i o }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handleCommit")) (Val #c))
    {{ RET #(); ownRep γ i r (hCommit σ m).1 }} := by
  wp_start as ⟨#Hrr, #Hfw, Hrep, Hc, Houts⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HlS, HlP, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  unfold ownCommit
  icases Hc with ⟨%cs, %ds, Hc, Hcs, Hds⟩
  have hq : toN m.replica < nR := by
    have := hw.q1; have := hw.q0; simp only [toN, zz] at *; omega
  have hn : toN m.inst < MAX_INSTANCE := by have := hw.n1; omega
  icases repInsts_acc γ i r σ.inst ⟨toN m.replica, toN m.inst⟩ hq hn $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  wp_auto
  have e1 : sint.Z (W64 (sint.Z m.replica)) = sint.Z m.replica := by word
  have e2 : sint.Z (W64 (sint.Z m.inst)) = sint.Z m.inst := by word
  have hq' : (sint.Z m.replica).toNat = toN m.replica := rfl
  have hn' : (sint.Z m.inst).toNat = toN m.inst := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧ sint.Z (W64 (sint.Z m.replica)) < sint.Z iss.len := by
    have := hw.q0; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hq']; exact Hrow
  have h2 : 0 ≤ sint.Z (W64 (sint.Z m.inst)) ∧ sint.Z (W64 (sint.Z m.inst)) < sint.Z row.len := by
    have := hw.n0; have := hw.n1; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hn']; exact Hptr.1
  have hplen' : (sint.Z row.len) = ((ptrs.length : Nat) : Int) := by
    have := Hplen.1; have := Hplen.2; word
  -- crtInstance
  unfold repRowArr
  icases Hcrt with ⟨%crt, #Hcrtf, Hcrtsl⟩
  ihave %Hclen := ownSlice_len _ _ _ $$ Hcrtsl
  wp_auto
  have hclen : ((List.range nR).map σ.crtInstance).length = nR := by simp
  have h3 : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧ sint.Z (W64 (sint.Z m.replica)) < sint.Z crt.len := by
    have := hw.q0; have := hw.q1; simp only [toN, zz] at *; constructor <;> word
  simp only [h3, _root_.and_self, ↓reduceIte]
  have hcv : ((List.range nR).map σ.crtInstance)[(sint.Z (W64 (sint.Z m.replica))).toNat]? =
      some (σ.crtInstance (toN m.replica)) := by
    rw [e1, hq']; simp [hq]
  wp_apply wp_load_slice_index crt _ _ _ _ h3.1 $$ [$Hcrtsl] as Hcrtsl
  · ipureintro; exact hcv
  ipersist r
  ipersist commit
  wp_join iprop(crt ↦* ((List.range nR).map (bumpCrt σ (toN m.replica) m.inst).crtInstance) ∗
      c ↦ epaxos.Commit.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [Hcrtsl Hc] as ⟨Hcrtsl, Hc⟩
  · have h3' : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧
        sint.Z (W64 (sint.Z m.replica)) < ((List.range nR).map σ.crtInstance).length := by
      rw [hclen]; have := hw.q0; have := hw.q1; simp only [toN, zz] at *; constructor <;> word
    try simp only [h3, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hcrtsl] as Hcrtsl
    · ipureintro; exact h3'
    wp_join_done
    rw [bumpCrt_crt_true σ _ _ Hif, map_range_upd _ _ _ _ hq, e1, hq']
    iframe Hc; iexact Hcrtsl
  · rw [bumpCrt_crt_false σ _ _ Hif]; iframe Hc; iexact Hcrtsl
  -- maxRecvBallot
  wp_join iprop(efld r go!"maxRecvBallot" ↦
      (bumpRecvBallot (bumpCrt σ (toN m.replica) m.inst) m.ballot).maxRecvBallot ∗
      c ↦ epaxos.Commit.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [Hmrb Hc] as ⟨Hmrb, Hc⟩
  · rw [bumpRecvBallot_true _ _ (by simpa using Hif)]
    iframe Hc; iexact Hmrb
  · rw [bumpRecvBallot_false _ _ (by simpa using Hif)]
    simp only [bumpCrt_maxRecvBallot]
    iframe Hc; iexact Hmrb
  -- the instance, created if nil
  have hxq : W32 (toN m.replica : Int) = m.replica := by
    have := hw.q0; simp only [toN, zz] at *; word
  have hxi : W32 (toN m.inst : Int) = m.inst := by
    have := hw.n0; simp only [toN, zz] at *; word
  wp_join iprop(∃ p', inst_ptr ↦ p' ∗ row ↦* ptrs.set (toN m.inst) p' ∗
      ownInst γ i ⟨toN m.replica, toN m.inst⟩ p'
        (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2 ∗
      c ↦ epaxos.Commit.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds)
    with [inst Hptrs Hx Hc]
  · -- nil: `newInstanceDefault`
    rcases hx : σ.inst ⟨toN m.replica, toN m.inst⟩ with _ | w0
    case some =>
      unfold instAt ownInst
      icases Hx with ⟨%y, Hy, -⟩
      ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hy
      exact (Hnn rfl).elim
    wp_apply wp_newInstanceDefault as %p' ⟨%Hp'nn, %t, %idp, Hp', Hid⟩
    ipersist Hid
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hq']; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_store_slice_index $$ [$Hptrs] as Hptrs
    · ipureintro; rw [← hplen'] ; exact h2
    simp only [h1, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
    · ipureintro; rw [e1, hq']; exact Hrow
    simp only [h2, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index row _ _ _ p' h2.1 $$ [$Hptrs] as Hptrs
    · ipureintro; rw [e2, hn']
      simp [List.getElem?_set, show toN m.inst < ptrs.length by have := Hptr.2; omega]
    rw [e2, hn']
    wp_join_done
    iexists p'
    iframe inst Hptrs Hc
    have hd : (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2 =
        newInstanceDefault ⟨toN m.replica, toN m.inst⟩ := by simp [getOrDefault, hx]
    rw [hd]
    iapply ownInst_default
    iframe Hp'
    rw [hxq, hxi]; iexact Hid
  · -- not nil: the instance exists
    rcases hx : σ.inst ⟨toN m.replica, toN m.inst⟩ with _ | w0
    · unfold instAt; icases Hx with %Hnull
      exact (Hif Hnull).elim
    unfold instAt
    iexists ptr
    have hset : ptrs.set (toN m.inst) ptr = ptrs := by
      have := List.getElem?_eq_some_iff.mp Hptr.1
      rw [← this.2]; exact List.set_getElem_self this.1
    rw [hset]
    have hd : (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2 = w0 := by simp [getOrDefault, hx]
    rw [hd]
    iframe
  iintro ⟨%p', inst, Hptrs, Hx, Hc⟩
  have hw0 : (getOrDefault σ ⟨toN m.replica, toN m.inst⟩).2 = commitW0 σ m := rfl
  rw [hw0]
  unfold ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  have hib' : instBounds (upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (commitW0 σ m))) :=
    instBounds_upd _ _ _ Hib hq hw.n1
  wp_auto
  wp_if_destruct
  · -- already committed
    rw [hCommit_early σ m (Or.inl ((stGe_iff _ _).mpr (by rw [← Hyf.2.2.1]; exact Hif)))]
    iapply HΦ
    simp only [commitPre]
    rw [← bumpRecvBallot_bumpCrt_mrb σ (toN m.replica) m.inst m.ballot]
    ihave Hins := Hclose $$ %p' %(some (commitW0 σ m)) Hptrs [Hy Hycmds Hydeps Hylb]
    · unfold instAt ownInst; iexists y; iframe Hy Hycmds Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      · iexact Hyid
    iframe Hins Hcut Heut Hconf Hmsk HmaxSeq Hlead Hstore Hpeer Hmrb
    isplitr
    · ipureintro; exact hib'
    isplitr
    · ipureintro; exact Hcb
    isplitl [Hcrtsl]
    · iexists crt; iframe Hcrtf Hcrtsl
    isplitl [HlS]
    · iexact HlS
    iexact HlP
  have hst : stGe (commitW0 σ m).status stCOMMITTED = false := by
    rcases h : stGe (commitW0 σ m).status stCOMMITTED
    · rfl
    · exact absurd ((stGe_iff _ _).mp h) (by rw [← Hyf.2.2.1]; exact Hif)
  wp_if_destruct
  · -- a lower ballot
    rw [hCommit_early σ m (Or.inr ((slt_iff _ _).mpr (by rw [← Hyf.1]; exact Hif)))]
    iapply HΦ
    simp only [commitPre]
    rw [← bumpRecvBallot_bumpCrt_mrb σ (toN m.replica) m.inst m.ballot]
    ihave Hins := Hclose $$ %p' %(some (commitW0 σ m)) Hptrs [Hy Hycmds Hydeps Hylb]
    · unfold instAt ownInst; iexists y; iframe Hy Hycmds Hydeps Hylb
      isplitr
      · ipureintro; exact Hyf
      · iexact Hyid
    iframe Hins Hcut Heut Hconf Hmsk HmaxSeq Hlead Hstore Hpeer Hmrb
    isplitr
    · ipureintro; exact hib'
    isplitr
    · ipureintro; exact Hcb
    isplitl [Hcrtsl]
    · iexists crt; iframe Hcrtf Hcrtsl
    isplitl [HlS]
    · iexact HlS
    iexact HlP
  have hbal : m.ballot.slt (commitW0 σ m).bal = false := by
    rcases h : m.ballot.slt (commitW0 σ m).bal
    · rfl
    · exact absurd ((slt_iff _ _).mp h) (by rw [← Hyf.1]; exact Hif)
  rw [hCommit_main σ m hst hbal]
  ihave #Hro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hro
  have hnex : (commitW0 σ m).status ≠ stEXECUTED := by
    intro h; rw [h] at hst; revert hst; decide
  have hnex' : decide ((commitW0 σ m).status = stEXECUTED) = false := by simp [hnex]
  rw [hnex']
  wp_auto
  wp_join iprop(inst_ptr ↦ p' ∗ p' ↦ y ∗
      c ↦ epaxos.Commit.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds ∗
      ownCmds cs m.command (DFrac.own 1) ∗
      match (commitRp σ m (commitW0 σ m)).1.lb with
      | none => iprop(⌜y.lb' = null⌝)
      | some lb => iprop(⌜y.lb' ≠ null⌝ ∗ ownLb γ i false y.lb' lb))
    with [Hc Hcs Hylb Houts inst Hy] as ⟨inst, Hy, Hc, Hcs, Hylb⟩
  · -- the instance's own leader
    have hi5 : (i : Int) < 5 := by
      have := HLn.2; have := HLn.1; simp only [nRep] at *; omega
    have hid : toN m.replica = σ.id := by
      rw [hw.id, Hif]; simp only [toN]
      have : sint.Z (W32 (i : Int)) = (i : Int) := by word
      rw [this]; simp
    have hskip : ∀ (hs : commitRp σ m (commitW0 σ m) = (commitW0 σ m, [])),
        (c ↦ epaxos.Commit.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds ∗
          ownCmds (GF := GF) cs m.command (DFrac.own 1) ∗
          match (commitW0 σ m).lb with
          | none => iprop(⌜y.lb' = null⌝)
          | some lb => iprop(⌜y.lb' ≠ null⌝ ∗ ownLb γ i false y.lb' lb)) ⊢
        (c ↦ epaxos.Commit.mk m.leaderId m.replica m.inst m.ballot cs m.seq ds ∗
          ownCmds cs m.command (DFrac.own 1) ∗
          match (commitRp σ m (commitW0 σ m)).1.lb with
          | none => iprop(⌜y.lb' = null⌝)
          | some lb => iprop(⌜y.lb' ≠ null⌝ ∗ ownLb γ i false y.lb' lb)) := by
      intro hs; rw [hs]
    icases ownCmds_open _ _ _ $$ Hcs with ⟨%vs, Hcs, %Hvslen, Hcms⟩
    ihave %Hcslen := ownSlice_len _ _ _ $$ Hcs
    wp_if_destruct
    · -- one command
      have hlen1 : m.command.length = 1 := by
        rw [← Hvslen]; have := Hcslen.1; rw [Hif] at this; rw [this]; rfl
      obtain ⟨wc, hwc⟩ : ∃ wc, m.command = [wc] := by
        match h : m.command, hlen1 with
        | [a], _ => exact ⟨a, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v, vs = [v] := by
        match h : vs, (show vs.length = 1 by rw [Hvslen, hlen1]) with
        | [a], _ => exact ⟨a, rfl⟩
      subst hv
      icases ownSlice_elem_acc 0 v cs _ _ (by omega) rfl $$ Hcs with ⟨Hv, Hcsc⟩
      have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z cs.len := by
        rw [Hif]; decide
      have hb0' : (0 : Int) ≤ 0 ∧ 0 < sint.Z cs.len := by rw [Hif]; decide
      simp only [show sint.Z (W64 0) = 0 from rfl, hb0', _root_.and_self, ↓reduceIte]
      wp_auto
      icases Hcms with ⟨⟨%wc', %Hwc', #Hok⟩, -⟩
      have hwc' : wc' = wc := by rw [hwc] at Hwc'; simpa using Hwc'.symm
      subst hwc'
      unfold cmdOk at *
      icases Hok with ⟨%Hokp, #Hokv⟩
      ihave Hcs := Hcsc $$ %v Hv
      simp only [List.set_cons_zero, show Int.toNat 0 = 0 from rfl] at *
      ihave Hcs : ownCmds cs m.command (DFrac.own 1) $$ [Hcs]
      · iapply ownCmds_close _ _ _ [v]
        iframe Hcs
        isplitr
        · ipureintro; rw [hwc]; rfl
        rw [hwc]
        isplitl []
        · iexists wc'
          isplitr
          · ipureintro; rfl
          unfold cmdOk; iframe Hokv; ipureintro; exact Hokp
        · iempintro
      wp_if_destruct
      · -- a no-op
        have hnoop : Option.map (fun x => x.op) m.command.head? = some opNONE := by
          rw [hwc]; simp only [List.head?_cons, Option.map_some, Option.some.injEq]
          rw [← Hokp.1]; exact Hif
        have hcond : toN m.replica = σ.id ∧ m.command.length = 1 ∧
            Option.map (fun x => x.op) m.command.head? = some opNONE := ⟨hid, hlen1, hnoop⟩
        rcases hlb : (commitW0 σ m).lb with _ | lb
        · exfalso
          have := hw.lb (by rw [hid, hw.id])
          unfold commitW0 at hlb; rw [hlb] at this; simp at this
        icases Hylb with ⟨%Hlbnn, Hlb⟩
        unfold ownLb
        icases Hlb with ⟨%yl, %gs, %prs, Hyl, %Hylf, Hcp, Hlbrest⟩
        rcases hcp : lb.clientProposals with _ | ps
        · -- no proposals held
          icases Hcp with %Hcpnil
          wp_auto
          simp only [Hcpnil, _root_.decide_true, Bool.not_true]
          wp_auto
          have hs : commitRp σ m (commitW0 σ m) = (commitW0 σ m, []) := by
            unfold commitRp; simp only [hcond, _root_.and_self, ite_true, hlb, hcp]
          rw [hs, hlb]
          isplitr
          · ipureintro; simp
          iframe inst Hy Hc Hcs
          isplitr
          · ipureintro; exact Hlbnn
          iexists yl, gs, prs
          iframe Hyl Hlbrest
          isplitr
          · ipureintro; exact Hylf
          rw [hcp]; ipureintro; exact Hcpnil
        · -- re-propose the held proposals
          have hs : commitRp σ m (commitW0 σ m) =
              ({ commitW0 σ m with lb := some { lb with clientProposals := none } },
                ps.map Out.repropose) := by
            unfold commitRp; simp only [hcond, _root_.and_self, ite_true, hlb, hcp]
          rw [hs]
          icases Hcp with ⟨%Hcpf, #Hgs, Hprops⟩
          ihave ⟨Hrep, -⟩ := (BigSepL.bigSepL_append).1 $$ Houts
          rw [BigSepL.bigSepL_map Out.repropose]
          wp_auto
          rw [show decide (yl.clientProposals' = slice.nil) = false from decide_eq_false Hcpf.1]
          simp only [Bool.not_false]
          wp_auto
          ihave %Hgslen := ownSlice_len _ _ _ $$ Hgs
          ihave HI : (∃ k : w64, "Hi" ∷ i_ptr ↦ k ∗ "Hp" ∷ (∃ pv : Loc, p_ptr ↦ pv) ∗
              "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.nat k ≤ gs.length⌝ ∗
              "Hprops" ∷ ([∗list] j ↦ g ∈ gs.drop (sint.nat k),
                propHeld γ i false g (ps.getD (sint.nat k + j) default)) ∗
              "Hrep" ∷ ([∗list] x ∈ ps.drop (sint.nat k), outOk γ i (Out.repropose x)) : IProp GF)
            $$ [«i» p Hprops Hrep]
          · iexists W64 0; iframe «i»
            isplitl [p]
            · iexists _; iexact p
            isplitr
            · ipureintro; constructor <;> word
            simp only [show sint.nat (W64 0) = 0 from rfl, List.drop_zero, Nat.zero_add]
            iframe Hprops Hrep
          wp_for HI
          wp_if_destruct
          · -- an iteration
            have hkl : sint.nat k < gs.length := by have := Hgslen.1; word
            have hkp : sint.nat k < ps.length := by rw [← Hcpf.2]; exact hkl
            obtain ⟨g, hg⟩ : ∃ g, gs[sint.nat k]? = some g :=
              ⟨gs[sint.nat k], List.getElem?_eq_getElem hkl⟩
            obtain ⟨pr, hpr⟩ : ∃ pr, ps[sint.nat k]? = some pr :=
              ⟨ps[sint.nat k], List.getElem?_eq_getElem hkp⟩
            rw [List.drop_eq_getElem_cons hkl, List.drop_eq_getElem_cons hkp]
            icases Hprops with ⟨Hg1, Hprops⟩
            icases Hrep with ⟨Hr1, Hrep⟩
            have hgk : gs[sint.nat k] = g := by rw [List.getElem?_eq_getElem hkl] at hg; exact Option.some.inj hg
            have hpk : ps[sint.nat k] = pr := by rw [List.getElem?_eq_getElem hkp] at hpr; exact Option.some.inj hpr
            have hpd : ps.getD (sint.nat k + 0) default = pr := by simp [hpr]
            rw [hgk, hpk, hpd]
            ihave ⟨Hg1, Hro⟩ := propHeld_ro _ _ _ _ _ $$ Hg1
            icases Hro with ⟨%pp, %w, %mu, %proxy, %addr, %cc, %cv, %wc, #Hgp, #Hpp, #Hok, %Hns⟩
            have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z yl.clientProposals'.len := ⟨Hk.1, Hif⟩
            simp only [hb, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index _ (sint.Z k) gs _ g hb.1 $$ [$Hgs] as -
            · ipureintro; rw [show (sint.Z k).toNat = sint.nat k from rfl]; exact hg
            icases Hp with ⟨%pv, Hp⟩
            iStructNamed Hgp
            iStructNamed Hpp
            wp_auto
            wp_apply (hS _ DFrac.discard cv wc Hns) $$ [$Command $Hok] as %str -
            wp_apply wp_slice_literal (V := GoInterface) _
            isplitr
            · ipureintro; rfl
            iintro %_ ⟨-, -⟩
            wp_auto
            wp_apply (wp_ep_Printf hP γ r rr i L p) $$ [$Hrr $Hro]
            ihave ⟨%γc, #Hbag⟩ := fwRO_proposeChan _ _ _ _ _ $$ Hro
            wp_apply (wp_bag_send γc p.pchan g (proposal γ i)) $$ [$Hbag Hg1 Hr1]
            · iapply propHeld_proposal
              iframe Hg1
              simp only [outOk]
              iexact Hr1
            wp_for_post
            iframe
            iexists k + W64 1
            have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by
              have := Hgslen.1; have := Hgslen.2; word
            rw [hk1]
            iframe Hi
            isplitl [Hp]
            · iexists g; iexact Hp
            isplitr
            · ipureintro; constructor
              · have := Hgslen.1; word
              · omega
            isplitl [Hprops]
            · have e : (fun j g => propHeld (GF := GF) γ i false g (ps.getD (sint.nat k + 1 + j) default)) =
                  (fun j g => propHeld γ i false g (ps.getD (sint.nat k + (j + 1)) default)) := by
                funext j g; congr 2; omega
              rw [e]
              iexact Hprops
            iexact Hrep
            done
          · -- the loop's end: `lb.clientProposals = nil`
            isplitr
            · itrivial
            iframe inst Hy Hc Hcs
            isplitr
            · ipureintro; exact Hlbnn
            iexists _, gs, prs
            iframe Hyl
            isplitr
            · ipureintro; exact Hylf
            isplitr
            · ipureintro; rfl
            have hdo : lbDepsOwned { lb with clientProposals := none } = lbDepsOwned lb := rfl
            rw [hdo]
            iexact Hlbrest
      · -- not a no-op: no re-proposal
        have hs : commitRp σ m (commitW0 σ m) = (commitW0 σ m, []) := by
          unfold commitRp
          have : ¬ (Option.map (fun x => x.op) m.command.head? = some opNONE) := by
            rw [hwc]; simp only [List.head?_cons, Option.map_some, Option.some.injEq]
            rw [← Hokp.1]; exact Hif
          simp [this]
        isplitr
        · ipureintro; simp
        iframe inst Hy
        iapply (hskip hs)
        iframe Hc Hcs
        rcases (commitW0 σ m).lb with _ | lb <;> iexact Hylb
    · -- not one command: no re-proposal
      have hs : commitRp σ m (commitW0 σ m) = (commitW0 σ m, []) := by
        unfold commitRp
        have : ¬ m.command.length = 1 := by
          intro h; apply Hif; rw [← Hvslen] at h; word
        simp [this]
      isplitr
      · ipureintro; simp
      iframe inst Hy
      iapply (hskip hs)
      iframe Hc
      isplitl [Hcs Hcms]
      · iapply ownCmds_close _ _ _ vs
        iframe Hcs Hcms; ipureintro; exact Hvslen
      rcases (commitW0 σ m).lb with _ | lb <;> iexact Hylb
  · -- another replica's instance
    have hne : ¬ (toN m.replica = σ.id) := by
      rw [hw.id]; intro h; apply Hif; rw [← hxq, h]
    have e : commitRp σ m (commitW0 σ m) = (commitW0 σ m, []) := by
      unfold commitRp; simp [hne]
    rw [e]
    iframe inst Hy Hc Hcs
    rcases (commitW0 σ m).lb with _ | lb <;> iexact Hylb
  -- the committed record
  unfold epaxos.COMMITTED
  wp_auto
  imod ownCmds_persist $$ Hcs with #Hcs
  ihave %Hcsnn := ownCmds_nonnil _ _ _ hw.cmds $$ Hcs
  ihave Hins := Hclose $$ %p' %(some (commitInst σ m)) Hptrs [Hy Hylb Hds]
  · unfold instAt ownInst
    iexists _
    iframe Hy
    isplitr
    · ipureintro
      simp only [commitInst, stCOMMITTED, stEXECUTED]
      exact ⟨trivial, trivial, trivial, trivial, fun _ => Hyf.2.2.2.2 hnex⟩
    isplitr
    · iexact Hyid
    isplitr
    · unfold cmdsRep; simp only [commitInst]
      iframe Hcs; ipureintro; exact Hcsnn
    isplitl [Hds]
    · iexists _; unfold ownDeps; simp only [commitInst]; iexact Hds
    rw [show decide ((commitInst σ m).status = stEXECUTED) = false from by
      simp [commitInst, stCOMMITTED, stEXECUTED]]
    simp only [commitInst]
    rcases (commitRp σ m (commitW0 σ m)).1.lb with _ | lb <;> iexact Hylb
  -- updateConflicts
  ihave HlS : repRowArr r go!"lastScan" σ.lastScan $$ [HlS]
  · unfold repRowArr; iexact HlS
  ihave HlP : repRowArr r go!"lastPut" σ.lastPut $$ [HlP]
  · unfold repRowArr; iexact HlP
  wp_apply wp_updateConflicts r σ cs m.command DFrac.discard m.replica m.inst m.seq
    ⟨hw.q0, hw.q1⟩ $$ [$Hcs $Hconf $Hmsk $HlS $HlP] as ⟨-, Hconf, Hmsk, HlS, HlP⟩
  -- updateCommitted
  have hib2 : instBounds (upd σ.inst ⟨toN m.replica, toN m.inst⟩ (some (commitInst σ m))) :=
    instBounds_upd _ _ _ Hib hq hw.n1
  ihave Hins : repInsts γ i r (commitIns σ m).inst $$ [Hins]
  · simp only [commitIns]; iexact Hins
  ihave Hcut : repRowArr r go!"CommittedUpTo" (commitIns σ m).committedUpTo $$ [Hcut]
  · simp only [commitIns, repRowArr]; iexact Hcut
  wp_apply wp_updateCommitted γ i r rr L p Rext (commitIns σ m) m.replica ⟨hw.q0, hw.q1⟩ hib2 Hcb
    $$ [$Hrr $Hfw $Hins $Hcut] as ⟨Hins, Hcut⟩
  -- recordInstanceMetadata(r.InstanceSpace[q][n]): the slot read again
  icases repInsts_acc γ i r _ ⟨toN m.replica, toN m.inst⟩ hq hn $$ Hins with
    ⟨%iss', %rows', %row', %ptrs', %ptr', #Hiss', #Hrows', %Hrow', Hptrs', %Hptr', Hx', Hclose'⟩
  icombine Hiss Hiss' gives %Heqi
  subst Heqi
  ihave %Heqr := ownSlice_agree _ _ _ _ _ $$ Hrows Hrows'
  subst Heqr
  have Heqrow : row' = row := by rw [Hrow] at Hrow'; exact (Option.some.inj Hrow').symm
  subst Heqrow
  ihave %Hplen2 := ownSlice_len _ _ _ $$ Hptrs'
  have h1' : 0 ≤ sint.Z (W64 (sint.Z m.replica)) ∧ sint.Z (W64 (sint.Z m.replica)) < sint.Z iss.len := by
    have := hw.q0; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  have h2' : 0 ≤ sint.Z (W64 (sint.Z m.inst)) ∧ sint.Z (W64 (sint.Z m.inst)) < sint.Z row'.len := by
    have := hw.n0; have := hw.n1; have := Hptr'.2
    unfold toN zz at *; constructor <;> word
  simp only [h1', _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row' h1'.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hq']; exact Hrow
  simp only [h2', _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row' _ ptrs' _ ptr' h2'.1 $$ [$Hptrs'] as Hptrs'
  · ipureintro; rw [e2, hn']; exact Hptr'.1
  have hset' : ptrs'.set (toN m.inst) ptr' = ptrs' := by
    have := List.getElem?_eq_some_iff.mp Hptr'.1
    rw [← this.2]; exact List.set_getElem_self this.1
  ihave Hins := Hclose' $$ %ptr' %_ [Hptrs'] Hx'
  · rw [hset']; iexact Hptrs'
  rw [upd_self _ _ _ rfl]
  ihave #Hdur := isReplicaFw_durable _ _ _ _ _ _ $$ Hfw
  wp_apply wp_recordInstanceMetadata $$ [$Hrr $Hdur]
  wp_apply wp_recordCommands $$ [$Hrr $Hdur]
  iapply HΦ
  rw [commitFinal_eq]
  simp only
  rw [← bumpRecvBallot_bumpCrt_mrb σ (toN m.replica) m.inst m.ballot]
  iframe Hins Heut Hconf Hmsk HmaxSeq Hlead Hstore Hpeer Hmrb
  isplitr
  · ipureintro; exact hib2
  isplitr
  · ipureintro; exact cutBounds_updateCommitted _ _ hib2 Hcb
  isplitl [Hcrtsl]
  · iexists crt; iframe Hcrtf Hcrtsl
  unfold repRowArr
  rw [show upd σ.committedUpTo (toN m.replica) (advanceCommitted (commitIns σ m) (toN m.replica)
      MAX_INSTANCE (σ.committedUpTo (toN m.replica))) =
      (updateCommitted (commitIns σ m) (toN m.replica)).committedUpTo from rfl]
  isplitl [Hcut]
  · iexact Hcut
  isplitl [HlS]
  · iexact HlS
  iexact HlP

end heap


end Perennial.github_com.imdea_software.swiftpaxos_epaxos
