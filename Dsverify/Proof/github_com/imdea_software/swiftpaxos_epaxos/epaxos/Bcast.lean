/-
The broadcasts (`bcastAccept`, `bcastPreAccept`, `bcastCommit`, `bcastPrepare`): one model
`bcastStep` per `r.alive(q)` read (`ep_bcastStep`, with the value read), then on `true` the
`SendMsg` with the protocol layer's send update (`ep_sendUpd`) or, if the peer is not connected,
the `lose` step (`ep_sendLost`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HCtx
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Alive
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.Log

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model epaxosProof

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## Pure facts -/

theorem bcastRep_noTrack (σ : RState) (b : Bcast) (a : Bool) (h : b.trackPA = false) :
    bcastRep σ b a = σ := by
  unfold bcastRep; simp [h]

/-- The peers of the thrifty broadcasts, from the order `ord` (a permutation of the ids, `i`
last): the first `N - 1`, in range and not `i`. -/
theorem prefPeers_ok (i : Nat) (ord : List w32) (hp : (ord.map (fun x => sint.nat x)).Perm
    (List.range nR)) (hl : ord[nR - 1]? = some (W32 i)) (hi : i < nR)
    (hnn : ∀ o ∈ ord, 0 ≤ sint.Z o) (k : Nat) (hk : k < nR - 1) :
    ∃ t : Nat, ord[k]? = some (W32 t) ∧ t < nR ∧ t ≠ i ∧ sint.nat (W32 (t : Int)) = t := by
  have hlen : ord.length = nR := by
    have := hp.length_eq; simpa using this
  have hk' : k < ord.length := by rw [hlen]; omega
  have hmem : sint.nat ord[k] ∈ List.range nR :=
    hp.subset (List.mem_map.mpr ⟨ord[k], List.getElem_mem hk', rfl⟩)
  have hlt : sint.nat ord[k] < nR := List.mem_range.mp hmem
  have hnd : (ord.map (fun x => sint.nat x)).Nodup := hp.nodup_iff.mpr List.nodup_range
  have hl' : ord[nR - 1]'(by rw [hlen]; unfold nR; omega) = W32 i := by
    rw [List.getElem?_eq_getElem (by rw [hlen]; unfold nR; omega)] at hl
    exact Option.some.inj hl
  have hne : sint.nat ord[k] ≠ i := by
    intro he
    have h1 : (ord.map (fun x => sint.nat x))[k]'(by simp; omega) =
        (ord.map (fun x => sint.nat x))[nR - 1]'(by simp [hlen]; unfold nR; omega) := by
      simp only [List.getElem_map, he, hl']
      have : i < 5 := hi
      unfold sint.nat; word
    have := hnd.getElem_inj.mp h1
    unfold nR at this hk; omega
  have hnn' : 0 ≤ sint.Z ord[k] := hnn _ (List.getElem_mem hk')
  have ho : ord[k] = W32 (sint.nat ord[k] : Int) := by
    have : sint.nat ord[k] < 5 := hlt
    unfold sint.nat at *
    apply BitVec.eq_of_toInt_eq
    have e : ((sint.Z ord[k]).toNat : Int) = sint.Z ord[k] := Int.toNat_of_nonneg hnn'
    rw [e]
    word
  refine ⟨sint.nat ord[k], ?_, hlt, hne, ?_⟩
  · rw [List.getElem?_eq_getElem hk', ← ho]
  · rw [← ho]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- A command field's commands, read-only (`nil` for `none`: the empty list). -/
theorem cmdsRep_dup (sl : GoSlice) (o : Option (List WCmd)) :
    cmdsRep (GF := GF) sl o ⊢ cmdsRep sl o ∗ ownCmds sl (o.getD []) DFrac.discard := by
  rcases o with _ | cs
  · unfold cmdsRep
    iintro %Hnil
    isplitr
    · ipureintro; exact Hnil
    rw [Hnil]
    iapply ownCmds_close _ _ _ []
    isplitl []
    · iapply ownSlice_nil
    isplitr
    · ipureintro; rfl
    · iempintro
  · unfold cmdsRep
    iintro ⟨%Hnn, #Hc⟩
    simp only [Option.getD_some]
    iframe Hc
    ipureintro; exact Hnn

/-- `r.SendMsg` through the embedded framework. -/
theorem wp_ep_SendMsg (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (r rr : Loc) (i : Nat)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (t : Nat) (msg : GoInterface)
    (m : Msg) (dq : DFrac) (Ψ Ψnil : IProp GF) (dq1 dq2 : DFrac := dq) :
    {{ pkgInit_epaxos (GF := GF) ∗ pkgInit_replica ∗ efld r go!"Replica" ↦□ rr ∗
        ⌜t < L.length ∧ t ≠ i ∧ m.isProto = true ∧ m.wf⌝ ∗
        isReplicaFw γ rr i L p Rext ∗ msgObj msg m dq dq1 dq2 ∗ (sendUpd γ i t m Ψ ∧ Ψnil) }}
      (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"SendMsg"))
        (Val #(W32 t))) (Val #m.code)) (Val #msg))
    {{ RET #(); msgObj msg m dq dq1 dq2 ∗ (Ψ ∨ Ψnil) }} := by
  wp_start as ⟨#Hrr, %Ht, #Hfw, Hm, Hu⟩
  wp_auto
  wp_apply (hS γ rr i L p Rext t msg m dq dq1 dq2 Ψ Ψnil) $$ [$Hfw $Hm $Hu]
  · ipureintro; exact Ht
  iintro Hpost
  iapply HΦ $$ Hpost

/-- A broadcast's read of `alive` = `a` for its next peer `pr` (the ghost step), then on `true`
the send (`SendMsg` with the send update, or the `lose` step). -/
theorem bcast_step (γ : EpNames) (i : Nat) (σ : RState) (b : Bcast) (pr : Nat) (ps : List Nat)
    (a : Bool) (hb : b.peers = pr :: ps) (hpr : pr < nR) (hi : i < nR) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ pendFrag γ i (some b) -∗ outboxesNil γ i -∗
      £ 1 ={⊤}=∗ repFrag γ i (bcastRep σ b a) ∗ pendFrag γ i (b.next a) ∗
        outboxFrag γ i pr (if a then [b.m] else []) ∗
        (outboxFrag γ i pr [] -∗ outboxesNil γ i) := by
  iintro #Hinv Hf Hp Hob Hlc
  unfold outboxesNil
  have hget : (List.range nR)[pr]? = some pr := by simp [hpr]
  icases bigSepL_get_acc (Φ := fun _ to => outboxFrag γ i to []) hget $$ Hob with ⟨Ho, Hclose⟩
  imod ep_bcastStep γ ⊤ i σ b pr ps a CoPset.subseteq_top hi hb $$ Hinv Hf Hp Ho Hlc with
    ⟨Hf, Hp, Ho⟩
  imodintro
  iframe Hf Hp Ho
  iexact Hclose

/-- The send of a broadcast's message `m` to `pr` (its outbox `[m]`): `SendMsg` with
`ep_sendUpd`, or `ep_sendLost` if the peer is not connected. -/
theorem wp_bcast_send (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (r rr : Loc) (i : Nat)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (pr : Nat)
    (msg : GoInterface) (m : Msg) (dq : DFrac) (code : w8) (hc : code = m.code)
    (h : pr < L.length ∧ pr ≠ i ∧ m.isProto = true ∧ m.wf) (dq1 dq2 : DFrac := dq) :
    {{ hdCtx γ i r rr L p Rext ord ∗ outboxFrag γ i pr [m] ∗ msgObj msg m dq dq1 dq2 }}
      (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"SendMsg"))
        (Val #(W32 pr))) (Val #code)) (Val #msg))
    {{ RET #(); msgObj msg m dq dq1 dq2 ∗ outboxFrag γ i pr [] }} := by
  subst hc
  wp_start_folded as ⟨#Hctx, Ho, Hm⟩
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, -, #Hinv, -⟩
  iapply wp_fupd
  wp_apply (wp_ep_SendMsg hS γ r rr i L p Rext pr msg m dq (outboxFrag γ i pr [])
      iprop(|={⊤}=> outboxFrag γ i pr []) dq1 dq2) $$ [$Hpe $Hpr $Hrr $Hfw $Hm Ho]
  · isplitr
    · ipureintro; exact h
    isplit
    · iapply ep_sendUpd γ i pr m [] $$ Hinv Ho
    · iapply ep_sendLost γ ⊤ i pr m [] CoPset.subseteq_top $$ Hinv Ho
  iintro ⟨Hm, Hor⟩
  icases Hor with (Ho | Ho)
  · imodintro; iapply HΦ; iframe Hm Ho
  · imod Ho
    iapply HΦ; iframe Hm Ho

set_option maxHeartbeats 4000000 in
set_option pp.deepTerms true in
set_option pp.deepTerms.threshold 1000 in
/-- `bcastAccept(replica, instance)`: the Accept built from the instance's bookkeeping `lb`, sent
to the first `N / 2` alive peers of `PreferredPeerOrder[0..N-2]` (the pending broadcast run to its
end; `bcastRep` leaves the state unchanged: no `preAcceptsSent`). -/
theorem wp_bcastAccept (hS : replica.Replica.SendMsg.spec (GF := GF)) (γ : EpNames) (i : Nat) (r rr : Loc)
    (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (ord : List w32) (σ : RState)
    (replica n : w32) (w : InstRec) (lb : LbRec) (hwf : RepWf i σ ord)
    (hq : 0 ≤ zz replica ∧ zz replica < nR) (hn : 0 ≤ zz n ∧ toN n + 1 < MAX_INSTANCE)
    (hw : σ.inst ⟨toN replica, toN n⟩ = some w) (hlb : w.lb = some lb)
    (hdo : lbDepsOwned lb = false) (hm : (Msg.accept (acceptOf σ replica n lb)).wf)
    (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) :
    {{ hdCtx γ i r rr L p Rext ord ∗ ownRep γ i r σ ∗ repFrag γ i σ ∗
        pendFrag γ i (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).norm ∗
        outboxesNil γ i }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"bcastAccept"))
        (Val #replica)) (Val #n))
    {{ RET #(); ownRep γ i r σ ∗ repFrag γ i σ ∗ pendFrag γ i none ∗ outboxesNil γ i }} := by
  wp_start as ⟨#Hctx, Hrep, Hf, Hp, Hob⟩
  ihave #Hctx0 := Hctx
  unfold hdCtx
  icases Hctx with ⟨#Hpe, #Hpr, #Hrr, #Hfw, #Hro, #Hinv, #Hpo⟩
  rw [ownRep_unseal]; unfold ownRepDef
  icases Hrep with ⟨%Hib, %Hcb, Hinsts, Hcrt, Hcut, Heut, Hconf, Hmsk, HmaxSeq, Hlead, Hmrb,
    Hstore, Hpeer⟩
  have hq' : toN replica < nR := by
    have := hq.1; have := hq.2; simp only [toN, zz] at *; omega
  have hn' : toN n < MAX_INSTANCE := by have := hn.2; omega
  icases repInsts_acc γ i r σ.inst ⟨toN replica, toN n⟩ hq' hn' $$ Hinsts with
    ⟨%iss, %rows, %row, %ptrs, %ptr, #Hiss, #Hrows, %Hrow, Hptrs, %Hptr, Hx, Hclose⟩
  rw [hw]
  unfold instAt ownInst
  icases Hx with ⟨%y, Hy, %Hyf, #Hyid, Hycmds, Hydeps, Hylb⟩
  rw [hlb]
  icases Hylb with ⟨%Hlbnn, Hlb⟩
  unfold ownLb
  icases Hlb with ⟨%yl, %gs, %prs, Hyl, %Hylf, Hcp, Hlcmds, Hldeps, Hlprs, %Hlprsl, Hlpr⟩
  wp_apply wp_with_defer_recover as %defer %pnc Hdefer Hpnc
  ihave %Hrlen := ownSlice_len _ _ _ $$ Hrows
  ihave %Hplen := ownSlice_len _ _ _ $$ Hptrs
  have e1 : sint.Z (W64 (sint.Z replica)) = sint.Z replica := by word
  have e2 : sint.Z (W64 (sint.Z n)) = sint.Z n := by word
  have hqe : (sint.Z replica).toNat = toN replica := rfl
  have hne : (sint.Z n).toNat = toN n := rfl
  have h1 : 0 ≤ sint.Z (W64 (sint.Z replica)) ∧ sint.Z (W64 (sint.Z replica)) < sint.Z iss.len := by
    have := hq.1; have hl := (List.getElem?_eq_some_iff.mp Hrow).1
    unfold toN zz at *; constructor <;> word
  simp only [h1, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index iss _ rows _ row h1.1 $$ [$Hrows] as -
  · ipureintro; rw [e1, hqe]; exact Hrow
  have h2 : 0 ≤ sint.Z (W64 (sint.Z n)) ∧ sint.Z (W64 (sint.Z n)) < sint.Z row.len := by
    have := hn.1; have := hn.2; have := Hptr.2
    unfold toN zz at *; constructor <;> word
  simp only [h2, _root_.and_self, ↓reduceIte]
  wp_apply wp_load_slice_index row _ ptrs _ ptr h2.1 $$ [$Hptrs] as Hptrs
  · ipureintro; rw [e2, hne]; exact Hptr.1
  ihave #Hfro := isReplicaFw_ro _ _ _ _ _ _ $$ Hfw
  ihave ⟨#HN, #HF, #HId, #HSt, #HRPC, #HPC, #HThr, #HEx, #HDr, #HSh, #HStats, #HStm, #HAl, %HLn⟩ :=
    fwRO_fields _ _ _ _ _ $$ Hfro
  unfold epROFields
  icases Hro with ⟨-, -, -, -, #Hacc, -⟩
  unfold prefOrder
  icases Hpo with ⟨%po, #Hpof, #Hpos, %Hpop⟩
  wp_auto
  ipersist «$r0»
  ihave #Hea : «$r0_ptr» ↦□ epaxos.Accept.mk (W32 i) replica n yl.lastTriedBallot' yl.cmds'
      yl.seq' yl.deps' $$ [«$r0»]
  · iexact «$r0»
  iclear «$r0»
  -- the message object
  rw [hdo]
  simp only [Bool.false_eq_true, if_false]
  icases Hldeps with ⟨%dq0, Hldeps⟩
  ipersist Hldeps
  icases cmdsRep_dup _ _ $$ Hlcmds with ⟨Hlcmds, #Hcmd⟩
  -- the state, closed again (the loop reads only persistent data)
  have hset : ptrs.set (toN n) ptr = ptrs := by
    have := List.getElem?_eq_some_iff.mp Hptr.1
    rw [← this.2]; exact List.set_getElem_self this.1
  ihave Hins := Hclose $$ %ptr %(some w) [Hptrs] [Hy Hycmds Hydeps Hyl Hcp Hlcmds Hlprs Hlpr]
  · simp only [hset]; iexact Hptrs
  · iexists y
    iframe Hy Hyid Hycmds Hydeps
    isplitr
    · ipureintro; exact Hyf
    rw [hlb]
    isplitr
    · ipureintro; exact Hlbnn
    iexists yl, gs, prs
    iframe Hyl Hcp Hlcmds Hlprs Hlpr
    rw [hdo]
    isplitr
    · ipureintro; exact Hylf
    isplitl []
    · simp only [Bool.false_eq_true, ite_false]; iexists DFrac.discard; iexact Hldeps
    ipureintro; exact Hlprsl
  rw [upd_self _ _ _ hw]
  ihave Hrep : ownRep γ i r σ $$ [Hins Hcrt Hcut Heut Hconf Hmsk HmaxSeq Hlead Hmrb Hstore Hpeer]
  · rw [ownRep_unseal]; unfold ownRepDef
    iframe
    ipureintro; exact ⟨Hib, Hcb⟩
  -- the loop
  have hL5 : L.length = nR := HLn.1
  have hi : i < nR := hwf.hi
  obtain ⟨hperm, hlast, -⟩ := Hpop
  rw [hL5] at hperm hlast
  have hpeers : (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers =
      (ord.map (fun x => sint.nat x)).take (nR - 1) := by
    simp only [bcastAcceptOf, hwf.po]
  have hordlen : ord.length = nR := by have := hperm.length_eq; simpa using this
  ihave HI : (∃ k s : Nat, "Hq" ∷ q_ptr ↦ W64 k ∗ "Hs" ∷ sent_ptr ↦ W64 s ∗
      "%Hks" ∷ ⌜k ≤ nR - 1 ∧ s < nR / 2⌝ ∗ "Hf" ∷ repFrag γ i σ ∗
      "Hp" ∷ pendFrag γ i ({ bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
        peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop k,
        sent := s }).norm ∗
      "Hob" ∷ outboxesNil γ i : IProp GF) $$ [q sent Hf Hp Hob]
  · iexists 0, 0
    iframe q sent Hf Hob
    isplitr
    · ipureintro; unfold nR; omega
    have e0 : ({ bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
        peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop 0,
        sent := 0 } : Bcast) = bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) := rfl
    rw [e0]
    iexact Hp
  wp_for HI
  ihave %Hpolen := ownSlice_len _ _ _ $$ Hpos
  wp_if_destruct
  · -- an iteration: peer `ord[k]`
    have hk : k < nR - 1 := by
      have h := Hif; rw [hL5] at h; unfold nR at *; have := Hks.1
      simp only [show (5 : Nat) - 1 = 4 from rfl] at *
      have : sint.Z (W64 ((k : Nat) : Int)) = (k : Int) := by word
      word
    obtain ⟨t, hot, htn, hti, htt⟩ := prefPeers_ok i ord hperm hlast hi hord k hk
    have hb : 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z po.len := by
      have := Hpolen.1; have := Hpolen.2; rw [hordlen] at *; unfold nR at *
      constructor <;> word
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index po _ ord _ (W32 t) hb.1 $$ [$Hpos] as -
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact hot
    wp_apply (lc := 1) (wp_alive γ i r rr L p Rext (W32 t) ⟨by word, by rw [hL5]; unfold nR at *; word⟩)
      $$ [$Hrr $Hfw] as %a -
    -- the broadcast's ghost step for this read
    have hdrop : ((ord.map (fun x => sint.nat x)).take (nR - 1)).drop k =
        t :: ((ord.map (fun x => sint.nat x)).take (nR - 1)).drop (k + 1) := by
      have hk' : k < ((ord.map (fun x => sint.nat x)).take (nR - 1)).length := by
        simp [hordlen]; omega
      rw [List.drop_eq_getElem_cons hk']
      congr 1
      simp only [List.getElem_take, List.getElem_map]
      rw [List.getElem?_eq_getElem (by omega)] at hot
      rw [Option.some.inj hot, htt]
    have hnorm : ({ bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
        peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop k,
        sent := s } : Bcast).norm = some { bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
        peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop k,
        sent := s } := by
      unfold Bcast.norm
      rw [if_neg]
      rw [hpeers, hdrop]
      simp only [bcastAcceptOf, reduceCtorEq, false_or]
      exact Nat.not_le.mpr Hks.2
    rw [hnorm]
    iapply fupd_wp
    imod bcast_step γ i σ _ t _ a (by rw [hpeers]; exact hdrop) htn hi $$ Hinv Hf Hp Hob Hlc1 with
      ⟨Hf, Hp, Ho, Hobc⟩
    imodintro
    rw [bcastRep_noTrack _ _ _ rfl]
    have hk1 : W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) := by
      have : k < 4 := hk; word
    have hdrop' : (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop k =
        t :: (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop (k + 1) := by
      rw [hpeers]; exact hdrop
    have hnext : ∀ a : Bool, ({ bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
        peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop k,
        sent := s } : Bcast).next a =
        ({ bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
        peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop (k + 1),
        sent := if a then s + 1 else s } : Bcast).norm := by
      intro a
      unfold Bcast.next
      simp only [hdrop']
      cases a <;> rfl
    rw [hnext]
    rcases a with _ | _
    · -- not alive: the next peer
      simp only [Bool.false_eq_true, ↓reduceIte]
      wp_auto
      wp_for_post
      iframe
      iexists k + 1, s
      rw [← hk1]
      iframe Hq Hs Hf Hp
      isplitr
      · ipureintro; exact ⟨by omega, Hks.2⟩
      iapply Hobc $$ Ho
    · -- alive: the send
      wp_auto
      simp only [hb, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index po _ ord _ (W32 t) hb.1 $$ [$Hpos] as -
      · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact hot
      ihave Hmsg : msgObj (interface.mkOk (go.GoType.PointerType epaxos.Accept.ty) #«$r0_ptr»)
          (Msg.accept (acceptOf σ replica n lb)) DFrac.discard $$ []
      · unfold msgObj
        iexists MsgKind.accept, «$r0_ptr»
        isplitr
        · ipureintro; exact ⟨rfl, rfl⟩
        unfold ownMsg ownAccept acceptOf ownDeps
        iexists yl.cmds', yl.deps'
        rw [hwf.id, ← Hylf.2.2.2.2.2.2.2.1, ← Hylf.2.2.2.2.2.2.2.2.2.1]
        iframe Hea Hcmd Hldeps
      wp_apply (wp_bcast_send hS γ r rr i L p Rext ord t
        (interface.mkOk (go.GoType.PointerType epaxos.Accept.ty) #«$r0_ptr»)
        (Msg.accept (acceptOf σ replica n lb)) DFrac.discard (W8 13) rfl
        ⟨by rw [hL5]; exact htn, hti, rfl, hm⟩) $$ [Ho Hmsg]
      · isplitl []
        · unfold hdCtx epROFields prefOrder; iexact Hctx0
        iframe Hmsg
        rw [show (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).m =
          Msg.accept (acceptOf σ replica n lb) from rfl]
        iexact Ho
      iintro ⟨-, Ho⟩
      wp_auto
      have hn2 : sint.Z (BitVec.sdiv (W64 (L.length : Int)) (W64 2)) = 2 := by rw [hL5]; rfl
      have hs1 : sint.Z (W64 (s : Int) + W64 1) = (s : Int) + 1 := by
        have := Hks.2; unfold nR at *; word
      rw [hn2, hs1]
      have hs1' : W64 (s : Int) + W64 1 = W64 ((s + 1 : Nat) : Int) := by
        have := Hks.2; unfold nR at *; word
      rw [hs1']
      ihave Hob := Hobc $$ Ho
      wp_if_destruct
      · -- enough sends: the loop ends
        wp_for_post
        have hnone : ({ bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
            peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop (k + 1),
            sent := s + 1 } : Bcast).norm = none := by
          unfold Bcast.norm
          rw [if_pos]
          right
          simp only [bcastAcceptOf]
          have := Hif; unfold nR at *; omega
        rw [hnone]
        wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
        iapply HΦ
        rw [ownRep_unseal]; unfold ownRepDef
        iframe Hrep Hf Hp Hob
      · -- the next peer
        wp_for_post
        iframe
        iexists k + 1, s + 1
        rw [← hk1]
        iframe Hq Hs Hf Hp Hob
        ipureintro; constructor
        · omega
        · unfold nR at *; omega
  · -- every peer read: the loop ends
    have hk4 : k = nR - 1 := by
      have h := Hif; rw [hL5] at h; have := Hks.1; unfold nR at *
      simp only [show (5 : Nat) - 1 = 4 from rfl] at *
      word
    have hnone : ({ bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb) with
        peers := (bcastAcceptOf σ ⟨toN replica, toN n⟩ (acceptOf σ replica n lb)).peers.drop k,
        sent := s } : Bcast).norm = none := by
      unfold Bcast.norm
      rw [if_pos]
      left
      rw [hpeers, hk4]
      simp
    rw [hnone]
    wp_apply wp_recoverPanic $$ [$Hpnc] as Hpnc
    iapply HΦ
    rw [ownRep_unseal]; unfold ownRepDef
    iframe Hrep Hf Hp Hob

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
