/-
The run loop's critical sections, one per kind of event: with the instance lock held (its state,
idle), the peer order step (`lock_peerOrder`), the event's ghost step (`ep_deliverB`,
`ep_recover`; `handlePropose` takes its own), the handler's spec, back to idle.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RunLemmas

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

/-- The instance lock's state part (`instLockInv` without the executor's stack). -/
abbrev lockSt (γ : EpNames) (i : Nat) (r : Loc) : IProp GF :=
  iprop(∃ σ : RState, ownRep γ i r σ ∗ repFrag γ i σ ∗ repIdle γ i)

theorem hctx_unfold (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) :
    hctx γ i r rr L p Rext ord ⊢ pkgInit_epaxos ∗ isReplica γ i r ∗ efld r go!"Replica" ↦□ rr ∗
      isReplicaFw γ rr i L p Rext ∗ prefOrder rr i L ord := by
  unfold hctx; exact .rfl

theorem isReplica_inv (γ : EpNames) (i : Nat) (r : Loc) :
    isReplica (GF := GF) γ i r ⊢ inv protoN (epInv γ) := by
  rw [isReplica_unseal]; unfold isReplicaDef
  iintro ⟨%rr, %L, %p, -, -, -, -, -, #H, -⟩
  iexact H

/-- `ep_deliver` with what it knows of the pre-state (`ep_deliverB`). -/
theorem ep_deliverPre (γ : EpNames) (E : CoPset) (i : Nat) (σ : RState) (fr n : Nat) (m : Msg)
    (hE : ↑protoN ⊆ E) (hi : i < nR) (hfr : fr < nR) (hne : fr ≠ i) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ repIdle γ i -∗ msgSent γ fr i n m -∗
      delivTok γ i fr n -∗
      £ 1 ={E}=∗ ⌜deliverPre fr i n m σ⌝ ∗ repFrag γ i (hMsg σ m).1 ∗ outsOk γ i (hMsg σ m).2 := by
  rw [epInv_unseal, epInvDef_eq, repIdle_eq, outsOk_eq]; unfold repFrag
  iintro #Hinv Hf Hidle #Hs Ht Hlc
  iapply ep_deliverB γ protoN E i σ fr n m hE hi hfr hne $$ Hinv Hf Hidle Hs Ht Hlc

/-- A protocol message's critical section (all kinds but `Commit`): from the handler's spec. -/
theorem wp_deliverCall (k : MsgKind) (meth : GoString) (hs : HandlerSpec (GF := GF) k meth) (γ : EpNames)
    (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (l : Loc) (m : Msg) (fr n : Nat)
    (hk : m.kind = some k) (hwf : m.wf) (hfr : fr < nR) (hne : fr ≠ i) (hi : i < nR)
    (hL : L.length = nR) :
    {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ lockSt γ i r ∗ ownMsg l m (DFrac.own 1) ∗
        msgSent γ fr i n m ∗ delivTok γ i fr n ∗ £ 1 ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! meth)) (Val #l))
    {{ RET #(); lockSt γ i r }} := by
  iintro %Φ ⟨#Hctx, ⟨%σ, Hrep, Hf, Hidle⟩, Hm, #Hs, Ht, Hlc1, Hlc2⟩ HΦ
  icases hctx_unfold γ i r rr L p Rext ord $$ Hctx with ⟨#Hpk, #Hisr, #Hrr, #Hfw, #Hpo⟩
  ihave #Hinv := isReplica_inv $$ Hisr
  iapply fupd_wp
  imod lock_peerOrder γ i r rr L ord σ hi hL $$ Hinv Hrr Hpo Hrep Hf Hlc1 with ⟨Hrep, Hf⟩
  imod ep_deliverPre γ ⊤ i _ fr n m (by solve_ndisj) hi hfr hne $$ Hinv Hf Hidle Hs Ht Hlc2
    with ⟨%Hpre, Hf, Houts⟩
  imodintro
  wp_apply (hs γ i r rr L p Rext ord _ l m fr n Hpre hk hwf hne rfl)
    $$ [$Hctx $Hrep $Hm $Hf $Houts] as Hpost
  iapply HΦ
  unfold lockSt
  iexact Hpost

/-- The commit's critical section (`wp_handleCommit`). -/
theorem wp_commitCall (hP : dlog.Logger.Printf.spec (GF := GF)) (hS : CmdStringSpec (GF := GF)) (γ : EpNames)
    (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (l : Loc) (m : Msg) (fr n : Nat)
    (hk : m.kind = some .commit) (hfr : fr < nR) (hne : fr ≠ i) (hi : i < nR)
    (hL : L.length = nR) :
    {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ lockSt γ i r ∗ ownMsg l m (DFrac.own 1) ∗
        msgSent γ fr i n m ∗ delivTok γ i fr n ∗ £ 1 ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handleCommit")) (Val #l))
    {{ RET #(); lockSt γ i r }} := by
  rcases m with _ | _ | _ | _ | _ | _ | c | _ | _ | _ | _ <;> simp [Msg.kind] at hk
  iintro %Φ ⟨#Hctx, ⟨%σ, Hrep, Hf, Hidle⟩, Hm, #Hs, Ht, Hlc1, Hlc2⟩ HΦ
  icases hctx_unfold γ i r rr L p Rext ord $$ Hctx with ⟨#Hpk, #Hisr, #Hrr, #Hfw, #Hpo⟩
  ihave #Hinv := isReplica_inv $$ Hisr
  iapply fupd_wp
  imod lock_peerOrder γ i r rr L ord σ hi hL $$ Hinv Hrr Hpo Hrep Hf Hlc1 with ⟨Hrep, Hf⟩
  imod ep_deliverPre γ ⊤ i _ fr n _ (by solve_ndisj) hi hfr hne $$ Hinv Hf Hidle Hs Ht Hlc2
    with ⟨%Hpre, Hf, Houts⟩
  imodintro
  have hw := commitWf_of_pre Hpre
  have hm : ∀ σ0 : RState, hMsg σ0 (.commit c) = hCommit σ0 c := fun σ0 => rfl
  rw [hm]
  icases outsOk_noSend γ i _ (hCommit_noSend _ c) $$ Houts with ⟨Hidle, Houts⟩
  unfold ownMsg
  wp_apply (wp_handleCommit hP hS γ i r _ l c rr L p Rext hw) $$ [$Hpk $Hrr $Hfw $Hrep $Hm $Houts]
    as Hrep
  iapply HΦ
  unfold lockSt
  iexists _
  iframe

/-- `ep_recover` with the pre-state's invariant (`ep_recoverB`). -/
theorem ep_recoverPre (γ : EpNames) (E : CoPset) (i : Nat) (σ : RState) (x : InstId) (n : w32)
    (hE : ↑protoN ⊆ E) (hi : i < nR) (hq : x.q < nR) (hn : (x.i : Int) ≤ zz n) :
    ⊢ inv protoN (epInv (GF := GF) γ) -∗ repFrag γ i σ -∗ repIdle γ i -∗ crtLb γ i x.q n -∗ £ 1 ={E}=∗
      ⌜∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ⌝ ∗
      repFrag γ i (hRecover σ x).1 ∗ outsOk γ i (hRecover σ x).2 := by
  rw [epInv_unseal, epInvDef_eq]; rw [repIdle_eq, outsOk_eq]
  exact ep_recoverB γ protoN E i σ x n hE hi hq hn

/-- A recovery request's critical section (`ep_recover`, then the handler's spec). -/
theorem wp_recoverCall (hs : RecoverSpec (GF := GF)) (γ : EpNames)
    (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (q k : Nat) (nb : w32) (hq : q < nR) (hk : (k : Int) ≤ zz nb) (hi : i < nR)
    (hL : L.length = nR) :
    {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ lockSt γ i r ∗ crtLb γ i q nb ∗ £ 1 ∗ £ 1 }}
      (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"startRecoveryForInstance"))
        (Val #(W32 q))) (Val #(W32 k)))
    {{ RET #(); lockSt γ i r }} := by
  iintro %Φ ⟨#Hctx, ⟨%σ, Hrep, Hf, Hidle⟩, #Hlb, Hlc1, Hlc2⟩ HΦ
  icases hctx_unfold γ i r rr L p Rext ord $$ Hctx with ⟨#Hpk, #Hisr, #Hrr, #Hfw, #Hpo⟩
  ihave #Hinv := isReplica_inv $$ Hisr
  iapply fupd_wp
  imod lock_peerOrder γ i r rr L ord σ hi hL $$ Hinv Hrr Hpo Hrep Hf Hlc1 with ⟨Hrep, Hf⟩
  ihave %Hle := crtLb_valid γ i q _ nb $$ Hf Hlb
  imod ep_recoverPre γ ⊤ i _ ⟨q, k⟩ nb (by solve_ndisj) hi hq hk $$ Hinv Hf Hidle Hlb Hlc2
    with ⟨%Hpre, Hf, Houts⟩
  imodintro
  wp_apply (hs γ i r rr L p Rext ord _ ⟨q, k⟩ Hpre hq (Int.le_trans hk Hle) rfl)
    $$ [$Hctx $Hrep $Hf $Houts] as Hpost
  iapply HΦ
  unfold lockSt
  iexact Hpost

/-- A proposal's critical section (`handlePropose` takes its own step). -/
theorem wp_proposeCall (hs : ProposeSpec (GF := GF)) (γ : EpNames)
    (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs) (Rext : IProp GF)
    (ord : List w32) (g : Loc) (hi : i < nR) (hL : L.length = nR) :
    {{ hctx (GF := GF) γ i r rr L p Rext ord ∗ lockSt γ i r ∗ proposal γ i g ∗ cpcOwn r ∗ £ 1 }}
      (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"handlePropose")) (Val #g))
    {{ RET #(); lockSt γ i r ∗ cpcOwn r }} := by
  iintro %Φ ⟨#Hctx, ⟨%σ, Hrep, Hf, Hidle⟩, Hg, Hcpc, Hlc1⟩ HΦ
  icases hctx_unfold γ i r rr L p Rext ord $$ Hctx with ⟨#Hpk, #Hisr, #Hrr, #Hfw, #Hpo⟩
  ihave #Hinv := isReplica_inv $$ Hisr
  iapply fupd_wp
  imod lock_peerOrder γ i r rr L ord σ hi hL $$ Hinv Hrr Hpo Hrep Hf Hlc1 with ⟨Hrep, Hf⟩
  imodintro
  wp_apply (hs γ i r rr L p Rext ord _ g rfl) $$ [$Hctx $Hrep $Hf $Hidle $Hg $Hcpc]
    as ⟨⟨%σ', Hrep, Hf, Hidle⟩, Hcpc⟩
  iapply HΦ
  iframe Hcpc
  unfold lockSt
  iexists _
  iframe

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
