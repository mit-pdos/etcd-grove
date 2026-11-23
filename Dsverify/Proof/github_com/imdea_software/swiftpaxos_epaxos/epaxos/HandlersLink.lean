/-
The handlers' specs in the run loop's form (`RunSpec.lean`'s `HandlerSpec`, `RecoverSpec`,
`ProposeSpec`): `handlerSpecs_of`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.RunSpec
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlePrepareReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlePrepare
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandleAccept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandleTPA
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlePreAccept
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandlePreAcceptReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.HandleAcceptReply
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.OutsWfProof

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

theorem pkgInit_replica_of_epaxos : pkgInit_epaxos (GF := GF) ⊢ pkgInit_replica := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF)
    pkg_id.github_com.imdea_software.swiftpaxos_epaxos.epaxos).trans ?_
  show iprop(_ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ _ ∗ pkgInit_replica ∗ _) ⊢ _
  iintro ⟨-, -, -, -, -, -, -, -, -, H, -⟩
  iexact H

/-- The run loop's context gives the handlers'. -/
theorem hdCtx_of_hctx (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) :
    hctx γ i r rr L p Rext ord ⊢ hdCtx γ i r rr L p Rext ord := by
  unfold hctx hdCtx
  iintro #⟨Hpk, Hisr, Hrr, Hfw, Hpo⟩
  ihave #Hpr := pkgInit_replica_of_epaxos $$ Hpk
  rw [isReplica_unseal]; unfold isReplicaDef
  icases Hisr with ⟨%rr', %L', %p', -, -, -, #Hro, -, #Hinv, -⟩
  iframe Hpk Hpr Hrr Hfw Hro Hinv Hpo

/-! ### What the handlers' premises need of `deliverPre` (model facts) -/

theorem repWf_of_pre {fr i n : Nat} {m : Msg} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n m σ) (hpo : σ.peerOrder = ord.map (fun x => sint.nat x)) :
    RepWf i σ ord := by
  obtain ⟨S, hS, hi, -, -, hσ, -, -⟩ := h
  refine ⟨?_, hi, hpo⟩
  rw [← hσ]; exact hS.1.1.1 i hi

/-- A delivered message is in the system's messages. -/
theorem pre_msgs {fr i n : Nat} {m : Msg} {σ : RState} (h : deliverPre fr i n m σ) :
    ∃ S : Sys, Inv S ∧ i < nR ∧ fr < nR ∧ S.rep i = σ ∧ m ∈ S.msgs fr i := by
  obtain ⟨S, hS, hi, hfr, -, hσ, hn, -⟩ := h
  refine ⟨S, hS, hi, hfr, hσ, ?_⟩
  unfold Sys.msgs
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? hn))

theorem pre_ids {fr i n : Nat} {m : Msg} {σ : RState} (h : deliverPre fr i n m σ) {q k : w32}
    (hm : m.rawId = some (q, k)) : 0 ≤ zz q ∧ zz q < nR ∧ 0 ≤ zz k ∧ toN k + 1 < MAX_INSTANCE := by
  obtain ⟨S, hS, -, -, -, hmem⟩ := pre_msgs h
  exact (hS.1.2.1 _ _ _ hmem).1 q k hm

theorem link_toN_W32 (fr : Nat) (h : fr < nR) : toN (W32 (fr : Int)) = fr := by
  unfold toN; have : fr < 5 := h
  rw [show sint.Z (W32 (fr : Int)) = (fr : Int) by word]; simp

theorem hdCtx_ordNe (γ : EpNames) (i : Nat) (r rr : Loc) (L : List GoString) (p : FwPtrs)
    (Rext : IProp GF) (ord : List w32) :
    hdCtx γ i r rr L p Rext ord ⊢ ⌜ord ≠ []⌝ := by
  unfold hdCtx prefOrder
  iintro ⟨-, -, -, -, -, -, %po, -, -, %H⟩
  ipureintro; intro h; rw [h] at H; simp at H

/-- Every message a delivery's step sends or broadcasts is encodable (HANDLERS-5,
`deliver_outsWf_of`). -/
theorem deliver_outsWf {fr i n : Nat} {m : Msg} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n m σ) (hpo : σ.peerOrder = ord.map (fun x => sint.nat x))
    (hne : ord ≠ []) : OutsWf (hMsg σ m).2 :=
  deliver_outsWf_of h (by rw [hpo]; simpa using hne)

theorem prepWf_of_pre {fr i n : Nat} {x : Prepare} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n (.prepare x) σ) (hne : fr ≠ i)
    (hpo : σ.peerOrder = ord.map (fun x => sint.nat x)) (hon : ord ≠ []) :
    PrepWf i σ ord x := by
  have hid := pre_ids h (q := x.replica) (k := x.inst) rfl
  obtain ⟨S, hS, hi, hfr, -, hmem⟩ := pre_msgs h
  have hl := ((hS.1.2.2.2.2.2.1).2.2.2.1 fr i x hmem).1
  refine ⟨repWf_of_pre h hpo, ⟨hid.1, hid.2.1⟩, ⟨hid.2.2.1, hid.2.2.2⟩, ?_, ?_⟩
  · rw [hl, link_toN_W32 fr hfr]
    refine ⟨?_, hfr, hne⟩
    unfold zz; have : fr < 5 := hfr; rw [show sint.Z (W32 (fr : Int)) = (fr : Int) by word]; omega
  · exact deliver_outsWf h hpo hon

theorem accWf_of_pre {fr i n : Nat} {x : Accept} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n (.accept x) σ) (hne : fr ≠ i)
    (hpo : σ.peerOrder = ord.map (fun x => sint.nat x)) :
    AccWf i σ ord x := by
  have hid := pre_ids h (q := x.replica) (k := x.inst) rfl
  obtain ⟨S, hS, hi, hfr, -, hmem⟩ := pre_msgs h
  have hl := ((hS.1.2.2.2.2.2.1).2.2.2.2.2 fr i x hmem).1
  refine ⟨repWf_of_pre h hpo, ⟨hid.1, hid.2.1⟩, ⟨hid.2.2.1, hid.2.2.2⟩, ?_⟩
  rw [hl, link_toN_W32 fr hfr]
  refine ⟨?_, hfr, hne⟩
  unfold zz; have : fr < 5 := hfr; rw [show sint.Z (W32 (fr : Int)) = (fr : Int) by word]; omega

theorem accept_cmds_ne {fr i n : Nat} {x : Accept} {σ : RState}
    (h : deliverPre fr i n (.accept x) σ) : x.command ≠ [] := by
  obtain ⟨S, hS, -, -, -, hmem⟩ := pre_msgs h
  exact hS.accept_cmds_ne hmem

theorem noTPA_pre {fr i n : Nat} {x : TryPreAccept} {σ : RState}
    (h : deliverPre fr i n (.tryPreAccept x) σ) : False := by
  obtain ⟨S, hS, -, -, -, hmem⟩ := pre_msgs h
  exact (hS.1.2.2.2.1 _ _ _ hmem).1 x rfl

theorem noTPAR_pre {fr i n : Nat} {x : TryPreAcceptReply} {σ : RState}
    (h : deliverPre fr i n (.tryPreAcceptReply x) σ) : False := by
  obtain ⟨S, hS, -, -, -, hmem⟩ := pre_msgs h
  exact (hS.1.2.2.2.1 _ _ _ hmem).2 x rfl

/-- A recorded reply of a preparing bookkeeping is a report (`prepReport`) of its acceptor. -/
theorem prep_entry_report {S : Sys} (hS : Inv S) {i : Nat} (hi : i < nR) {x : InstId}
    {w : InstRec} {lb : LbRec} (hw : (S.rep i).inst x = some w) (hlb : w.lb = some lb)
    (hp : lb.preparing = true) {e : PReply} (he : e ∈ lb.prepareReplies) :
    (∃ a ev, S.prepReport a e.m ev ∧ Msg.prepareReply e.m ∈ S.msgs a i) ∨
    S.ev i (.selfReply e.m) := by
  have hl := (hS.1.2.2.2.2.2.2.2.2.2.2.1 i hi x w lb hw hlb).2.2.2.2.2.2.2.2 hp
  obtain ⟨-, -, hor⟩ := hl.2 e he
  rcases hor with ⟨-, ⟨n', hn', -⟩⟩ | ⟨-, hself⟩
  · left
    have hm' : Msg.prepareReply e.m ∈ S.msgs (toN e.m.acceptorId) i := by
      unfold Sys.msgs
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_of_getElem? hn'))
    exact ⟨_, _, ⟨hS.2.prSent _ _ _ hm', Or.inl ⟨i, hm', rfl⟩⟩, hm'⟩
  · exact Or.inr hself

theorem prWf_of_pre {fr i n : Nat} {x : PrepareReply} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n (.prepareReply x) σ) (hpo : σ.peerOrder = ord.map (fun x => sint.nat x))
    (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) (houts : OutsWf (hPrepareReply σ x).2) :
    ∃ w lb, PRWf i σ ord x w lb := by
  have hid := pre_ids h (q := x.replica) (k := x.inst) rfl
  obtain ⟨S, hS, hi, hfr, hσ, hmem⟩ := pre_msgs h
  obtain ⟨w, lb, hw, hlb⟩ := hS.1.2.2.1 fr i _ _ hmem rfl (Or.inl ⟨x, rfl⟩)
  have hrepx : S.prepReport fr x (.sent i (.prepareReply x)) :=
    ⟨hS.2.prSent _ _ _ hmem, Or.inl ⟨i, hmem, rfl⟩⟩
  have hrps := hS.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  refine ⟨w, lb, repWf_of_pre h hpo, ⟨hid.1, hid.2.1⟩, ⟨hid.2.2.1, hid.2.2.2⟩, by rw [← hσ]; exact hw,
    hlb, fun hp => (hS.2.prepNoProp i hi _ w lb hw hlb hp).2.2.2.1, ?_, ?_, ?_, hord, houts⟩
  · intro hp e he hst
    rcases List.mem_append.mp he with he | he
    · rcases prep_entry_report hS hi hw hlb hp he with ⟨a, ev, hr, -⟩ | hself
      · exact hrps.2.2.1 _ _ _ hr hst
      · exact hrps.2.2.1 _ _ _ ⟨hself, Or.inr rfl⟩ hst
    · simp only [List.mem_singleton] at he; subst he
      exact hrps.2.2.1 _ _ _ hrepx hst
  · intro hp e he hst
    rcases List.mem_append.mp he with he | he
    · rcases prep_entry_report hS hi hw hlb hp he with ⟨a, ev, -, hm'⟩ | hself
      · exact hS.2.cmdsNe.2.2.2.1 _ _ _ hm' hst
      · exact hS.2.cmdsNe.2.2.2.2.1 _ _ hself hst
    · simp only [List.mem_singleton] at he; subst he
      exact hS.2.cmdsNe.2.2.2.1 _ _ _ hmem hst
  · rw [← hσ]
    exact ⟨fun q k pr hpr => hS.1.1.2.2.2.1 i hi q k pr hpr, fun q hq => hS.2.classWf i hi q hq⟩

theorem paWf_of_pre {fr i n : Nat} {x : PreAccept} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n (.preAccept x) σ) (hne : fr ≠ i)
    (hpo : σ.peerOrder = ord.map (fun x => sint.nat x)) (hord : ∀ o ∈ ord, 0 ≤ sint.Z o)
    (houts : OutsWf (hPreAccept σ x).2) :
    PAWf i σ ord x := by
  have hid := pre_ids h (q := x.replica) (k := x.inst) rfl
  obtain ⟨S, hS, hi, hfr, hσ, hmem⟩ := pre_msgs h
  have hl := (hS.1.2.2.2.2.2.1.2.2.2.2.1 fr i x hmem).1
  refine ⟨repWf_of_pre h hpo, ⟨hid.1, hid.2.1⟩, ⟨hid.2.2.1, hid.2.2.2⟩, ?_, ?_,
    hS.preAccept_cmds_ne hmem, ?_, hord, houts⟩
  · rw [hl, link_toN_W32 fr hfr]
    refine ⟨hfr, hne, ?_⟩
    unfold zz; have : fr < 5 := hfr; rw [show sint.Z (W32 (fr : Int)) = (fr : Int) by word]; omega
  · exact (hS.1.2.1 fr i _ hmem).2 _ (by simp [Msg.depsFields])
  · rw [← hσ]
    exact ⟨fun q k pr hpr => hS.1.1.2.2.2.1 i hi q k pr hpr, fun q hq => hS.2.classWf i hi q hq⟩

/-- A decoded `PrepareReply` as the handler takes it (HANDLERS-4: `ownPReply` allows a `nil`
command slice for an empty list, so no `cs ≠ nil` is needed). -/
theorem ownPrepareReply_nn (l : Loc) (m : PrepareReply) :
    ownPrepareReply l m (DFrac.own 1) ⊢ ownPrepareReplyNN (GF := GF) l m := by
  unfold ownPrepareReply ownPrepareReplyNN
  exact .rfl

/-! ### The run loop's form -/

theorem handlePrepareReply_spec (hS : replica.Replica.SendMsg.spec (GF := GF))
    (hSQ : replica.Replica.SlowQuorumSize.spec (GF := GF)) (hNoop : state.NOOP.spec (GF := GF)) :
    HandlerSpec (GF := GF) .prepareReply go!"handlePrepareReply" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ _ hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  iintro %Φ ⟨#Hctx, Hrep, Hm, Hf, Houts⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  ihave %Hord := hdCtx_ord $$ Hctx'
  ihave %Hon := hdCtx_ordNe $$ Hctx'
  obtain ⟨w, lb, hw⟩ := prWf_of_pre hpre hpo Hord (deliver_outsWf hpre hpo Hon)
  simp only [hMsg, ownMsg]
  ihave Hm := ownPrepareReply_nn $$ Hm
  wp_apply (wp_handlePrepareReply hS hSQ hNoop γ i r rr L p Rext ord σ l x w lb hw)
    $$ [$Hctx' $Hrep $Hm $Hf $Houts] as Hpost
  unfold repDone at *; iapply HΦ $$ Hpost

theorem handlePreAccept_spec (hS : replica.Replica.SendMsg.spec (GF := GF)) (hP : dlog.Logger.Printf.spec (GF := GF)) :
    HandlerSpec (GF := GF) .preAccept go!"handlePreAccept" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ hne hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  iintro %Φ ⟨#Hctx, Hrep, Hm, Hf, Houts⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  ihave %Hord := hdCtx_ord $$ Hctx'
  ihave %Hon := hdCtx_ordNe $$ Hctx'
  simp only [hMsg, ownMsg]
  wp_apply (wp_handlePreAccept hS hP γ i r rr L p Rext ord σ l x
    (paWf_of_pre hpre hne hpo Hord (deliver_outsWf hpre hpo Hon)))
    $$ [$Hctx' $Hrep $Hm $Hf $Houts] as Hpost
  unfold repDone at *; iapply HΦ $$ Hpost

/-- `startRecoveryForInstance`'s outputs: two ghost events and a Prepare broadcast. -/
theorem recover_outsWf (σ : RState) (x : InstId) : OutsWf (hRecover σ x).2 := by
  unfold hRecover
  simp only []
  split
  · intro o ho; simp at ho
  split
  · intro o ho; simp at ho
  intro o ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl <;> simp [bcastPrepareOf, Msg.wf]

theorem recWf_of_pre {i : Nat} {σ : RState} {ord : List w32} {x : InstId}
    (h : ∃ S : Sys, Inv S ∧ i < nR ∧ S.rep i = σ) (hq : x.q < nR)
    (hx : (x.i : Int) ≤ zz (σ.crtInstance x.q))
    (hpo : σ.peerOrder = ord.map (fun x => sint.nat x)) (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) :
    RecWf i σ ord x := by
  obtain ⟨S, hS, hi, hσ⟩ := h
  have hc := hS.1.1.2.2.1 i hi x.q hq
  rw [hσ] at hc
  refine ⟨⟨by rw [← hσ]; exact hS.1.1.1 i hi, hi, hpo⟩, hq, ?_, hord, recover_outsWf σ x⟩
  have := hc.2
  simp only [toN, zz] at this hx ⊢
  omega

theorem recover_spec (hS : replica.Replica.SendMsg.spec (GF := GF)) (hP : dlog.Logger.Printf.spec (GF := GF)) :
    RecoverSpec (GF := GF) := by
  intro γ i r rr L p Rext ord σ x hpre hq hx hpo
  iintro %Φ ⟨#Hctx, Hrep, Hf, Houts⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  ihave %Hord := hdCtx_ord $$ Hctx'
  have hw : RecWf i σ ord x := recWf_of_pre hpre hq hx hpo Hord
  wp_apply (wp_startRecoveryForInstance hS hP γ i r rr L p Rext ord σ x hw)
    $$ [$Hctx' $Hrep $Hf $Houts] as Hpost
  unfold repDone at *; iapply HΦ $$ Hpost

theorem handlePrepare_spec (hS : replica.Replica.SendMsg.spec (GF := GF)) :
    HandlerSpec (GF := GF) .prepare go!"handlePrepare" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ hne hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  iintro %Φ ⟨#Hctx, Hrep, Hm, Hf, Houts⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  ihave %Hon := hdCtx_ordNe $$ Hctx'
  simp only [hMsg, ownMsg]
  wp_apply (wp_handlePrepare hS γ i r rr L p Rext ord σ l x (prepWf_of_pre hpre hne hpo Hon))
    $$ [$Hctx' $Hrep $Hm $Hf $Houts] as Hpost
  unfold repDone at *; iapply HΦ $$ Hpost

theorem handleAccept_spec (hS : replica.Replica.SendMsg.spec (GF := GF)) :
    HandlerSpec (GF := GF) .accept go!"handleAccept" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ hne hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  iintro %Φ ⟨#Hctx, Hrep, Hm, Hf, Houts⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  simp only [hMsg, ownMsg]
  unfold ownAccept
  icases Hm with ⟨%cs, %ds, Hm, Hcs, Hds⟩
  ihave %Hnn := ownCmds_nonnil _ _ _ (accept_cmds_ne hpre) $$ Hcs
  wp_apply (wp_handleAccept hS γ i r rr L p Rext ord σ l x (accWf_of_pre hpre hne hpo))
    $$ [$Hctx' $Hrep $Hf $Houts Hm Hcs Hds] as Hpost
  · unfold ownAcceptNN; iexists cs, ds; iframe; ipureintro; exact Hnn
  unfold repDone at *; iapply HΦ $$ Hpost

theorem handleTryPreAccept_spec : HandlerSpec (GF := GF) .tryPreAccept go!"handleTryPreAccept" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ _ hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  exact (noTPA_pre hpre).elim

theorem handleTryPreAcceptReply_spec :
    HandlerSpec (GF := GF) .tryPreAcceptReply go!"handleTryPreAcceptReply" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ _ hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  exact (noTPAR_pre hpre).elim

theorem nodup_len_le (l : List Nat) (hl : l.Nodup) (hb : ∀ a ∈ l, a < nR) : l.length ≤ nR := by
  have := (List.subperm_of_subset hl (fun a ha => List.mem_range.2 (hb a ha))).length_le
  simpa using this

theorem slt_zz (a b : w32) : a.slt b = true ↔ zz a < zz b := by
  simp only [zz, sint.Z]; exact BitVec.slt_iff_toInt_lt

theorem parWf_of_pre {fr i n : Nat} {x : PreAcceptReply} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n (.preAcceptReply x) σ) (hpo : σ.peerOrder = ord.map (fun x => sint.nat x))
    (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) (houts : OutsWf (hPreAcceptReply σ x).2) :
    ∃ w lb, PARWf i σ ord x w lb := by
  have hid := pre_ids h (q := x.replica) (k := x.inst) rfl
  obtain ⟨S, hS, hi, hfr, hσ, hmem⟩ := pre_msgs h
  obtain ⟨w, lb, hw, hlb⟩ := hS.1.2.2.1 fr i _ _ hmem rfl (Or.inr (Or.inl ⟨x, rfl⟩))
  have hL := hS.1.2.2.2.2.2.2.2.2.2.2.1 i hi _ w lb hw hlb
  have hrv := (hS.1.2.2.2.2.2.2.2.2.1.2.1 fr i x hmem).1
  obtain ⟨v, hv⟩ := hrv
  have hle : zz x.ballot ≤ zz lb.lastTriedBallot := hL.2.2.2.1 _ _ (Or.inl hv)
  have hst := hS.2.pm.parSt fr i x hmem
  refine ⟨w, lb, repWf_of_pre h hpo, ⟨hid.1, hid.2.1⟩, ⟨hid.2.2.1, hid.2.2.2⟩,
    by rw [← hσ]; exact hw, hlb, hord, houts, ?_, ?_, ?_, ?_, ?_⟩
  · intro hs
    have hne : lb.status ≠ stNONE := by
      rcases hs with h' | h' <;> rw [h'] <;> decide
    exact ((hS.1.1.2.1 i hi _ w hw).2.2.2.2.1 lb hlb hne).1
  · exact ((hS.1.2.1 fr i _ hmem).2 _ (by simp [Msg.depsFields])).1
  · intro h1 h2 hs h0
    have heq : x.ballot = lb.lastTriedBallot := by
      have a1 : ¬ zz lb.lastTriedBallot < zz x.ballot := fun h' => by
        rw [← slt_zz] at h'; rw [h1] at h'; cases h'
      have a2 : ¬ zz x.ballot < zz lb.lastTriedBallot := fun h' => by
        rw [← slt_zz] at h'; rw [h2] at h'; cases h'
      have : zz x.ballot = zz lb.lastTriedBallot := by omega
      simp only [zz] at this; word
    rw [heq] at hv
    have hb := hS.2.pm.paFresh i hi _ w lb hw hlb hs h0 ⟨v, hv⟩
    rw [slt_zz]; have := hst.2.1; omega
  · rcases h' : lb.lastTriedBallot.slt x.ballot
    · rfl
    · rw [slt_zz] at h'; omega
  · obtain ⟨Q, hnd, hlen, hQ⟩ := hL.2.2.2.2.2.1
    have hb : (Q.map (·.1)).length ≤ nR :=
      nodup_len_le _ hnd (fun a ha => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha; exact (hQ p.1 p.2 hp).1)
    simp only [List.length_map] at hb
    intro h0
    have := congrArg BitVec.toNat h0
    rw [BitVec.toNat_add] at this
    unfold nR at hb
    simp at this; omega

theorem arWf_of_pre {fr i n : Nat} {x : AcceptReply} {σ : RState} {ord : List w32}
    (h : deliverPre fr i n (.acceptReply x) σ) (hpo : σ.peerOrder = ord.map (fun x => sint.nat x))
    (hord : ∀ o ∈ ord, 0 ≤ sint.Z o) (houts : OutsWf (hAcceptReply σ x).2) :
    ∃ w lb, ARWf i σ ord x w lb := by
  have hid := pre_ids h (q := x.replica) (k := x.inst) rfl
  obtain ⟨S, hS, hi, hfr, hσ, hmem⟩ := pre_msgs h
  obtain ⟨w, lb, hw, hlb⟩ := hS.1.2.2.1 fr i _ _ hmem rfl (Or.inr (Or.inr ⟨x, rfl⟩))
  exact ⟨w, lb, repWf_of_pre h hpo, ⟨hid.1, hid.2.1⟩, ⟨hid.2.2.1, hid.2.2.2⟩,
    by rw [← hσ]; exact hw, hlb, hord, houts⟩

theorem handlePreAcceptReply_spec (hS : replica.Replica.SendMsg.spec (GF := GF)) :
    HandlerSpec (GF := GF) .preAcceptReply go!"handlePreAcceptReply" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ _ hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  iintro %Φ ⟨#Hctx, Hrep, Hm, Hf, Houts⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  ihave %Hord := hdCtx_ord $$ Hctx'
  ihave %Hon := hdCtx_ordNe $$ Hctx'
  obtain ⟨w, lb, hw⟩ := parWf_of_pre hpre hpo Hord (deliver_outsWf hpre hpo Hon)
  simp only [hMsg, ownMsg]
  wp_apply (wp_handlePreAcceptReply hS γ i r rr L p Rext ord σ l x w lb hw)
    $$ [$Hctx' $Hrep $Hm $Hf $Houts] as Hpost
  unfold repDone at *; iapply HΦ $$ Hpost

theorem handleAcceptReply_spec (hS : replica.Replica.SendMsg.spec (GF := GF)) :
    HandlerSpec (GF := GF) .acceptReply go!"handleAcceptReply" := by
  intro γ i r rr L p Rext ord σ l m fr n hpre hk _ _ hpo
  rcases m with x | x | x | x | x | x | x | x | x | x | x <;> simp [Msg.kind] at hk
  iintro %Φ ⟨#Hctx, Hrep, Hm, Hf, Houts⟩ HΦ
  ihave #Hctx' := hdCtx_of_hctx $$ Hctx
  ihave %Hord := hdCtx_ord $$ Hctx'
  ihave %Hon := hdCtx_ordNe $$ Hctx'
  obtain ⟨w, lb, hw⟩ := arWf_of_pre hpre hpo Hord (deliver_outsWf hpre hpo Hon)
  simp only [hMsg, ownMsg]
  wp_apply (wp_handleAcceptReply hS γ i r rr L p Rext ord σ l x w lb hw)
    $$ [$Hctx' $Hrep $Hm $Hf $Houts] as Hpost
  unfold repDone at *; iapply HΦ $$ Hpost

/-- The handlers' specs in the run loop's form. -/
theorem handlerSpecs_of (hS : replica.Replica.SendMsg.spec (GF := GF))
    (hSQ : replica.Replica.SlowQuorumSize.spec (GF := GF)) (hNoop : state.NOOP.spec (GF := GF))
    (hP : dlog.Logger.Printf.spec (GF := GF)) (hprop : ProposeSpec (GF := GF)) : HandlerSpecs (GF := GF) where
  prepare := handlePrepare_spec hS
  preAccept := handlePreAccept_spec hS hP
  accept := handleAccept_spec hS
  prepareReply := handlePrepareReply_spec hS hSQ hNoop
  preAcceptReply := handlePreAcceptReply_spec hS
  acceptReply := handleAcceptReply_spec hS
  tryPreAccept := handleTryPreAccept_spec
  tryPreAcceptReply := handleTryPreAcceptReply_spec
  propose := hprop
  recover := recover_spec hS hP

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
