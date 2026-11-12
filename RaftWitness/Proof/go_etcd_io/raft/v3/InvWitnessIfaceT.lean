/-
The witness proxy with the terms within a bound (2026-10-20, witness support, W4,
`notes/raft-witness.md`): `witness.Process` at W2's ghost state (`InvWitnessIface.lean`) with the
storage's states' terms, the cache's and a request's (but a pre-vote's) within a persistent bound
`T`, so an answer's (but a pre-vote answer's): every state a round writes and every such answer is
of the stored term or the request's (`wStep_termP`). The kv example takes `T` the cluster's term
budget (`termLB`): the witness's answers it steps into its node are within it, as `Node.Step` asks.
-/
module

public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitnessIface
public import RaftWitness.Proof.go_etcd_io.raft.v3.InvWitnessOut

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section model
open GMap
variable [GooseExts]

/-- `t` is the state's term, or the request's when it is no pre-vote. -/
def TermOfP (σ : WHS) (μ : WMsg) (t : w64) : Prop :=
  t = σ.term ∨ (μ.ty ≠ MsgPreVote ∧ t = μ.term)

/-- An answer that is no `MsgPreVoteResp` is of one of the two terms. -/
def RespTermOfP (σ : WHS) (μ : WMsg) : Option WResp → Prop
  | none => True
  | some r => r.1.Type' ≠ MsgPreVoteResp → TermOfP σ μ r.1.Term'

theorem wOlder_termP (id : w64) (cq pv : Bool) (σ : WHS) (μ : WMsg) :
    RespTermOfP σ μ (wOlder id cq pv σ μ) := by
  unfold wOlder
  split
  · intro _; exact .inl rfl
  · split
    · intro _; exact .inl rfl
    · trivial

theorem wAppendNoUpdate_term (id : w64) (σ : WHS) (μ : WMsg) :
    (wAppendNoUpdate id σ μ).1.1.Term' = σ.term := by
  unfold wAppendNoUpdate
  split
  · rfl
  · split <;> rfl

theorem wNoUpdate_termP (id : w64) (cq pv hh : Bool) (σ : WHS) (μ : WMsg) (r : Option WResp)
    (h : wNoUpdate id cq pv hh σ μ = some r) : RespTermOfP σ μ r := by
  unfold wNoUpdate at h
  split at h
  · cases h; trivial
  split at h
  · cases h; exact wOlder_termP id cq pv σ μ
  split at h
  · simp only at h
    split at h
    · cases h
      intro _; exact .inl (wAppendNoUpdate_term id σ μ)
    · cases h
  · cases h

theorem wNewer_termP (σ : WHS) (μ : WMsg) : TermOfP σ μ (wNewer σ μ).term := by
  unfold wNewer
  split
  · exact .inl rfl
  · rename_i h
    split
    · exact .inr ⟨h, rfl⟩
    · exact .inr ⟨h, rfl⟩

theorem wVote_term_aux (rj : Bool) (P : Prop) [Decidable P] (st : WHS) (x t : w64) :
    (if rj = true then (if P ∧ rj = false then { st with vote := x } else st).term else t) = st.term ∨
    (if rj = true then (if P ∧ rj = false then { st with vote := x } else st).term else t) = t := by
  cases rj
  · right; simp
  · left; simp

theorem wVote_term (id : w64) (st : WHS) (μ : WMsg) :
    (wVote id st μ).1.term = st.term ∧
    ((wVote id st μ).2.1.Term' = st.term ∨ (wVote id st μ).2.1.Term' = μ.term) := by
  unfold wVote
  simp only [respM]
  constructor
  · rw [apply_ite WHS.term]; simp
  · exact wVote_term_aux _ _ _ _ _

theorem wVote_type (id : w64) (st : WHS) (μ : WMsg) (h : μ.ty = MsgPreVote) :
    (wVote id st μ).2.1.Type' = MsgPreVoteResp := by
  unfold wVote; simp only [respM, h, ↓reduceIte]

theorem wAppend_term (id : w64) (σ st : WHS) (μ : WMsg) (Hst : TermOfP σ μ st.term) :
    TermOfP σ μ (wAppend id σ st μ).1.term ∧ TermOfP σ μ (wAppend id σ st μ).2.1.Term' := by
  unfold wAppend
  simp only
  split
  · exact ⟨Hst, .inl (wAppendNoUpdate_term id σ μ)⟩
  · exact ⟨Hst, Hst⟩

/-- One round's new state, and its answer if no pre-vote's, are of the two terms. -/
theorem wStep_termP (id : w64) (cq pv : Bool) (σ : WHS) (μ : WMsg) :
    (∀ σ', (wStep id cq pv σ μ).1 = some σ' → TermOfP σ μ σ'.term) ∧
    RespTermOfP σ μ (wStep id cq pv σ μ).2 := by
  unfold wStep
  by_cases h1 : μ.ty = MsgHeartbeat ∧ μ.term = σ.term
  · rw [if_pos h1]; exact ⟨(fun _ h => by cases h), fun _ => .inl rfl⟩
  rw [if_neg h1]
  cases hr : wNoUpdate id cq pv true σ μ with
  | some r => exact ⟨(fun _ h => by cases h), wNoUpdate_termP id cq pv true σ μ r hr⟩
  | none =>
    simp only
    have Hst : TermOfP σ μ (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ).term := by
      split
      · exact wNewer_termP σ μ
      · exact .inl rfl
    generalize (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) = st at Hst ⊢
    by_cases h2 : μ.ty = MsgHeartbeat
    · rw [if_pos h2]; exact ⟨(fun _ h => by cases h; exact Hst), fun _ => Hst⟩
    rw [if_neg h2]
    by_cases h3 : μ.ty = MsgApp
    · rw [if_pos h3]
      obtain ⟨Ha, Hb⟩ := wAppend_term id σ st μ Hst
      exact ⟨(fun _ h => by cases h; exact Ha), fun _ => Hb⟩
    rw [if_neg h3]
    obtain ⟨Ha, Hb⟩ := wVote_term id st μ
    refine ⟨(fun _ h => by cases h; rw [Ha]; exact Hst), ?_⟩
    intro Hnp
    rcases Hb with Hb | Hb
    · show TermOfP σ μ (wVote id st μ).2.1.Term'
      rw [Hb]; exact Hst
    · have hnp : μ.ty ≠ MsgPreVote := fun h => Hnp (wVote_type id st μ h)
      exact .inr ⟨hnp, Hb⟩

/-- An answer that is no `MsgPreVoteResp` is to the request's sender, from the witness `id`, an
append's, a heartbeat's or a vote's response. -/
def RespAddr (μ : WMsg) (id : w64) : Option WResp → Prop
  | none => True
  | some r => r.1.Type' ≠ MsgPreVoteResp → r.1.To' = μ.frm ∧ r.1.From' = id ∧
      (r.1.Type' = MsgAppResp ∨ r.1.Type' = MsgHeartbeatResp ∨ r.1.Type' = MsgVoteResp)

theorem wAppendNoUpdate_addr (id : w64) (σ : WHS) (μ : WMsg) :
    (wAppendNoUpdate id σ μ).1.1.To' = μ.frm ∧ (wAppendNoUpdate id σ μ).1.1.From' = id ∧
      (wAppendNoUpdate id σ μ).1.1.Type' = MsgAppResp := by
  unfold wAppendNoUpdate
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> exact ⟨rfl, rfl, rfl⟩

theorem wNoUpdate_addr (id : w64) (cq pv hh : Bool) (σ : WHS) (μ : WMsg) (r : Option WResp)
    (h : wNoUpdate id cq pv hh σ μ = some r) : RespAddr μ id r := by
  unfold wNoUpdate at h
  split at h
  · cases h; trivial
  split at h
  · cases h
    unfold wOlder
    split
    · intro _; exact ⟨rfl, rfl, .inl rfl⟩
    · split
      · intro h; exact absurd rfl h
      · trivial
  split at h
  · simp only at h
    split at h
    · cases h
      intro _
      obtain ⟨h1, h2, h3⟩ := wAppendNoUpdate_addr id σ μ
      exact ⟨h1, h2, .inl h3⟩
    · cases h
  · cases h

/-- One round's answer, if no pre-vote's, is to the sender, from the witness. -/
theorem wStep_addr (id : w64) (cq pv : Bool) (σ : WHS) (μ : WMsg) :
    RespAddr μ id (wStep id cq pv σ μ).2 := by
  unfold wStep
  by_cases h1 : μ.ty = MsgHeartbeat ∧ μ.term = σ.term
  · rw [if_pos h1]; intro _; exact ⟨rfl, rfl, .inr (.inl rfl)⟩
  rw [if_neg h1]
  cases hr : wNoUpdate id cq pv true σ μ with
  | some r => exact wNoUpdate_addr id cq pv true σ μ r hr
  | none =>
    simp only
    generalize (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) = st
    by_cases h2 : μ.ty = MsgHeartbeat
    · rw [if_pos h2]; intro _; exact ⟨rfl, rfl, .inr (.inl rfl)⟩
    rw [if_neg h2]
    by_cases h3 : μ.ty = MsgApp
    · rw [if_pos h3]
      intro _
      unfold wAppend
      simp only
      split
      · obtain ⟨a1, a2, a3⟩ := wAppendNoUpdate_addr id σ μ
        exact ⟨a1, a2, .inl a3⟩
      · exact ⟨rfl, rfl, .inl rfl⟩
    rw [if_neg h3]
    intro hnp
    refine ⟨rfl, rfl, .inr (.inr ?_)⟩
    by_cases h4 : μ.ty = MsgPreVote
    · exact absurd (wVote_type id st μ h4) hnp
    · unfold wVote; simp only [respM, h4, ↓reduceIte]

end model

section ifaceT
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- An answer's term within `T`, but a pre-vote answer's. -/
def wRespTerm (T : w64 → IProp GF) : Option WResp → IProp GF
  | none => iprop(True)
  | some r => if r.1.Type' = MsgPreVoteResp then iprop(True) else T r.1.Term'

instance wRespTerm_persistent (T : w64 → IProp GF) [∀ t, Persistent (T t)] (r : Option WResp) :
    Persistent (wRespTerm T r) := by
  unfold wRespTerm; split
  · infer_instance
  · split <;> infer_instance

/-- A request's term within `T`, but a pre-vote's. -/
def wReqTerm (T : w64 → IProp GF) (μ : WMsg) : IProp GF :=
  if μ.ty = MsgPreVote then iprop(True) else T μ.term

instance wReqTerm_persistent (T : w64 → IProp GF) [∀ t, Persistent (T t)] (μ : WMsg) :
    Persistent (wReqTerm T μ) := by
  unfold wReqTerm; split <;> infer_instance

theorem termOfP_T (T : w64 → IProp GF) [∀ t, Persistent (T t)] (σ : WHS) (μ : WMsg) (t : w64)
    (H : TermOfP σ μ t) : ⊢ T σ.term -∗ wReqTerm T μ -∗ T t := by
  iintro #Hs #Hr
  rcases H with rfl | ⟨Hnp, rfl⟩
  · iexact Hs
  · unfold wReqTerm; rw [if_neg Hnp]; iexact Hr

theorem respTermOfP_T (T : w64 → IProp GF) [∀ t, Persistent (T t)] (σ : WHS) (μ : WMsg)
    (r : Option WResp) (H : RespTermOfP σ μ r) :
    ⊢ T σ.term -∗ wReqTerm T μ -∗ wRespTerm T r := by
  iintro #Hs #Hr
  cases r with
  | none => unfold wRespTerm; itrivial
  | some r =>
    simp only [wRespTerm]
    by_cases h : r.1.Type' = MsgPreVoteResp
    · rw [if_pos h]; itrivial
    · rw [if_neg h]
      iapply termOfP_T T σ μ _ (H h) $$ Hs Hr

/-- `witness.Process.ghostSpec` with the terms within a bound `T` (2026-10-20, witness support):
the storage's states' terms (`P`) and the cache's within it, and a request's (but a pre-vote's),
so an answer's (but a pre-vote answer's): the kv example's term budget (`termLB`). -/
abbrev witness.Process.ghostSpecT : Prop :=
  ∀ (γ : RaftNames) (T : w64 → IProp GF) [∀ t, Persistent (T t)] (w : Loc) (s : GoInterface)
    (cq pv : Bool) (c : WHS) (h : Bool) (N : Namespace) (mv : WitnessMessage) (μ : WMsg),
  (↑raftLogN : CoPset) ⊆ ⊤ \ ↑N → γ.reWit ≠ W64 0 → μ.to = γ.reWit → μ.frm ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownWitness w γ.reWit s cq pv c h ∗
      isWitnessStorage s N (fun σ => iprop(wGhost γ σ.ws ∗ T σ.term)) ∗
      ownWMsg mv μ ∗ wSt γ c.ws ∗ T c.term ∗ raftCommitInv γ ∗ isMessage γ (wAbsReq μ) ∗
      wReqTerm T μ }}
    (App (Val (w @!! go.GoType.PointerType witness.ty @!! go!"Process")) (Val #mv))
  {{ (ml : Loc) (err : GoError), RET (PairV #ml #err);
      ∃ c' h', ownWitness w γ.reWit s cq pv c' h' ∗ wSt γ c'.ws ∗ T c'.term ∗
      ((⌜err = interface.nil⌝ ∗ ∃ r, respOpt ml r ∗ wRespOk γ r ∗ wRespTerm T r ∗
          ⌜RespAddr μ γ.reWit r⌝) ∨
       (⌜err ≠ interface.nil⌝ ∗ ⌜ml = null⌝)) }}

theorem witness.Process.ghostT (wp_Process : witness.Process.spec (GF := GF) (hG := hG)) :
    witness.Process.ghostSpecT (GF := GF) (hG := hG) := by
  intro γ T _ w s cq pv c h N mv μ HN Hwnz Hto Hfr
  iintro %Φ ⟨#Hpkg, Hw, #Hs, #Hm, #Hc, #HTc, #Hinv, #Hreq, #HTr⟩ HΦ
  wp_apply wp_Process w γ.reWit s cq pv c h N (fun σ => iprop(wGhost γ σ.ws ∗ T σ.term))
    (fun σ => iprop(wSt γ σ.ws ∗ T σ.term))
    (fun r => iprop(wRespOk γ r ∗ wRespTerm T r ∗ ⌜RespAddr μ γ.reWit r⌝)) mv μ
    (fun _ => inferInstance) $$ [$Hw] as %ml %err ⟨%c', %h', Hw, ⟨#Hc', #HTc'⟩, Hr⟩
  · iframe Hs Hm
    isplitr
    · iframe Hc HTc
    isplitr
    · imodintro
      iintro %σ %hh %r ⟨#Hst, #HTs⟩ %Hr
      isplitr
      · iapply wInst_cache γ γ.reWit cq pv μ rfl Hwnz Hto σ hh r Hr $$ Hreq Hst
      isplitr
      · iapply respTermOfP_T T σ μ r (wNoUpdate_termP γ.reWit cq pv hh σ μ r Hr) $$ HTs HTr
      · ipureintro; exact wNoUpdate_addr γ.reWit cq pv hh σ μ r Hr
    isplitr
    · imodintro
      iintro %σ %Hty4 ⟨Hg, #HTs⟩
      imod wInst_read γ N HN cq pv μ Hwnz Hto Hfr Hty4 σ $$ Hinv Hreq Hg with ⟨Hg, #Hst, Hobl⟩
      iframe Hg HTs Hst
      have Hterm := wStep_termP γ.reWit cq pv σ μ
      have Haddr := wStep_addr γ.reWit cq pv σ μ
      unfold wObl
      revert Hterm Haddr
      cases wStep γ.reWit cq pv σ μ with
      | mk o r =>
        intro Hterm Haddr
        cases o with
        | none =>
          simp only
          imodintro
          iframe Hobl
          isplitr
          · iapply respTermOfP_T T σ μ r Hterm.2 $$ HTs HTr
          · ipureintro; exact Haddr
        | some σ' =>
          simp only
          imodintro
          iintro ⟨Hg, -⟩
          imod Hobl $$ Hg with ⟨Hg, #Hst', #Hr'⟩
          ihave #HT' := termOfP_T T σ μ σ'.term (Hterm.1 σ' rfl) $$ HTs HTr
          imodintro
          iframe Hg HT' Hst' Hr'
          isplitr
          · iapply respTermOfP_T T σ μ r Hterm.2 $$ HTs HTr
          · ipureintro; exact Haddr
    imodintro
    isplitr
    · unfold wRespOk; itrivial
    isplitr
    · unfold wRespTerm; itrivial
    · ipureintro; trivial
  iapply HΦ
  iexists c', h'
  iframe Hw Hc' HTc'
  icases Hr with (⟨%He, %r, Hro, #Hok, #Ht, %Ha⟩ | ⟨%He, %Hn⟩)
  · ileft
    isplitr; · ipureintro; exact He
    iexists r
    iframe Hro Hok Ht
    ipureintro; exact Ha
  · iright
    ipureintro; exact ⟨He, Hn⟩

/-- `ownWitnessI` with the terms within `T` (`witness.Process.ghostSpecT`'s storage and cache). -/
def ownWitnessIT (γ : RaftNames) (N : Namespace) (T : w64 → IProp GF) (wi : GoInterface) :
    IProp GF :=
  iprop(∃ (w : Loc) (s : GoInterface) (cq pv : Bool) (c : WHS) (h : Bool),
    ⌜wi = interface.mkOk (go.GoType.PointerType witness.ty) #w⌝ ∗
    ownWitness w γ.reWit s cq pv c h ∗
    isWitnessStorage s N (fun σ => iprop(wGhost γ σ.ws ∗ T σ.term)) ∗
    wSt γ c.ws ∗ T c.term)

theorem ownWitnessIT_intro (γ : RaftNames) (N : Namespace) (T : w64 → IProp GF)
    [∀ t, Persistent (T t)] (w : Loc) (s : GoInterface) (cq pv : Bool) (c : WHS) (h : Bool) :
    ⊢ ownWitness (GF := GF) w γ.reWit s cq pv c h -∗
      isWitnessStorage s N (fun σ => iprop(wGhost γ σ.ws ∗ T σ.term)) -∗ wSt γ c.ws -∗ T c.term -∗
      ownWitnessIT γ N T (interface.mkOk (go.GoType.PointerType witness.ty) #w) := by
  iintro Hw #Hs #Hc #Ht
  unfold ownWitnessIT
  iexists w, s, cq, pv, c, h
  iframe Hw Hs Hc Ht
  ipureintro; rfl

/-- `Witness.Process` on the `Witness` of the witness `γ.reWit`, the terms within `T`. -/
abbrev Witness.Process.specT : Prop :=
  ∀ (γ : RaftNames) (N : Namespace) (T : w64 → IProp GF) [∀ t, Persistent (T t)]
    (i : GoInterfaceOk) (mv : WitnessMessage) (μ : WMsg),
  (↑raftLogN : CoPset) ⊆ ⊤ \ ↑N → γ.reWit ≠ W64 0 → μ.to = γ.reWit → μ.frm ≠ W64 0 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.raft.v3 ∗
      ownWitnessIT γ N T (interface.ok i) ∗ ownWMsg mv μ ∗ raftCommitInv γ ∗
      isMessage γ (wAbsReq μ) ∗ wReqTerm T μ }}
    (App (Val #(methods i.ty go!"Process" i.v)) (Val #mv))
  {{ (ml : Loc) (err : GoError), RET (PairV #ml #err);
      ownWitnessIT γ N T (interface.ok i) ∗
      ((⌜err = interface.nil⌝ ∗ ∃ r, respOpt ml r ∗ wRespOk γ r ∗ wRespTerm T r ∗
          ⌜RespAddr μ γ.reWit r⌝) ∨
       (⌜err ≠ interface.nil⌝ ∗ ⌜ml = null⌝)) }}

theorem Witness.wp_ProcessT (wp_Process : witness.Process.spec (GF := GF) (hG := hG)) :
    Witness.Process.specT (GF := GF) (hG := hG) := by
  intro γ N T _ i mv μ HN Hwnz Hto Hfr
  iintro %Φ ⟨#Hpkg, Hw, #Hm, #Hinv, #Hreq, #HTr⟩ HΦ
  iunfold ownWitnessIT at Hw
  icases Hw with ⟨%w, %s, %cq, %pv, %c, %h, %Hwi, Hw, #Hs, #Hc, #Ht⟩
  rcases i with ⟨ity, iv⟩
  simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq] at Hwi
  obtain ⟨rfl, rfl⟩ := Hwi
  wp_apply witness.Process.ghostT wp_Process γ T w s cq pv c h N mv μ HN Hwnz Hto Hfr
    $$ [$Hw] as %ml %err ⟨%c', %h', Hw, #Hc', #Ht', Hr⟩
  · iframe Hs Hm Hc Ht Hinv Hreq HTr
  iapply HΦ
  iframe Hr
  unfold ownWitnessIT
  iexists w, s, cq, pv, c', h'
  iframe Hw Hs Hc' Ht'
  ipureintro; rfl

/-- A queued request's reading on the outbox (`wAbs`) is legitimate, so is the witness's
reading of it (`wAbsReq`): the two agree on the four request types, and any other reads as a
pre-vote for the witness, which carries nothing. -/
theorem isMessage_wAbsReq (γ : RaftNames) (μ : WMsg) :
    isMessage (GF := GF) γ (wAbs μ) ⊢ isMessage γ (wAbsReq μ) := by
  unfold wAbs wAbsReq
  by_cases h1 : μ.ty = MsgApp
  · rw [if_pos h1, if_pos h1]; try exact .rfl
  rw [if_neg h1, if_neg h1]
  by_cases h2 : μ.ty = MsgVote
  · rw [if_pos h2, if_pos h2]; try exact .rfl
  rw [if_neg h2, if_neg h2]
  by_cases h3 : μ.ty = MsgHeartbeat
  · have h4 : ¬ μ.ty = MsgPreVote := by rw [h3]; simp [MsgPreVote, MsgHeartbeat]
    rw [if_neg h4, if_pos h3]; try exact .rfl
  rw [if_neg h3]
  by_cases h4 : μ.ty = MsgPreVote
  · rw [if_pos h4]; try exact .rfl
  · iintro -
    unfold isMessage
    simp only [Msg.mkV]
    itrivial

end ifaceT

end EtcdGrove
end Perennial
