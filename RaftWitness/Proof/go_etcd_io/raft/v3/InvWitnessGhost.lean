/-
The witness proxy over the witness's ghost state (2026-10-20, witness support, W3b,
`notes/raft-witness.md`): `witness.Process` (`Spec/go_etcd_io/raft/v3/witness__Process.lean`,
stated for any reading `P` of the storage's states) at W2's `wGhost` (`Protocol/Witness.lean`):
a request whose protocol reading (`wAbsReq`) is a legitimate message is answered, if at all,
with a legitimate message (`wRespOk`: its reading carries `isMessage`).

The storage's states are read as W2's `WState`s (`WHS.ws`: the term, vote, last entry and
replication set; the commit index, the leader and the outgoing set no safety argument reads);
the cache is a state of W2's history (`wSt`). Each round of `Process` (`wStep`) is one of W2's
lemmas: the heartbeat at the stored term (`wGhost_heartbeat`), the answers without a write from
a state of the history (`wSt_app_noupd`; an older term's carries nothing), and at the
compare-and-swap the term raised (`wGhost_raise`), the entry written (`wGhost_write`) or the
vote granted (`wGhost_vote`).
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.witness__Process
public import RaftWitness.Proof.go_etcd_io.raft.v3.Protocol.Witness

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI GMap go_etcd_io.raft.v3

section model
variable [FfiSyntax]

/-- A storage state as the protocol reads it. -/
def WHS.ws (σ : WHS) : WState := ⟨σ.term, σ.vote, σ.lt, σ.ls, σ.li, σ.rs⟩

/-- A request to the witness as the protocol reads it: a leader's append (`wapp`: its entry
`(lt, ls)` at `li`, the replication set's voters), a candidate's vote request (`wvote`: its last
entry, the responders so far) or pre-vote (`wprevote`), a leader's heartbeat (its context).
A request of another type (which `Process` ignores) reads as a pre-vote, which carries
nothing. -/
def wAbsReq (μ : WMsg) : Msg :=
  if μ.ty = MsgApp then Msg.mkV .wapp μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] μ.rs0 []
  else if μ.ty = MsgVote then
    Msg.mkV .wvote μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] (elements (domSet μ.votes)) []
  else if μ.ty = MsgHeartbeat then
    Msg.mkV .heartbeat μ.frm μ.to μ.term false (W64 0) (W64 0) (W64 0) (W64 0) [] [] μ.ctx
  else Msg.mkV .wprevote μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] [] []

end model

/-- The responders of a tally among a replication set without repetition, counted over it
(`votesInSet`), are all of them: every responder is in the set. -/
theorem votesInSet_all [FfiSyntax] (rs : List w64) (votes : GMap w64 Bool) (hnd : rs.Nodup)
    (h : votesInSet rs votes = GMap.size votes) : ∀ v, v ∈ domSet votes → v ∈ rs := by
  intro v hv
  refine Classical.byContradiction (fun hvr => ?_)
  let L := rs.filter (fun x => (votes !! x).isSome)
  have hLnd : L.Nodup := hnd.filter _
  have hsub : listToSet L ⊆ domSet votes \ {[v]} := by
    rw [elem_of_subseteq]
    intro x hx
    rw [elem_of_list_to_set] at hx
    have hx' := List.mem_filter.mp hx
    rw [elem_of_difference, elem_of_singleton]
    refine ⟨?_, fun e => hvr (e ▸ hx'.1)⟩
    rw [elem_of_dom]
    obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (by simpa using hx'.2)
    exact ⟨b, hb⟩
  have h1 := subseteq_size hsub
  rw [size_list_to_set L hLnd, size_difference (by
    rw [elem_of_subseteq]; intro x hx; rw [elem_of_singleton] at hx; subst hx; exact hv),
    size_singleton, size_dom] at h1
  have hL : L.length = GMap.size votes := h
  have hpos : 0 < GMap.size votes := by
    rw [← size_dom]
    rcases Nat.eq_zero_or_pos (size (domSet votes)) with h0 | h0
    · exfalso
      have := subseteq_size (show ({[v]} : GSet w64) ⊆ domSet votes from by
        rw [singleton_subseteq_l]; exact hv)
      rw [size_singleton] at this; omega
    · exact h0
  omega

section ghost
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, so that the heap's invariants are an `InvGS GF` (`raft__Step.lean`)
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- An answer of the witness is a legitimate message: its protocol reading (`absMsg`, at its
type) carries `isMessage`; none is legitimate. -/
def wRespOk (γ : RaftNames) : Option WResp → IProp GF
  | none => iprop(True)
  | some r => iprop(∀ ty, ⌜mtypeOf r.1.Type' = some ty⌝ -∗ isMessage γ (absMsg ty r.1 [] r.2))

instance wRespOk_persistent (γ : RaftNames) (r : Option WResp) :
    Persistent (wRespOk (GF := GF) γ r) := by
  unfold wRespOk; split <;> infer_instance

/-- An answer of a known type is legitimate when its reading is. -/
theorem wRespOk_of (γ : RaftNames) (m : MessageM) (ctx : List w8) (ty0 : MsgType)
    (Hty : mtypeOf m.Type' = some ty0) :
    isMessage (GF := GF) γ (absMsg ty0 m [] ctx) ⊢ wRespOk γ (some (m, ctx)) := by
  iintro #H
  unfold wRespOk
  iintro %ty %Hty'
  rw [Hty] at Hty'
  cases Hty'
  iexact H

end ghost

/-- `(lt, ls)` below `(lt', ls')` and not equal to it, strictly or not. -/
theorem ltPair_iff_LexLe (a b c d : w64) (hne : ¬ (a = c ∧ b = d)) :
    ltPair a b c d ↔ LexLe a b c d := by
  unfold ltPair LexLe
  constructor
  · rintro (h | ⟨h1, h2⟩)
    · left; exact h
    · right; exact ⟨h1, Int.le_of_lt h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · left; exact h
    · right
      refine ⟨h1, ?_⟩
      have : b ≠ d := fun e => hne ⟨h1, e⟩
      have : uint.Z b ≠ uint.Z d := fun e => this (uint_Z_inj.mp e)
      omega

/-- `handleAppendNoUpdate`'s answer, when it handles the request, is W2's `wAppNoUpd`'s. -/
theorem wAppNoUpd_of [FfiSyntax] (id : w64) (σ : WHS) (μ : WMsg) (Hty : μ.ty = MsgApp)
    (Hh : (wAppendNoUpdate id σ μ).2 = true) :
    (wAppendNoUpdate id σ μ).1.2 = [] ∧ (wAppendNoUpdate id σ μ).1.1.Type' = MsgAppResp ∧
    wAppNoUpd id σ.ws (wAbsReq μ) =
      some (absMsg .appResp (wAppendNoUpdate id σ μ).1.1 [] (wAppendNoUpdate id σ μ).1.2) := by
  have Hreq : wAbsReq μ = Msg.mkV .wapp μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] μ.rs0 [] := by
    unfold wAbsReq; rw [if_pos Hty]
  unfold wAppendNoUpdate at Hh ⊢
  rw [Hreq]
  unfold wAppNoUpd
  by_cases He : μ.lt = σ.lt ∧ μ.ls = σ.ls
  · simp only [He, and_self, ↓reduceIte, WHS.ws]
    refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
  · rw [if_neg He] at Hh ⊢
    by_cases Hl : ltPair μ.lt μ.ls σ.lt σ.ls
    · rw [if_pos Hl]
      have He' : ¬ (μ.lt = σ.ws.lt ∧ μ.ls = σ.ws.ls) := He
      have Hl' : LexLe μ.lt μ.ls σ.ws.lt σ.ws.ls := (ltPair_iff_LexLe _ _ _ _ He).mp Hl
      simp only [Msg.sub, He', Hl', ↓reduceIte]
      refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl
    · rw [if_neg Hl] at Hh; cases Hh

section ghost2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
-- `hlc := HasLC.hasLC`, so that the heap's invariants are an `InvGS GF` (`raft__Step.lean`)
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- An older term's `MsgAppResp`, of index `0`, carries nothing. -/
theorem wRespOk_appResp0 (γ : RaftNames) (to frm term : w64) :
    ⊢ wRespOk (GF := GF) γ (some (respM MsgAppResp to frm term (W64 0) false, [])) := by
  iapply wRespOk_of γ _ [] .appResp rfl
  simp only [isMessage, absMsg, absMsgFrom, respM, Bool.false_eq_true, ↓reduceIte]
  isplitr
  · unfold isAcked; ileft; ipureintro; rfl
  · unfold ackIn; ileft; ipureintro; rfl

/-- A pre-vote's answer carries nothing. -/
theorem wRespOk_preVoteResp (γ : RaftNames) (to frm term idx : w64) (rj : Bool) :
    ⊢ wRespOk (GF := GF) γ (some (respM MsgPreVoteResp to frm term idx rj, [])) := by
  iapply wRespOk_of γ _ [] .preVoteResp rfl
  simp only [isMessage, absMsg, absMsgFrom, respM]
  itrivial

/-- A rejection of a vote carries nothing. -/
theorem wRespOk_voteReject (γ : RaftNames) (to frm term idx : w64) :
    ⊢ wRespOk (GF := GF) γ (some (respM MsgVoteResp to frm term idx true, [])) := by
  iapply wRespOk_of γ _ [] .voteResp rfl
  simp only [isMessage, absMsg, absMsgFrom, respM, ↓reduceIte]
  itrivial

/-- The cache's answers (`processNoUpdate` before the loop, `wNoUpdate`): from a state of the
witness's history, an answer without a write is legitimate. -/
theorem wInst_cache (γ : RaftNames) (id : w64) (cq pv : Bool) (μ : WMsg) (Hid : id = γ.reWit)
    (Hwnz : γ.reWit ≠ W64 0) (Hto : μ.to = id) (σ : WHS) (hh : Bool) (r : Option WResp)
    (Hr : wNoUpdate id cq pv hh σ μ = some r) :
    ⊢ isMessage (GF := GF) γ (wAbsReq μ) -∗ wSt γ σ.ws -∗ wRespOk γ r := by
  subst Hid
  iintro #Hm #Hst
  unfold wNoUpdate at Hr
  by_cases h1 : (!hh && decide (μ.ty = MsgHeartbeat)) = true
  · rw [if_pos h1] at Hr; cases Hr; unfold wRespOk; itrivial
  rw [if_neg h1] at Hr
  by_cases h2 : uint.Z μ.term < uint.Z σ.term
  · rw [if_pos h2] at Hr
    cases Hr
    unfold wOlder
    split
    · iapply wRespOk_appResp0
    · split
      · iapply wRespOk_preVoteResp
      · unfold wRespOk; itrivial
  rw [if_neg h2] at Hr
  by_cases h3 : μ.term = σ.term ∧ μ.ty = MsgApp
  · rw [if_pos h3] at Hr
    simp only at Hr
    by_cases h4 : (wAppendNoUpdate γ.reWit σ μ).2 = true
    · rw [if_pos h4] at Hr
      cases Hr
      obtain ⟨Hc, Hty', Heq⟩ := wAppNoUpd_of γ.reWit σ μ h3.2 h4
      have Hpair : (wAppendNoUpdate γ.reWit σ μ).1 = ((wAppendNoUpdate γ.reWit σ μ).1.1, []) := by
        rw [← Hc]
      rw [Hpair]
      iapply wRespOk_of γ _ [] .appResp (by rw [Hty']; rfl)
      have Hreq : (wAbsReq μ).ty = .wapp := by unfold wAbsReq; rw [if_pos h3.2]
      have Hdst : (wAbsReq μ).dst = γ.reWit := by
        unfold wAbsReq; rw [if_pos h3.2]; exact Hto
      have Hterm : (wAbsReq μ).term = σ.ws.term := by
        unfold wAbsReq; rw [if_pos h3.2]; exact h3.1
      have H := wSt_app_noupd (GF := GF) γ σ.ws (wAbsReq μ) _ Hreq Hdst Hwnz Hterm Heq
      rw [← Hc]
      iapply H $$ Hst Hm
    · rw [if_neg h4] at Hr; cases Hr
  · rw [if_neg h3] at Hr; cases Hr

/-- `processMessageWithNewerTerm` of a message other than a pre-vote is W2's raise. -/
theorem wNewer_ws (σ : WHS) (μ : WMsg) (h : μ.ty ≠ MsgPreVote) :
    (wNewer σ μ).ws = wRaise σ.ws μ.term := by
  unfold wNewer
  rw [if_neg h]
  split <;> rfl

theorem wNewer_prevote (σ : WHS) (μ : WMsg) (h : μ.ty = MsgPreVote) : wNewer σ μ = σ := by
  unfold wNewer; rw [if_pos h]

/-- A request `wNoUpdate` does not answer from the state read is of its term or a later one,
and an append of its term is one `handleAppendNoUpdate` does not answer. -/
theorem wNoUpdate_none (id : w64) (cq pv : Bool) (σ : WHS) (μ : WMsg)
    (H : wNoUpdate id cq pv true σ μ = none) :
    ¬ uint.Z μ.term < uint.Z σ.term ∧
    (μ.term = σ.term → μ.ty = MsgApp → (wAppendNoUpdate id σ μ).2 = false) := by
  unfold wNoUpdate at H
  simp only [Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte] at H
  by_cases h2 : uint.Z μ.term < uint.Z σ.term
  · rw [if_pos h2] at H; cases H
  rw [if_neg h2] at H
  refine ⟨h2, fun he ha => ?_⟩
  rw [if_pos ⟨he, ha⟩] at H
  cases h : (wAppendNoUpdate id σ μ).2
  · rfl
  · rw [h] at H; simp at H

/-- A witness append to the witness carries an entry of its own term. -/
theorem isMessage_wapp_lt (γ : RaftNames) (m : Msg) (Hty : m.ty = .wapp) (Hd : m.dst = γ.reWit)
    (Hwnz : γ.reWit ≠ W64 0) :
    isMessage (GF := GF) γ m ⊢ ⌜m.logterm = m.term⌝ := by
  simp only [isMessage, Hty]
  rw [if_pos ⟨Hd, Hwnz⟩]
  iintro ⟨%x, %P, %c, %H, %Hm, -⟩
  ipureintro; exact Hm.1

/-- The write of a heartbeat of a newer term: the term raised, the heartbeat answered at it. -/
theorem wInst_write_hb (γ : RaftNames) (E : CoPset) (μ : WMsg) (σ : WHS)
    (Hwnz : γ.reWit ≠ W64 0) (Hhb : μ.ty = MsgHeartbeat) (Hlt : uint.Z σ.term < uint.Z μ.term) :
    ⊢ isMessage (GF := GF) γ (wAbsReq μ) -∗
      (wGhost γ σ.ws ={E}=∗ wGhost γ (wNewer σ μ).ws ∗ wSt γ (wNewer σ μ).ws ∗
        wRespOk γ (some (wHeartbeat γ.reWit (wNewer σ μ).term μ))) := by
  have Hpv : μ.ty ≠ MsgPreVote := by rw [Hhb]; simp [MsgHeartbeat, MsgPreVote]
  have Hreq : wAbsReq μ = Msg.mkV .heartbeat μ.frm μ.to μ.term false (W64 0) (W64 0) (W64 0)
      (W64 0) [] [] μ.ctx := by
    unfold wAbsReq
    rw [if_neg (by rw [Hhb]; simp [MsgHeartbeat, MsgApp]),
      if_neg (by rw [Hhb]; simp [MsgHeartbeat, MsgVote]), if_pos Hhb]
  have Hterm : (wNewer σ μ).term = μ.term := by
    unfold wNewer; rw [if_neg Hpv, if_pos (Or.inr (Or.inl Hhb))]
  iintro #Hm Hg
  rw [wNewer_ws σ μ Hpv, Hterm]
  imod wGhost_raise γ σ.ws μ.term Hlt $$ Hg with ⟨Hg, #Hst⟩
  icases wGhost_heartbeat γ (wRaise σ.ws μ.term) (wAbsReq μ) (by rw [Hreq]) (by rw [Hreq]; rfl)
    Hwnz $$ Hm Hg with ⟨Hg, #Hr⟩
  imodintro
  iframe Hg Hst
  iapply wRespOk_of γ _ _ .heartbeatResp rfl
  have He : absMsg .heartbeatResp (wHeartbeat γ.reWit μ.term μ).1 [] (wHeartbeat γ.reWit μ.term μ).2 =
      Msg.mkV .heartbeatResp γ.reWit (wAbsReq μ).src (wRaise σ.ws μ.term).term false (W64 0)
        (W64 0) (W64 0) (W64 0) [] [] (wAbsReq μ).ctx := by
    rw [Hreq]; rfl
  rw [He]
  iexact Hr

/-- The write of an append to a state `ρ` of the request's term whose stored entry is below the
request's: `handleAppend`'s state and answer, W2's `wGhost_write`. -/
theorem wInst_write_core (γ : RaftNames) (E : CoPset) (μ : WMsg) (ρ : WHS)
    (Hwnz : γ.reWit ≠ W64 0) (Hto : μ.to = γ.reWit) (Happ : μ.ty = MsgApp)
    (Ht : μ.term = ρ.term) (Hnl : ¬ LexLe μ.lt μ.ls ρ.lt ρ.ls) :
    ⊢ isMessage (GF := GF) γ (wAbsReq μ) -∗
      (wGhost γ ρ.ws ={E}=∗
        wGhost γ ({ ρ with lt := μ.lt, ls := μ.ls, li := μ.li, rs := μ.rs0, rsOut := μ.rs1 }).ws ∗
        wSt γ ({ ρ with lt := μ.lt, ls := μ.ls, li := μ.li, rs := μ.rs0, rsOut := μ.rs1 }).ws ∗
        wRespOk γ (some (respM MsgAppResp μ.frm γ.reWit ρ.term μ.li false, []))) := by
  have Hreq : wAbsReq μ = Msg.mkV .wapp μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] μ.rs0 [] := by
    unfold wAbsReq; rw [if_pos Happ]
  iintro #Hm Hg
  imod wGhost_write γ ρ.ws (wAbsReq μ) (by rw [Hreq]) (by rw [Hreq]; exact Hto) Hwnz
    (by rw [Hreq]; exact Ht) (by rw [Hreq]; exact Hnl) $$ Hm Hg with ⟨Hg, #Hr⟩
  have Hws : wAppWrite ρ.ws (wAbsReq μ) =
      ({ ρ with lt := μ.lt, ls := μ.ls, li := μ.li, rs := μ.rs0, rsOut := μ.rs1 } : WHS).ws := by
    rw [Hreq]; rfl
  rw [Hws]
  icases wGhost_read γ _ $$ Hg with ⟨Hg, #Hst⟩
  imodintro
  iframe Hg Hst
  iapply wRespOk_of γ _ _ .appResp rfl
  have He : absMsg .appResp (respM MsgAppResp μ.frm γ.reWit ρ.term μ.li false) [] [] =
      Msg.mk .appResp γ.reWit (wAbsReq μ).src (wAbsReq μ).term false (wAbsReq μ).index (W64 0)
        (W64 0) (W64 0) [] := by
    rw [Hreq, Ht]; rfl
  rw [He]
  iexact Hr

/-- The write of an append (`handleAppend` on the state read, raised to a newer term): the
entry stored, its acknowledgement answered. -/
theorem wInst_write_app (γ : RaftNames) (E : CoPset) (μ : WMsg) (σ : WHS)
    (Hwnz : γ.reWit ≠ W64 0) (Hto : μ.to = γ.reWit) (Happ : μ.ty = MsgApp)
    (Hge : ¬ uint.Z μ.term < uint.Z σ.term)
    (Hnu : μ.term = σ.term → (wAppendNoUpdate γ.reWit σ μ).2 = false) :
    ⊢ isMessage (GF := GF) γ (wAbsReq μ) -∗ wSt γ σ.ws -∗
      (wGhost γ σ.ws ={E}=∗
        wGhost γ (wAppend γ.reWit σ (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).1.ws ∗
        wSt γ (wAppend γ.reWit σ (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).1.ws ∗
        wRespOk γ (some (wAppend γ.reWit σ (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).2)) := by
  have Hreq : wAbsReq μ = Msg.mkV .wapp μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) [] μ.rs0 [] := by
    unfold wAbsReq; rw [if_pos Happ]
  have Hpv : μ.ty ≠ MsgPreVote := by rw [Happ]; simp [MsgApp, MsgPreVote]
  iintro #Hm #Hst Hg
  ihave %Hlt := isMessage_wapp_lt γ (wAbsReq μ) (by rw [Hreq]) (by rw [Hreq]; exact Hto) Hwnz $$ Hm
  rw [Hreq] at Hlt
  simp only at Hlt
  ihave %Hsl := wSt_lt_le γ σ.ws $$ Hst
  simp only [WHS.ws] at Hsl
  -- not answered without a write: the request's entry is later than the stored one
  have Hun : (wAppendNoUpdate γ.reWit σ μ).2 = false ∧ ¬ LexLe μ.lt μ.ls σ.lt σ.ls := by
    have Hunh : (wAppendNoUpdate γ.reWit σ μ).2 = false := by
      by_cases hlt : uint.Z σ.term < uint.Z μ.term
      · unfold wAppendNoUpdate
        have h1 : ¬ (μ.lt = σ.lt ∧ μ.ls = σ.ls) := by
          rintro ⟨h, -⟩; rw [h] at Hlt; rw [Hlt] at Hsl; omega
        have h2 : ¬ ltPair μ.lt μ.ls σ.lt σ.ls := by
          unfold ltPair; rw [Hlt]; rintro (h | ⟨h, -⟩)
          · omega
          · rw [← h] at Hsl; omega
        rw [if_neg h1, if_neg h2]
      · exact Hnu (uint_Z_inj.mp (by omega))
    refine ⟨Hunh, fun hle => ?_⟩
    unfold wAppendNoUpdate at Hunh
    by_cases h1 : μ.lt = σ.lt ∧ μ.ls = σ.ls
    · rw [if_pos h1] at Hunh; cases Hunh
    rw [if_neg h1] at Hunh
    rw [if_pos ((ltPair_iff_LexLe _ _ _ _ h1).mpr hle)] at Hunh
    cases Hunh
  obtain ⟨Hunh, Hnl⟩ := Hun
  have Happ' : ∀ st : WHS, wAppend γ.reWit σ st μ =
      ({ st with lt := μ.lt, ls := μ.ls, li := μ.li, rs := μ.rs0, rsOut := μ.rs1 },
        (respM MsgAppResp μ.frm γ.reWit st.term μ.li false, [])) := by
    intro st; simp only [wAppend, Hunh, Bool.false_eq_true, ↓reduceIte]
  rw [Happ']
  by_cases hlt : uint.Z σ.term < uint.Z μ.term
  · -- a newer term: raised, then written
    rw [if_pos hlt]
    have HR := wGhost_raise (GF := GF) γ σ.ws μ.term hlt
    rw [← wNewer_ws σ μ Hpv] at HR
    imod HR $$ Hg with ⟨Hg, -⟩
    have Hnt : (wNewer σ μ).term = μ.term := by
      unfold wNewer; rw [if_neg Hpv, if_pos (Or.inl Happ)]
    have Hnl' : ¬ LexLe μ.lt μ.ls (wNewer σ μ).lt (wNewer σ μ).ls := by
      unfold wNewer; rw [if_neg Hpv, if_pos (Or.inl Happ)]; exact Hnl
    iapply wInst_write_core γ E μ (wNewer σ μ) Hwnz Hto Happ Hnt.symm Hnl' $$ Hm Hg
  · rw [if_neg hlt]
    have Ht : μ.term = σ.term := uint_Z_inj.mp (by omega)
    iapply wInst_write_core γ E μ σ Hwnz Hto Happ Ht Hnl $$ Hm Hg

end ghost2

/-- `handleVote` of a vote request: a rejection at the state's term, the state unchanged; or a
grant (the witness may vote for the candidate, whose last entry is not below its own, and of
its own with every responder in its replication set), the vote recorded. -/
theorem wVote_cases [FfiSyntax] (id : w64) (ρ : WHS) (μ : WMsg) (Hv : μ.ty = MsgVote) :
    wVote id ρ μ = (ρ, (respM MsgVoteResp μ.frm id ρ.term (W64 0) true, [])) ∨
    ((ρ.vote = μ.frm ∨ (ρ.vote = W64 0 ∧ ρ.lead = W64 0)) ∧ ¬ ltPair μ.lt μ.ls ρ.lt ρ.ls ∧
      (μ.lt = ρ.lt ∧ μ.ls = ρ.ls → votesInSet ρ.rs μ.votes = GMap.size μ.votes) ∧
      wVote id ρ μ = ({ ρ with vote := μ.frm },
        (respM MsgVoteResp μ.frm id μ.term (W64 0) false, []))) := by
  have Hnpv : ¬ μ.ty = MsgPreVote := by rw [Hv]; simp [MsgVote, MsgPreVote]
  by_cases hc : ρ.vote = μ.frm ∨ (ρ.vote = W64 0 ∧ ρ.lead = W64 0)
  · by_cases hl : ltPair μ.lt μ.ls ρ.lt ρ.ls
    · left; simp only [wVote, Hnpv, eq_true Hv, _root_.false_and, _root_.or_false, _root_.true_and, ↓reduceIte, ne_eq, _root_.decide_true, decide_false, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, _root_.and_self, _root_.and_true, _root_.and_false, ite_true, ite_false, eq_self_iff_true, eq_true hc, eq_true hl]
    · by_cases he : μ.lt = ρ.lt ∧ μ.ls = ρ.ls
      · by_cases hvs : votesInSet ρ.rs μ.votes = GMap.size μ.votes
        · right; refine ⟨hc, hl, fun _ => hvs, ?_⟩; simp only [wVote, Hnpv, eq_true Hv, _root_.false_and, _root_.or_false, _root_.true_and, ↓reduceIte, ne_eq, _root_.decide_true, decide_false, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, _root_.and_self, _root_.and_true, _root_.and_false, ite_true, ite_false, eq_self_iff_true, eq_true hc, eq_false hl, eq_true he, hvs]
        · left; simp only [wVote, Hnpv, eq_true Hv, _root_.false_and, _root_.or_false, _root_.true_and, ↓reduceIte, ne_eq, _root_.decide_true, decide_false, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, _root_.and_self, _root_.and_true, _root_.and_false, ite_true, ite_false, eq_self_iff_true, eq_true hc, eq_false hl, eq_true he, hvs]
      · right; refine ⟨hc, hl, fun h => absurd h he, ?_⟩; simp only [wVote, Hnpv, eq_true Hv, _root_.false_and, _root_.or_false, _root_.true_and, ↓reduceIte, ne_eq, _root_.decide_true, decide_false, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, _root_.and_self, _root_.and_true, _root_.and_false, ite_true, ite_false, eq_self_iff_true, eq_true hc, eq_false hl, eq_false he]
  · left; simp only [wVote, Hnpv, eq_true Hv, _root_.false_and, _root_.or_false, _root_.true_and, ↓reduceIte, ne_eq, _root_.decide_true, decide_false, not_true_eq_false, not_false_eq_true, Bool.false_eq_true, Bool.true_eq_false, _root_.and_self, _root_.and_true, _root_.and_false, ite_true, ite_false, eq_self_iff_true, eq_false hc]

/-- `handleVote` of a pre-vote leaves the state as it is and answers with a `MsgPreVoteResp`. -/
theorem wVote_prevote [FfiSyntax] (id : w64) (ρ : WHS) (μ : WMsg) (Hp : μ.ty = MsgPreVote) :
    ∃ t rj, wVote id ρ μ = (ρ, (respM MsgPreVoteResp μ.frm id t (W64 0) rj, [])) := by
  have Hnv : ¬ μ.ty = MsgVote := by rw [Hp]; simp [MsgVote, MsgPreVote]
  unfold wVote
  simp only [Hnv, eq_true Hp, false_and, if_false, ↓reduceIte]
  exact ⟨_, _, rfl⟩

section ghost3
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A justified state's replication set has no repetition. -/
theorem wStJust_nodup (γ : RaftNames) (st : WState) : wStJust (GF := GF) γ st ⊢ ⌜st.rs.Nodup⌝ := by
  unfold wStJust
  split
  · iintro %h; ipureintro; rw [h.2]; exact List.nodup_nil
  · iintro ⟨%x, %P, %c, %H, %h, -⟩; ipureintro; exact h.2

/-- A vote request of the state's term: `handleVote`, W2's `wGhost_vote` on a grant. -/
theorem wInst_vote_core (γ : RaftNames) (E : CoPset) (HE : (↑raftLogN : CoPset) ⊆ E) (μ : WMsg)
    (ρ : WHS) (Hwnz : γ.reWit ≠ W64 0) (Hto : μ.to = γ.reWit) (Hfr : μ.frm ≠ W64 0)
    (Hv : μ.ty = MsgVote) (Ht : μ.term = ρ.term) :
    ⊢ raftCommitInv (GF := GF) γ -∗ isMessage γ (wAbsReq μ) -∗ wSt γ ρ.ws -∗
      (wGhost γ ρ.ws ={E}=∗ wGhost γ (wVote γ.reWit ρ μ).1.ws ∗ wSt γ (wVote γ.reWit ρ μ).1.ws ∗
        wRespOk γ (some (wVote γ.reWit ρ μ).2)) := by
  have Hreq : wAbsReq μ = Msg.mkV .wvote μ.frm μ.to μ.term false μ.li μ.lt μ.ls (W64 0) []
      (elements (domSet μ.votes)) [] := by
    unfold wAbsReq; rw [if_neg (by rw [Hv]; simp [MsgVote, MsgApp]), if_pos Hv]
  iintro #Hinv #Hm #Hst Hg
  rcases wVote_cases γ.reWit ρ μ Hv with Hr | ⟨Hcv, Hnl, Heq, Hr⟩
  · rw [Hr]
    imodintro
    iframe Hg Hst
    iapply wRespOk_voteReject
  · have Hresp : (wVote γ.reWit ρ μ).2 = (respM MsgVoteResp μ.frm γ.reWit μ.term (W64 0) false, []) := by
      rw [Hr]
    have Hws : ({ ρ.ws with vote := μ.frm } : WState) = (wVote γ.reWit ρ μ).1.ws := by rw [Hr]; rfl
    rw [Hresp]
    ihave #Hj := wSt_just γ ρ.ws $$ Hst
    ihave %Hnd := wStJust_nodup γ ρ.ws $$ Hj
    have Hgr : WGrantOk ρ.ws μ.lt μ.ls (elements (domSet μ.votes)) := by
      by_cases he : μ.lt = ρ.lt ∧ μ.ls = ρ.ls
      · refine Or.inr ⟨he.1.symm, he.2.symm, fun v hv => ?_⟩
        exact votesInSet_all ρ.rs μ.votes Hnd (Heq he) v ((GMap.elem_of_elements _ _).mp hv)
      · have hne : ¬ (ρ.ws.lt = μ.lt ∧ ρ.ws.ls = μ.ls) := fun ⟨a, b⟩ => he ⟨a.symm, b.symm⟩
        refine Or.inl ⟨?_, hne⟩
        unfold ltPair at Hnl
        unfold LexLe
        by_cases h1 : ρ.lt = μ.lt
        · right
          refine ⟨h1, ?_⟩
          have h2 : ¬ uint.Z μ.ls < uint.Z ρ.ls := fun h => Hnl (Or.inr ⟨h1.symm, h⟩)
          show uint.Z ρ.ls ≤ uint.Z μ.ls
          omega
        · left
          have : uint.Z ρ.lt ≠ uint.Z μ.lt := fun e => h1 (uint_Z_inj.mp e)
          have h2 : ¬ uint.Z μ.lt < uint.Z ρ.lt := fun h => Hnl (Or.inl h)
          show uint.Z ρ.lt < uint.Z μ.lt
          omega
    have Hsrc : (wAbsReq μ).src = μ.frm := by rw [Hreq]
    have Htm : (wAbsReq μ).term = μ.term := by rw [Hreq]
    have HV := wGhost_vote (GF := GF) γ E HE ρ.ws (wAbsReq μ) (by rw [Hreq]) (by rw [Hreq]; exact Hto)
      Hwnz (by rw [Htm]; exact Ht) (by rw [Hsrc]; exact Hfr)
      (by rw [Hsrc]; rcases Hcv with h | h; exact Or.inl h; exact Or.inr h.1)
      (by rw [Hreq]; exact Hgr)
    rw [Hsrc, Htm, Hws] at HV
    imod HV $$ Hinv Hm Hg with ⟨Hg, #Hvt⟩
    icases wGhost_read γ _ $$ Hg with ⟨Hg, #Hst'⟩
    imodintro
    iframe Hg Hst'
    iapply wRespOk_of γ _ _ .voteResp rfl
    simp only [isMessage, absMsg, absMsgFrom, respM, Bool.false_eq_true, ↓reduceIte]
    iexact Hvt

/-- A vote request (`handleVote` on the state read, raised to a newer term). -/
theorem wInst_write_vote (γ : RaftNames) (E : CoPset) (HE : (↑raftLogN : CoPset) ⊆ E) (μ : WMsg)
    (σ : WHS) (Hwnz : γ.reWit ≠ W64 0) (Hto : μ.to = γ.reWit) (Hfr : μ.frm ≠ W64 0)
    (Hv : μ.ty = MsgVote) (Hge : ¬ uint.Z μ.term < uint.Z σ.term) :
    ⊢ raftCommitInv (GF := GF) γ -∗ isMessage γ (wAbsReq μ) -∗ wSt γ σ.ws -∗
      (wGhost γ σ.ws ={E}=∗
        wGhost γ (wVote γ.reWit (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).1.ws ∗
        wSt γ (wVote γ.reWit (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).1.ws ∗
        wRespOk γ (some (wVote γ.reWit (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).2)) := by
  have Hpv : μ.ty ≠ MsgPreVote := by rw [Hv]; simp [MsgVote, MsgPreVote]
  iintro #Hinv #Hm #Hst Hg
  by_cases hlt : uint.Z σ.term < uint.Z μ.term
  · rw [if_pos hlt]
    have HR := wGhost_raise (GF := GF) γ σ.ws μ.term hlt
    rw [← wNewer_ws σ μ Hpv] at HR
    imod HR $$ Hg with ⟨Hg, #Hst'⟩
    have Hnt : (wNewer σ μ).term = μ.term := by
      unfold wNewer; rw [if_neg Hpv]; split <;> rfl
    iapply wInst_vote_core γ E HE μ (wNewer σ μ) Hwnz Hto Hfr Hv Hnt.symm $$ Hinv Hm Hst' Hg
  · rw [if_neg hlt]
    have Ht : μ.term = σ.term := uint_Z_inj.mp (by omega)
    iapply wInst_vote_core γ E HE μ σ Hwnz Hto Hfr Hv Ht $$ Hinv Hm Hst Hg

/-- A pre-vote: the state as read, written back; the answer carries nothing. -/
theorem wInst_write_prevote (γ : RaftNames) (E : CoPset) (μ : WMsg) (σ : WHS)
    (Hp : μ.ty = MsgPreVote) :
    ⊢ wSt (GF := GF) γ σ.ws -∗
      (wGhost γ σ.ws ={E}=∗
        wGhost γ (wVote γ.reWit (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).1.ws ∗
        wSt γ (wVote γ.reWit (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).1.ws ∗
        wRespOk γ (some (wVote γ.reWit (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) μ).2)) := by
  have Hst0 : (if uint.Z σ.term < uint.Z μ.term then wNewer σ μ else σ) = σ := by
    split
    · exact wNewer_prevote σ μ Hp
    · rfl
  rw [Hst0]
  obtain ⟨t, rj, Hr⟩ := wVote_prevote γ.reWit σ μ Hp
  rw [Hr]
  iintro #Hst Hg
  imodintro
  iframe Hg Hst
  iapply wRespOk_preVoteResp

end ghost3

section ghost2
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- At every read, the state read is a state of the history, and the round's obligation
(`wObl`) holds: an answer without a write is legitimate, a write's shift keeps the ghost state
the storage's and makes its answer legitimate. -/
theorem wInst_read (γ : RaftNames) (N : Namespace) (HN : (↑raftLogN : CoPset) ⊆ ⊤ \ ↑N)
    (cq pv : Bool) (μ : WMsg) (Hwnz : γ.reWit ≠ W64 0) (Hto : μ.to = γ.reWit)
    (Hfr : μ.frm ≠ W64 0)
    (Hty4 : μ.ty = MsgHeartbeat ∨ μ.ty = MsgApp ∨ μ.ty = MsgVote ∨ μ.ty = MsgPreVote) (σ : WHS) :
    ⊢ raftCommitInv (GF := GF) γ -∗ isMessage γ (wAbsReq μ) -∗ wGhost γ σ.ws ={⊤ \ ↑N}=∗
      wGhost γ σ.ws ∗ wSt γ σ.ws ∗
      wObl γ.reWit cq pv N (fun σ => wGhost γ σ.ws) (fun σ => wSt γ σ.ws) (wRespOk γ) μ σ := by
  iintro #Hinv #Hm Hg
  icases wGhost_read γ σ.ws $$ Hg with ⟨Hg, #Hst⟩
  unfold wObl wStep
  by_cases Hhb : μ.ty = MsgHeartbeat ∧ μ.term = σ.term
  · -- the heartbeat at the stored term
    rw [if_pos Hhb]
    simp only
    have Hreq : wAbsReq μ = Msg.mkV .heartbeat μ.frm μ.to μ.term false (W64 0) (W64 0) (W64 0)
        (W64 0) [] [] μ.ctx := by
      unfold wAbsReq
      rw [if_neg (by rw [Hhb.1]; simp [MsgHeartbeat, MsgApp]),
        if_neg (by rw [Hhb.1]; simp [MsgHeartbeat, MsgVote]), if_pos Hhb.1]
    icases wGhost_heartbeat γ σ.ws (wAbsReq μ) (by rw [Hreq]) (by rw [Hreq]; exact Hhb.2) Hwnz
      $$ Hm Hg with ⟨Hg, #Hr⟩
    iframe Hg Hst
    iapply wRespOk_of γ _ _ .heartbeatResp rfl
    have He : absMsg .heartbeatResp (wHeartbeat γ.reWit σ.term μ).1 [] (wHeartbeat γ.reWit σ.term μ).2 =
        Msg.mkV .heartbeatResp γ.reWit (wAbsReq μ).src σ.ws.term false (W64 0) (W64 0) (W64 0)
          (W64 0) [] [] (wAbsReq μ).ctx := by
      rw [Hreq]; rfl
    rw [He]
    iexact Hr
  rw [if_neg Hhb]
  cases Hnu : wNoUpdate γ.reWit cq pv true σ μ with
  | some r =>
    simp only
    iframe Hg Hst
    iapply wInst_cache γ γ.reWit cq pv μ rfl Hwnz Hto σ true r Hnu $$ Hm Hst
  | none =>
  simp only
  obtain ⟨Hge, Hnu'⟩ := wNoUpdate_none γ.reWit cq pv σ μ Hnu
  iframe Hg Hst
  imodintro
  rcases Hty4 with Hh | Ha | Hv | Hp
  · have hlt : uint.Z σ.term < uint.Z μ.term := by
      have h1 : μ.term ≠ σ.term := fun e => Hhb ⟨Hh, e⟩
      have : uint.Z μ.term ≠ uint.Z σ.term := fun e => h1 (uint_Z_inj.mp e)
      omega
    rw [if_pos Hh, if_pos hlt]
    iapply wInst_write_hb γ (⊤ \ ↑N) μ σ Hwnz Hh hlt $$ Hm
  · have Hnh : ¬ μ.ty = MsgHeartbeat := by rw [Ha]; simp [MsgApp, MsgHeartbeat]
    rw [if_neg Hnh, if_pos Ha]
    iapply wInst_write_app γ (⊤ \ ↑N) μ σ Hwnz Hto Ha Hge (fun e => Hnu' e Ha) $$ Hm Hst
  · have Hnh : ¬ μ.ty = MsgHeartbeat := by rw [Hv]; simp [MsgVote, MsgHeartbeat]
    have Hna : ¬ μ.ty = MsgApp := by rw [Hv]; simp [MsgVote, MsgApp]
    rw [if_neg Hnh, if_neg Hna]
    iapply wInst_write_vote γ (⊤ \ ↑N) HN μ σ Hwnz Hto Hfr Hv Hge $$ Hinv Hm Hst
  · have Hnh : ¬ μ.ty = MsgHeartbeat := by rw [Hp]; simp [MsgPreVote, MsgHeartbeat]
    have Hna : ¬ μ.ty = MsgApp := by rw [Hp]; simp [MsgPreVote, MsgApp]
    rw [if_neg Hnh, if_neg Hna]
    iapply wInst_write_prevote γ (⊤ \ ↑N) μ σ Hp $$ Hst

end ghost2

end EtcdGrove
end Perennial
