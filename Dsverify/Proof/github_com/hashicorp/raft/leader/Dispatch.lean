/-
Ported from dsverify-lab examples/hraft/proof/HrVerify/Proof/github_com/hashicorp/raft/leader/Dispatch.lean (241f27e).
-/
/-
(stage 4, package leader, shared) The proof of `raft.(*Raft).dispatchLogs`, generic in the kinds of
the dispatched futures and in the protocol step (`leader.dispatch_gen`): `dispatchLogs`' spec
(`Raft__dispatchLogs.lean`) and `appendConfigurationEntry` (one configuration entry) instantiate it.
-/
module

public import Dsverify.Spec.github_com.hashicorp.raft.Raft__dispatchLogs
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCurrentTerm
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getLastIndex
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__getCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.Raft__tryStageCommitIndex
public import Dsverify.Spec.github_com.hashicorp.raft.commitment__match
public import Dsverify.Spec.github_com.hashicorp.raft.raftState__setLastLog
public import Dsverify.Spec.github_com.hashicorp.raft.asyncNotifyCh
public import Perennial.Spec.time.Now
public import Dsverify.Proof.github_com.hashicorp.raft.gprot.Snap
public import Dsverify.Proof.github_com.hashicorp.raft.handlers.Base
public import Dsverify.Proof.github_com.hashicorp.raft.leader.MainCfg
public import Dsverify.Proof.github_com.hashicorp.raft.core.CrashLaws

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace github_com.hashicorp.raft
open proto gprot

/-- A future dispatched by the first loop of `dispatchLogs`: the future and its entry. -/
structure DItem where
  f : Loc
  e : Entry

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

instance barrierDisp_persistent' (γ : GNames) (i : SID) (sc : Snap) (b : Nat) (e : Entry) :
    Persistent (barrierDisp (GF := GF) γ i sc b e) := by
  unfold barrierDisp; infer_instance

/-- The `j`-th future of the first loop of `dispatchLogs` (leader of term `T` with a log of
length `base`), after its iteration: its `log` field is the entry at `base + 1 + j`, read-only;
its kind and data satisfy `K` (stage 4: the caller's restriction: commands, no-ops and barriers for
`dispatchLogs`' spec, one configuration entry for `appendConfigurationEntry`); its responder side; for a
command, the client's token, still to go to the protocol. -/
def dDone (γ : GNames) (rc : RCtx GF) (i : SID) (K : Nat → List w8 → Prop) (T base j : Nat)
    (d : DItem) : IProp GF :=
  iprop(logPtr (d.f.[logFuture, go!"log"]) (base + 1 + j) d.e ∗
    ⌜d.e.term = T ∧ K d.e.kind d.e.data⌝ ∗
    (∃ v : GoInterface, d.f.[logFuture, go!"response"] ↦ v) ∗
    ((⌜d.e.kind = kNoop⌝ ∗ deferResp (d.f.[logFuture, go!"deferError"]) (fun _ => iprop(True))) ∨
     (∃ n : Nat, ⌜d.e.kind = kCommand⌝ ∗
        deferResp (d.f.[logFuture, go!"deferError"]) (futQ γ rc d.f d.e.data n) ∗
        opTok γ d.e.data n) ∨
     (∃ sc : Snap, ⌜d.e.kind = kBarrier⌝ ∗ barrierDisp γ i sc (base + 1 + j) d.e ∗
        deferResp (d.f.[logFuture, go!"deferError"]) (barrierQ γ rc i sc)) ∨
     (⌜d.e.kind = kConfig⌝ ∗ deferResp (d.f.[logFuture, go!"deferError"]) cfgChangeQ)))

theorem set_snoc_rep (xs : List Loc) (n k : Nat) (y z : Loc) (hx : xs.length = k) (hk : k < n) :
    (xs ++ List.replicate (n - k) z).set k y = (xs ++ [y]) ++ List.replicate (n - (k + 1)) z := by
  rw [show n - k = (n - (k + 1)) + 1 by omega, List.replicate_succ, ← hx, List.set_append_right _ _ (by omega)]
  simp

theorem lastTerm_append_cons (L es : RLog) (e : Entry) :
    lastTerm (L ++ es ++ [e]) = e.term := by
  unfold lastTerm termAt ent
  simp

theorem lastTerm_append_ne (L es : RLog) (T : Nat) (hne : es ≠ [])
    (hT : ∀ e ∈ es, e.term = T) : lastTerm (L ++ es) = T := by
  obtain ⟨es', e, rfl⟩ := List.eq_nil_or_concat es |>.resolve_left hne
  rw [List.concat_eq_append, ← List.append_assoc, lastTerm_append_cons]
  exact hT e (by simp)

/-- The dispatched futures of the first loop, split for `StoreLogs` (their log pointers), the
protocol (their entries' facts and the clients' tokens) and the inflight list (`futResp`). -/
theorem dDone_split (γ : GNames) (rc : RCtx GF) (i : SID) (K : Nat → List w8 → Prop) (T : Nat) :
    ∀ (ds : List DItem) (base : Nat),
    ([∗list] j ↦ d ∈ ds, dDone γ rc i K T base j d) ⊢
      ⌜∀ e ∈ ds.map DItem.e, e.term = T ∧ K e.kind e.data⌝ ∗
      ([∗list] j ↦ p ∈ ds.map (fun d => d.f.[logFuture, go!"log"]),
        ∃ e, ⌜(ds.map DItem.e)[j]? = some e⌝ ∗ logPtr p (base + 1 + j) e) ∗
      ([∗list] e ∈ (ds.map DItem.e).filter (fun e => decide (e.kind = kCommand)),
        ∃ n, opTok γ e.data n) ∗
      ([∗list] j ↦ d ∈ ds, futResp γ rc i d.f (base + 1 + j) d.e) := by
  intro ds
  induction ds with
  | nil =>
    intro base
    iintro -
    simp only [List.map_nil, List.filter_nil]
    isplitr
    · ipureintro; intro e he; simp at he
    isplitr; · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr; · iapply BigSepL.bigSepL_nil.2; iempintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons d ds ih =>
    intro base
    iintro Hl
    ihave ⟨Hd, Hl⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    ihave Hl : ([∗list] j ↦ d ∈ ds, dDone γ rc i K T (base + 1) j d) $$ [Hl]
    · iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hl
      unfold dDone; rw [show base + 1 + (k + 1) = base + 1 + 1 + k by omega]
    ihave ⟨%Hp, #Hptrs, Htoks, Hresps⟩ := ih (base + 1) $$ Hl
    unfold dDone
    icases Hd with ⟨#Hlp, %Hde, Hresp, Hdr⟩
    isplitr
    · ipureintro
      intro e he
      simp only [List.map_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact Hde
      · exact Hp e he
    isplitr
    · simp only [List.map_cons]
      iapply BigSepL.bigSepL_cons.2
      isplitr
      · iexists d.e; isplitr; · ipureintro; rfl
        rw [Nat.add_zero]; iexact Hlp
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hptrs
      simp only [List.getElem?_cons_succ]
      rw [show base + 1 + 1 + k = base + 1 + (k + 1) by omega]
    icases Hdr with (⟨%Hk, Hde'⟩ | ⟨%n, %Hk, Hde', Htok⟩ | ⟨%sc, %Hk, #Hbd, Hde'⟩ | ⟨%Hk, Hde'⟩)
    · have hnc : ¬ d.e.kind = kCommand := by rw [Hk]; decide
      rw [List.map_cons, List.filter_cons_of_neg (by simp [hnc])]
      iframe
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hresp Hde']
      · unfold futResp; isplitr; · iexact Hlp
        iframe; ileft; iframe; ipureintro; exact Hk
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hresps
      rw [show base + 1 + 1 + k = base + 1 + (k + 1) by omega]
    · rw [List.map_cons, List.filter_cons_of_pos (by simp [Hk])]
      isplitl [Htok Htoks]
      · iapply BigSepL.bigSepL_cons.2; iframe
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hresp Hde']
      · unfold futResp; isplitr; · iexact Hlp
        iframe; iright; ileft; iexists d.e.data, n; iframe
        ipureintro; exact ⟨Hk, rfl⟩
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hresps
      rw [show base + 1 + 1 + k = base + 1 + (k + 1) by omega]
    · have hnc : ¬ d.e.kind = kCommand := by rw [Hk]; decide
      rw [List.map_cons, List.filter_cons_of_neg (by simp [hnc])]
      iframe
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hresp Hde']
      · unfold futResp; isplitr; · iexact Hlp
        iframe; iright; iright; ileft; iexists sc; iframe; rw [Nat.add_zero]; iframe #
        ipureintro; exact Hk
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hresps
      rw [show base + 1 + 1 + k = base + 1 + (k + 1) by omega]
    · have hnc : ¬ d.e.kind = kCommand := by rw [Hk]; decide
      rw [List.map_cons, List.filter_cons_of_neg (by simp [hnc])]
      iframe
      iapply BigSepL.bigSepL_cons.2
      isplitl [Hresp Hde']
      · unfold futResp; isplitr; · iexact Hlp
        iframe; iright; iright; iright; iframe; ipureintro; exact Hk
      iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hresps
      rw [show base + 1 + 1 + k = base + 1 + (k + 1) by omega]

/-- The inflight futures of a leader are in its log. -/
theorem inflight_bound (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (E : CoPset)
    (hE : ↑gprotN ⊆ E) :
    ∀ fs0 : List InflightItem,
    gprot.Inv γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ∗
      ([∗list] x ∈ fs0, futResp γ rc i x.f x.k x.e ∗ llogIdx γ s.term x.k x.e) ⊢ |={E}=>
      srvOwn γ i s ∗ ([∗list] x ∈ fs0, futResp γ rc i x.f x.k x.e ∗ llogIdx γ s.term x.k x.e) ∗
      ⌜∀ x ∈ fs0, x.k ≤ s.log.length⌝ := by
  intro fs0
  induction fs0 with
  | nil =>
    iintro ⟨-, Hs, -, Hl⟩
    iframe; ipureintro; intro x hx; simp at hx
  | cons x xs ih =>
    iintro ⟨#HI, Hs, #Hl, Hfs⟩
    ihave ⟨⟨Hx, #Hxl⟩, Hfs⟩ := BigSepL.bigSepL_cons.1 $$ Hfs
    imod llogIdx_leader γ E hE i s x.k x.e $$ [Hs] with ⟨Hs, %Hent⟩
    · iframe; iframe #
    imod ih $$ [Hs Hfs] with ⟨Hs, Hfs, %Hb⟩
    · iframe; iframe #
    imodintro
    isplitl [Hs]; · iexact Hs
    isplitl [Hx Hfs]
    · iapply BigSepL.bigSepL_cons.2; iframe; iframe #
    ipureintro
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · unfold ent at Hent
      split at Hent
      · cases Hent
      · have := (List.getElem?_eq_some_iff.mp Hent).1; omega
    · exact Hb y hy

/-- (stage 2) A barrier future dispatched at `b > |log|` by the leader `i` of `s.term`: what the
leader knows at dispatch (`barrierDisp`: a snapshot after the client's, in its term, where its
log, so `llog s.term`, is shorter than `b`). -/
theorem disp_barrier_prep (γ : GNames) (rc : RCtx GF) (i : SID) (E : CoPset) (hE : ↑gprotN ⊆ E)
    (s : SState) (n0 b : Nat) (e : Entry)
    (he : e.term = s.term) (hb : s.log.length < b) (hn0 : n0 ≤ s.log.length) (f : Loc) (P0 P1 : IProp GF)
    (φ : Prop) (P3 : IProp GF) :
    Inv γ ∗ srvOwn γ i s ∗ leaderIs γ s.term i ∗ len0Is γ s.term n0 ∗
      (P0 ∨ P1 ∨ (⌜φ⌝ ∗ ∃ sc : Snap, histLb γ sc ∗
        deferResp (f.[logFuture, go!"deferError"]) (barrierQ γ rc i sc)) ∨ P3) ⊢ |={E}=>
    srvOwn γ i s ∗ (P0 ∨ P1 ∨ (⌜φ⌝ ∗ ∃ sc : Snap, barrierDisp γ i sc b e ∗
        deferResp (f.[logFuture, go!"deferError"]) (barrierQ γ rc i sc)) ∨ P3) := by
  iintro ⟨#HI, Hsrv, #Hldr, #Hlen0, (H0 | H1 | Hb | H3)⟩
  · imodintro; iframe
  · imodintro; iframe
  rotate_left
  · imodintro; iframe
  icases Hb with ⟨%hφ, %sc, #Hsc, Hde⟩
  imod srvOwn_now_leader γ E hE i s sc $$ [Hsrv] with ⟨Hsrv, %st, #Hst, %Hst⟩
  · iframe; iframe #
  imodintro
  iframe Hsrv
  iright; iright; ileft; isplitr; · ipureintro; exact hφ
  iexists sc; iframe
  unfold barrierDisp
  iexists n0, st
  rw [he]; iframe #
  obtain ⟨h1, h2, -, h4⟩ := Hst
  ipureintro
  exact ⟨by omega, by have := h1.2.2.2 s.term; omega, h1, h2⟩


/-- The dispatched futures as inflight items, the first at index `b`. -/
def newItems : Nat → List DItem → List InflightItem
  | _, [] => []
  | b, d :: ds => ⟨d.f, b, d.e⟩ :: newItems (b + 1) ds

theorem newItems_f : ∀ (b : Nat) (ds : List DItem),
    (newItems b ds).map InflightItem.f = ds.map DItem.f
  | _, [] => rfl
  | b, d :: ds => by simp [newItems, newItems_f (b + 1) ds]

theorem newItems_k : ∀ (b : Nat) (ds : List DItem),
    (newItems b ds).map InflightItem.k = List.range' b ds.length
  | _, [] => rfl
  | b, d :: ds => by simp [newItems, newItems_k (b + 1) ds, List.range'_succ]

theorem newItems_res (γ : GNames) (rc : RCtx GF) (i : SID) (T : Nat) :
    ∀ (ds : List DItem) (b : Nat),
    ([∗list] j ↦ d ∈ ds, futResp γ rc i d.f (b + j) d.e) ∗
      ([∗list] j ↦ e ∈ ds.map DItem.e, llogIdx γ T (b + j) e) ⊢
      [∗list] x ∈ newItems b ds, futResp γ rc i x.f x.k x.e ∗ llogIdx γ T x.k x.e := by
  intro ds
  induction ds with
  | nil => intro b; iintro -; simp only [newItems]; iapply BigSepL.bigSepL_nil.2; iempintro
  | cons d ds ih =>
    intro b
    iintro ⟨Hr, Hl⟩
    ihave ⟨Hr0, Hr⟩ := BigSepL.bigSepL_cons.1 $$ Hr
    simp only [List.map_cons]
    ihave ⟨Hl0, Hl⟩ := BigSepL.bigSepL_cons.1 $$ Hl
    simp only [newItems]
    iapply BigSepL.bigSepL_cons.2
    rw [Nat.add_zero]
    iframe
    iapply ih (b + 1)
    isplitl [Hr]
    · iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hr
      rw [show b + (k + 1) = b + 1 + k by omega]
    · iapply (BigSepL.bigSepL_mono (fun {k x} _ => ?_)) $$ Hl
      rw [show b + (k + 1) = b + 1 + k by omega]

/-- (stage 4) The kinds `dispatchLogs`' spec dispatches: commands, no-ops, barriers. -/
def Kstd (k : Nat) (d : List w8) : Prop := k = kCommand ∨ k = kNoop ∨ k = kBarrier

/-- A future handed to `dispatchLogs`, opened: its fields, its kind and data satisfying `K` (stage 4),
and its responder side (the no-op's, a client command's with the token, a client barrier's, or
(stage 4) a configuration change's). -/
def dispOpen (γ : GNames) (rc : RCtx GF) (i : SID) (K : Nat → List w8 → Prop) (f : Loc) : IProp GF :=
  iprop(∃ (lv : Log) (t : time.Time) (v : GoInterface) (d x : List w8),
    (f.[logFuture, go!"log"]) ↦ lv ∗ lv.Data' ↦*□ d ∗ lv.Extensions' ↦*□ x ∗
    f.[logFuture, go!"response"] ↦ v ∗ f.[logFuture, go!"dispatch"] ↦ t ∗
    ⌜K (uint.nat lv.Type') d⌝ ∗
    ((⌜lv.Type' = W8 1⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) (fun _ => iprop(True))) ∨
     (⌜lv.Type' = W8 0⌝ ∗ ∃ n : Nat,
        deferResp (f.[logFuture, go!"deferError"]) (futQ γ rc f d n) ∗ opTok γ d n) ∨
     (⌜lv.Type' = W8 4 ∧ d = []⌝ ∗ ∃ sc : Snap, histLb γ sc ∗
        deferResp (f.[logFuture, go!"deferError"]) (barrierQ γ rc i sc)) ∨
     (⌜lv.Type' = W8 5⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) cfgChangeQ)))

theorem dispP_open (γ : GNames) (rc : RCtx GF) (i : SID) (f : Loc) :
    dispP γ rc i f ⊢ dispOpen γ rc i Kstd f := by
  unfold dispP dispOpen
  iintro (Ha | Hn)
  · unfold applyP
    icases Ha with (⟨%d, %n, %lv, %t, Hlog, %Hty, #Hd, ⟨%x, #Hx⟩, Hresp, Hdisp, Hde, Htok⟩ |
      ⟨%lv, %t, %sc, Hlog, %Hty, #Hd, ⟨%x, #Hx⟩, Hresp, Hdisp, #Hsc, Hde⟩)
    · iexists lv, t, interface.nil, d, x
      isplitl [Hlog]; · iexact Hlog
      isplitr; · iexact Hd
      isplitr; · iexact Hx
      isplitl [Hresp]; · iexact Hresp
      isplitl [Hdisp]; · iexact Hdisp
      isplitr; · ipureintro; unfold Kstd; rw [Hty]; exact Or.inl rfl
      iright; ileft
      isplitr; · ipureintro; exact Hty
      iexists n; iframe
    · iexists lv, t, interface.nil, [], x
      isplitl [Hlog]; · iexact Hlog
      isplitr; · iexact Hd
      isplitr; · iexact Hx
      isplitl [Hresp]; · iexact Hresp
      isplitl [Hdisp]; · iexact Hdisp
      isplitr; · ipureintro; unfold Kstd; rw [Hty]; exact Or.inr (Or.inr rfl)
      iright; iright; ileft
      isplitr; · ipureintro; exact ⟨Hty, rfl⟩
      iexists sc; iframe; iframe #
  · unfold noopP
    icases Hn with ⟨%lv, %t, %v, Hlog, %Hty, #Hd, #Hx, Hresp, Hdisp, Hde⟩
    iexists lv, t, v, [], []
    isplitl [Hlog]; · iexact Hlog
    isplitr; · iexact Hd
    isplitr; · iexact Hx
    isplitl [Hresp]; · iexact Hresp
    isplitl [Hdisp]; · iexact Hdisp
    isplitr; · ipureintro; unfold Kstd; rw [Hty]; exact Or.inr (Or.inl rfl)
    ileft
    isplitr; · ipureintro; exact Hty
    iexact Hde

end defs
end github_com.hashicorp.raft

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.Assumptions]
variable [hRB : ReceiptBoundLe GF (2 ^ 62)]

open github_com.hashicorp.raft proto gprot

/-- (stage 4) **`dispatchLogs`, generic in the futures' kinds** (`K`) and in the protocol step
(hraft_robust: `hwin`, the window and atomic update of `StoreLogs` firing the step, with its own
resources `A` → `B`: `storeLogs_app_win`, `storeLogs_cfg_win`): the parts of `mainOwnAt` it uses
(the view `srvV`, the stable view with the staged commit index, durable), the leader state with
any replication-map condition `P`; the dispatched entries `es` (one per future, of term `s.term`,
kinds and data `K`) are appended. `dispatchLogs`' spec (`Kstd`, `leaderAppendCmd_upd`) and
`appendConfigurationEntry` (one configuration entry, `leaderAppendCfg_upd`) instantiate it. -/
theorem github_com.hashicorp.raft.leader.dispatch_gen
    (wp_getCurrentTerm : github_com.hashicorp.raft.raftState.getCurrentTerm.spec (GF := GF) (hG := hG))
    (wp_getLastIndex : github_com.hashicorp.raft.raftState.getLastIndex.spec (GF := GF) (hG := hG))
    (wp_getCommitIndex : github_com.hashicorp.raft.raftState.getCommitIndex.spec (GF := GF) (hG := hG))
    (wp_tryStageCommitIndex : github_com.hashicorp.raft.Raft.tryStageCommitIndex.spec (GF := GF) (hG := hG))
    (wp_match : github_com.hashicorp.raft.commitment.match.spec (GF := GF) (hG := hG))
    (wp_setLastLog : github_com.hashicorp.raft.raftState.setLastLog.spec (GF := GF) (hG := hG))
    (wp_asyncNotifyCh : github_com.hashicorp.raft.asyncNotifyCh.spec (GF := GF) (hG := hG))
    (wp_Now : time.Now.spec (GF := GF) (hG := hG))
    (r : Loc) (γ : GNames) (rc : RCtx GF) (i : SID) (s : SState) (sl : GoSlice) (dq : DFrac)
    (fs : List Loc) (a : Nat) (K : Nat → List w8 → Prop) (A B : IProp GF)
    (P : GMap SID Loc → Prop) (Hne : fs ≠ [])
    (D : StableAbs) (g : w64)
    (hwin : ∀ es : RLog, es.length = fs.length → (∀ e ∈ es, e.term = s.term ∧ K e.kind e.data) →
      ∀ g' : w64, uint.nat g' ≤ s.dur.1 →
      (Inv γ ∗ srvDurInv γ rc i ∗ srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗ stVS rc D g' ∗ leaderIs γ s.term i ∗ receipt es.length ∗
        ([∗list] e ∈ es.filter (fun e => decide (e.kind = kCommand)), ∃ n, opTok γ e.data n) ∗ A ⊢
        |==> logWin γ rc i (.store (s.log.length + 1) es) ∗
        (logWin γ rc i (.store (s.log.length + 1) es) -∗ |NC={⊤ \ ↑storeN, ∅}=> ▷ ∃ A : LogAbs,
          rc.ownL A ∗ (rc.ownL (A.store (s.log.length + 1) es) ={∅, ⊤ \ ↑storeN}=∗
            srvV rc { s with log := s.log ++ es } ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗ stVS rc D g' ∗
            ([∗list] k ↦ e ∈ es, llogIdx γ s.term (s.log.length + 1 + k) e) ∗ B)))) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft ∗ isRaft r γ rc i ∗
       srvV rc s ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗ stVS rc D g ∗ ⌜uint.nat g ≤ s.dur.1⌝ ∗
       ghostVar rc.names.lastLog (1 : Qp).half (s.log.length, lastTerm s.log) ∗
       monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗ ⌜a ≤ s.dur.1⌝ ∗ leaderIs γ s.term i ∗
       leaderOwnM r γ rc i s.term P s.log.length ∗
       sl ↦*{dq} fs ∗ ([∗list] f ∈ fs, dispOpen γ rc i K f) ∗ A }}
      (App (Val (r @!! go.GoType.PointerType Raft.ty @!! go!"dispatchLogs")) (Val #sl))
    {{ RET #(); ∃ es : RLog, ⌜es.length = fs.length ∧ ∀ e ∈ es, e.term = s.term ∧ K e.kind e.data⌝ ∗
        srvV rc { s with log := s.log ++ es } ∗ ghostVar rc.dur.pw 1 (none : Option Pend) ∗
        (∃ g' : w64, stVS rc D g' ∗ ⌜uint.nat g' ≤ s.dur.1⌝) ∗
        ghostVar rc.names.lastLog (1 : Qp).half ((s.log ++ es).length, s.term) ∗
        monoNatAuthOwn rc.dur.applied (1 : Qp).half a ∗
        leaderOwnM r γ rc i s.term P (s.log ++ es).length ∗ sl ↦*{dq} fs ∗ B ∗
        ([∗list] j ↦ q ∈ fs.map (fun q => q.[logFuture, go!"log"]),
          ∃ e, ⌜es[j]? = some e⌝ ∗ logPtr q (s.log.length + 1 + j) e) }} := by
  wp_start as ⟨#Hr, Hsrv, Hpw, Hst, %Hg, HlastLog, Happ, %Ha, #Hldr, Hl, Hsl, Hfs, HA⟩
  ihave ⟨#HInv, #Hvoter⟩ := isRaft_proto r γ rc i $$ Hr
  ihave #Hcells := isRaft_cells r γ rc i $$ Hr
  unfold raftCells
  icases Hcells with ⟨#HtermC, #HcidxC, #HdurI, -, -, -, -⟩
  iapply wp_ncmod _ _ rfl (srvOwn_facts_R γ rc i (E := ⊤) (by solve_ndisj) s)
  isplitl [Hsrv]; · iframe; iframe #
  iintro ⟨Hsrv, -, %Hfacts⟩
  obtain ⟨Hg1, Hdurlen, Hcidx, Hvt, Ht1, Htlt, Hloglt, Hcfg1, Hkinds⟩ := Hfacts
  wp_auto
  wp_apply wp_Now as %now -
  wp_apply wp_getCurrentTerm.1 $$ [$Hsrv $HInv $HtermC $HdurI] with Hsrv
  wp_apply wp_getLastIndex.1 r γ rc i s a $$ [$HlastLog $Hr $Hsrv $Happ] as %li ⟨%HliEq, HlastLog, Hsrv, Happ⟩
  · ipureintro; exact Ha
  ihave %Hsllen := ownSlice_len $$ Hsl
  wp_apply (wp_slice_make2 (V := Loc)) as %lsl ⟨Hlsl, Hlcap⟩
  · ipureintro; word
  unfold leaderOwnM
  icases Hl with ⟨%cc, %cm, %infl, %fs0, %rs, %rmap, %nt, %sd, %n0, #Hldr', #Hlen0, Hcc, #Hccn, Hcm,
    #Hcmi, Hinfl, Hinfls, Hinflc, %Hfs0, Hfs0, Hrs, Hrsm, Hrmap, Hnt, HNMp, Hsd, #Hsdn, %Hcov, %pb,
    #Hpb, %Hpbc⟩
  imod receipt_zero with Hrc
  ihave HI : (∃ (k : Nat) (ds : List DItem) (lix : w64) (infl' : GoSlice) (pa : Loc) (pidx : w64),
      "i" ∷ i_ptr ↦ W64 k ∗
      "lastIndex" ∷ lastIndex_ptr ↦ lix ∗
      "Hlsl" ∷ lsl ↦* (ds.map (fun d => d.f.[logFuture, go!"log"]) ++
          List.replicate (fs.length - k) (Perennial.zero_val Loc)) ∗
      "Hinfl" ∷ r.[Raft, go!"leaderState"].[leaderState, go!"inflight"] ↦ infl' ∗
      "Hinfls" ∷ infl' ↦* (fs0.map InflightItem.f ++ ds.map DItem.f) ∗
      "Hinflc" ∷ ownSliceCap Loc infl' (DFrac.own 1) ∗
      "%Hk" ∷ ⌜ds.map DItem.f = fs.take k ∧ k ≤ fs.length ∧ uint.nat lix = s.log.length + k⌝ ∗
      "Hds" ∷ ([∗list] j ↦ d ∈ ds, dDone γ rc i K s.term s.log.length j d) ∗
      "Hrest" ∷ ([∗list] f ∈ fs.drop k, dispOpen γ rc i K f) ∗
      "Hrc" ∷ receipt k ∗
      "applyLog" ∷ applyLog_ptr ↦ pa ∗ "idx" ∷ idx_ptr ↦ pidx : IProp GF)
    $$ [i lastIndex Hlsl Hinfl Hinfls Hinflc Hfs Hrc applyLog idx]
  · iexists 0, [], li, infl, _, _
    simp only [List.map_nil, List.append_nil, List.nil_append, Nat.sub_zero, List.drop_zero,
      List.take_zero, BigSepL.bigSepL_nil, Nat.add_zero]
    rw [show sint.nat sl.len = fs.length by omega]
    iframe
    isplitr
    · ipureintro; exact ⟨trivial, Nat.zero_le _, HliEq⟩
    · iapply BigSepL.bigSepL_nil.2; iempintro
  wp_for HI
  wp_if_destruct
  · obtain ⟨Hkds, Hkle, Hlix⟩ := Hk
    have hk : k < fs.length := by word
    list_elem fs k as f
    have hdrop : fs.drop k = f :: fs.drop (k + 1) := by
      rw [List.drop_eq_getElem_cons hk]; congr; exact (List.getElem?_eq_some_iff.mp Hf_lookup).2
    rw [hdrop]
    icases Hrest with ⟨Hf, Hrest⟩
    unfold dispOpen
    icases Hf with ⟨%lv, %t0, %v0, %d, %x, Hlog, #Hd, #Hx, Hresp, Hdisp, %HK, Hde⟩
    have hbp := disp_barrier_prep γ rc i (⊤ \ ↑durN) gprotN_diff_durN s n0 (s.log.length + 1 + k)
      ⟨s.term, uint.nat lv.Type', d⟩ rfl (by omega) Hpbc.1 f
      iprop(⌜lv.Type' = W8 1⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) (fun _ => iprop(True)))
      iprop(⌜lv.Type' = W8 0⌝ ∗ ∃ n : Nat,
        deferResp (f.[logFuture, go!"deferError"]) (futQ γ rc f d n) ∗ opTok γ d n)
      (lv.Type' = W8 4 ∧ d = [])
      iprop(⌜lv.Type' = W8 5⌝ ∗ deferResp (f.[logFuture, go!"deferError"]) cfgChangeQ)
    iapply wp_ncmod _ _ rfl (durFactL γ rc i (E := ⊤) (by solve_ndisj) s hbp)
    isplitl [Hsrv Hde]
    · iframe Hsrv; iframe #; iexact Hde
    iintro ⟨Hsrv, Hde⟩
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z sl.len by
      constructor <;> word)]
    wp_apply +noauto (wp_load_slice_index sl (sint.Z (W64 k)) fs dq f (by word)) $$ [$Hsl] with Hsl
    · ipureintro; rw [show (sint.Z (W64 (k : Int))).toNat = k by word]; exact Hf_lookup
    wp_pures; wp_load; wp_pures; wp_store; wp_pures; wp_store; wp_pures; wp_load; wp_pures; wp_load
    wp_bind (App (Val (GoInstruction (StructFieldRef _ _))) (Val _))
    iapply wp_go_step_receipt'
    case hv => exact isPanic_intoVal _
    inext
    iintro Hr1 Hlc1
    wp_auto
    ihave %Hlsllen := ownSlice_len $$ Hlsl
    have hdslen : ds.length = k := by
      have := congrArg List.length Hkds; simp at this; omega
    simp only [List.length_append, List.length_map, List.length_replicate, hdslen] at Hlsllen
    rw [if_pos (show 0 ≤ sint.Z (W64 (k : Int)) ∧ sint.Z (W64 (k : Int)) < sint.Z lsl.len by
      constructor <;> len)]
    ipersist Hlog
    wp_apply (wp_store_slice_index lsl (sint.Z (W64 k)) _ (f.[logFuture, go!"log"])) $$ [$Hlsl] with Hlsl
    · ipureintro; constructor <;> len
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType (go.GoType.PointerType logFuture.ty)))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := Loc) (t := go.GoType.PointerType logFuture.ty) [f]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %fsl ⟨Hfsl, -⟩
    wp_auto
    wp_apply (wp_slice_append (V := Loc)) $$ [$Hinfls $Hinflc $Hfsl] as %infl2 ⟨Hinfls, Hinflc, -⟩
    wp_for_post
    ihave Hrc := (receipt_add k 1).2 $$ [Hrc Hr1]
    · iframe
    iframe
    iexists (k + 1), ds ++ [⟨f, ⟨s.term, uint.nat lv.Type', d⟩⟩], lix + W64 1, infl2
    rw [show (sint.Z (W64 (k : Int))).toNat = k by word,
      set_snoc_rep _ fs.length k _ _ (by simp [hdslen]) hk]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]
    rw [show W64 (k : Int) + W64 1 = W64 ((k + 1 : Nat) : Int) by word]
    iframe
    isplitr
    · ipureintro
      refine ⟨?_, by omega, by word⟩
      rw [List.take_succ, ← Hkds, Hf_lookup]; simp
    iapply BigSepL.bigSepL_singleton.2
    rw [hdslen, Nat.zero_add]
    unfold dDone logPtr logIs
    simp only
    isplitr
    · iexists _; iframe; iframe #
      ipureintro; refine ⟨by word, by word, by simp⟩
    isplitr; · ipureintro; first | exact ⟨rfl, HK⟩ | exact ⟨trivial, HK⟩ | exact HK
    icases Hde with (⟨%Hty, Hde⟩ | ⟨%Hty, %n, Hde, Htok⟩ | ⟨%Hty, %sc, #Hbd, Hde⟩ | ⟨%Hty, Hde⟩)
    · isplitl [Hresp]; · iexists _; iexact Hresp
      ileft; rw [Hty]; iframe; ipureintro; rfl
    · isplitl [Hresp]; · iexists _; iexact Hresp
      iright; ileft; iexists n; rw [Hty]; iframe; ipureintro; rfl
    · isplitl [Hresp]; · iexists _; iexact Hresp
      iright; iright; ileft; iexists sc; iframe; iframe #; ipureintro; simp [Hty.1, kBarrier]
    · isplitl [Hresp]; · iexists _; iexact Hresp
      iright; iright; iright; rw [Hty]; iframe; ipureintro; rfl
  · obtain ⟨Hkds, Hkle, Hlix⟩ := Hk
    have hkn : k = fs.length := by word
    subst hkn
    have hds : ds.map DItem.f = fs := by rw [Hkds, List.take_length]
    have hdslen : ds.length = fs.length := by rw [← hds, List.length_map]
    rw [Nat.sub_self, List.replicate_zero, List.append_nil]
    wp_apply wp_getCommitIndex.1 $$ [$Hsrv $HInv $HcidxC $HdurI] as Hsrv
    wp_apply wp_tryStageCommitIndex $$ [$Hr $Hst] as ⟨%g', Hst, %Hg'⟩
    have hg' : uint.nat g' ≤ s.dur.1 := by
      rcases Hg' with h | h
      · subst h; have := Hcidx; have := Htlt; have := Hdurlen; have := Hloglt; word
      · subst h; exact Hg
    ihave #Hifs := isRaft_ifaces r γ rc i $$ Hr
    unfold raftIfaces
    icases Hifs with ⟨%logsI, %stableI, %snapsI, %transI, %fsmI, %rpcCh, %eof, #Hlogs, #HlogStore, -⟩
    unfold isLogStore
    icases HlogStore with ⟨-, -, -, #HSL, -, -⟩
    have hib := inflight_bound γ rc i s (⊤ \ ↑durN) gprotN_diff_durN fs0
    iapply wp_ncmod _ _ rfl (durFactL γ rc i (E := ⊤) (by solve_ndisj) s hib)
    isplitl [Hsrv Hfs0]
    · iframe Hsrv; iframe #; iexact Hfs0
    iintro ⟨Hsrv, Hfs0, %Hfs0b⟩
    ihave ⟨%Hes, #Hptrs, Htoks, Hresps⟩ := dDone_split γ rc i K s.term ds s.log.length $$ Hds
    iapply wp_ncmod _ _ rfl (append_bound_R γ rc i (E := ⊤) (by solve_ndisj) s fs.length)
    isplitl [Hsrv Hrc]; · iframe; iframe #
    iintro ⟨Hsrv, Hrc, %Hbound⟩
    wp_auto
    have hlen : (ds.map DItem.e).length = fs.length := by rw [List.length_map, hdslen]
    -- (hraft_robust) the leader's appends fire at `StoreLogs`' commit (`hwin`), the window lent till then
    rw [show fs.length = (ds.map DItem.e).length by rw [List.length_map, hdslen]] at Hbound
    rw [show fs.length = (ds.map DItem.e).length by rw [List.length_map, hdslen]]
    ihave Hwin := hwin (ds.map DItem.e) hlen Hes g' hg' $$ [Hsrv Hpw Hst Hrc Htoks HA]
    · iframe; iframe #
    iapply fupd_wp
    icases Hwin with ⟨>Hwin, Hau⟩
    imodintro
    wp_apply HSL $$ %lsl %(DFrac.own 1) %(ds.map (fun d => d.f.[logFuture, go!"log"]))
      %(s.log.length + 1) %(ds.map DItem.e) [] [$Hlsl] [] [Hwin]
    · ipureintro; exact ⟨by simp, by omega⟩
    · iexact Hptrs
    · iexact Hwin
    iintro Hwin Hnc
    imod Hau $$ Hwin Hnc with ⟨Hnc, Hau⟩
    imodintro
    iframe Hnc
    inext
    icases Hau with ⟨%A', HownL, Hcl⟩
    iexists A'
    iframe HownL
    iintro HownL
    imod Hcl $$ HownL with ⟨Hsrv, Hpw, Hst, #Hidx, HB⟩
    imodintro
    iintro Hlsl
    ihave #Himm := isRaft_imm r γ rc i $$ Hr
    unfold raftImm
    icases Himm with ⟨-, #HlocalID, -, -, -, -⟩
    iapply wp_ncmod _ _ rfl (ackLeader_R γ rc i (E := ⊤) (by solve_ndisj) _)
    isplitl [Hsrv]; · iframe; iframe #
    iintro ⟨Hsrv, #Hack⟩
    have Hlixeq : uint.nat lix = (s.log ++ ds.map DItem.e).length := by
      rw [List.length_append, List.length_map, hdslen]; exact Hlix
    wp_auto
    wp_apply (wp_match γ i s.term cm i lix) $$ [Hack]
    · iframe #; iright; ileft; rw [Hlixeq]; iexact Hack
    wp_apply (wp_setLastLog r γ rc i _ lix (W64 s.term)) $$ [$Hr $HlastLog] as HlastLog
    ihave ⟨#Hshared, Hstops⟩ := (replMain_split r γ i s.term rmap).1 $$ Hrmap
    wp_func_lits
    wp_bind (App (App (Val (map.forRange _ _)) _) _)
    iapply (wp_map_for_range (fun _ _ => iprop(∃ v : Loc, f_ptr ↦ v))) $$ Hrsm
    iintro %keys %hkeys
    isplitl [f]
    · iexists _; iframe
    isplitl []
    · imodintro
      iintro %_j %key %u ⟨%hk1, %hk2⟩ ⟨%v, Hf⟩
      ihave #Hsh := BigSepM.bigSepM_lookup hk2 $$ Hshared
      unfold replShared
      icases Hsh with ⟨%cm', %stopCh, %trig, %notif, %sd', %tde, %γs, -, -, -, -, -, -, -, -, -, #Htrig, #Htrign, -⟩
      unfold notifyChan
      icases Htrign with ⟨%γc, #Hbag⟩
      wp_auto
      wp_apply (wp_asyncNotifyCh γc trig (fun _ => iprop(True))) $$ [$Hbag]
      unfold forMapPostcondition
      iright; ileft
      isplit
      · ipureintro; rfl
      · iexists _; iframe
    iintro ⟨%v, Hf⟩ Hrsm
    wp_auto
    have hT : uint.nat (W64 (s.term : Int)) = s.term := by word
    have hesne : ds.map DItem.e ≠ [] := by
      intro h; apply Hne; rw [← hds]; simpa using h
    have hLT : lastTerm (s.log ++ ds.map DItem.e) = s.term :=
      lastTerm_append_ne _ _ _ hesne (fun e he => (Hes e he).1)
    have hsorted : ((fs0 ++ newItems (s.log.length + 1) ds).map InflightItem.k).Pairwise (· < ·) := by
      rw [List.map_append, newItems_k, List.pairwise_append]
      refine ⟨Hfs0, List.pairwise_lt_range', fun x hx y hy => ?_⟩
      obtain ⟨it, hit, rfl⟩ := List.mem_map.mp hx
      have := Hfs0b it hit
      rw [List.mem_range'] at hy
      omega
    rw [Hlixeq, hT]
    have hcov' : inflCover (fs0 ++ newItems (s.log.length + 1) ds) pb n0
        (s.log ++ ds.map DItem.e).length := by
      refine ⟨by have := Hpbc.1; simp only [List.length_append]; omega, fun x hx1 hx2 => ?_⟩
      rw [List.map_append, List.mem_append, newItems_k, List.mem_range']
      by_cases hxl : x ≤ s.log.length
      · left; exact Hpbc.2 x hx1 hxl
      · right
        simp only [List.length_append, List.length_map] at hx2
        refine ⟨x - (s.log.length + 1), by omega, by omega⟩
    ihave Hrmap := (replMain_split r γ i s.term rmap).2 $$ [Hstops]
    · iframe; iframe #
    ihave Hresps := newItems_res γ rc i s.term ds (s.log.length + 1) $$ [Hresps]
    · iframe; iframe #
    have hmap : ds.map (fun d => d.f.[logFuture, go!"log"]) = fs.map (fun q => q.[logFuture, go!"log"]) := by
      rw [← hds, List.map_map]; rfl
    rw [hmap]
    iapply HΦ
    iexists ds.map DItem.e
    isplitr; · ipureintro; first | exact ⟨hlen, Hes⟩ | exact ⟨rfl, Hes⟩
    iframe Hsrv Hpw HlastLog Happ Hsl HB Hptrs
    isplitl [Hst]; · iexists g'; iframe; ipureintro; exact hg'
    iexists cc, cm, infl', fs0 ++ newItems (s.log.length + 1) ds, rs, rmap, nt, sd, n0
    rw [List.map_append, newItems_f]
    iframe; iframe #
    ipureintro; exact ⟨hsorted, Hcov, hcov'⟩
end proof

end Perennial
