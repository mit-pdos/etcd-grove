/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: the pieces of `parReqB2.stmt`'s proof
(`node.parallel`'s request loop):
- `drain_peekB2`: node `j`'s B2 relation (`NodeOkD`) read from the run's invariant at its view;
- `pendFactsD_of`: the pending messages' facts out of it (unbatched);
- `bigSepL_frozenReq`: the `Ready`'s requests frozen, the other messages left owned;
- `req_absMsgOf`: a request (`isRequest`) has a protocol reading, an append or a heartbeat;
- `rMd_flags_b2`: B2's masked-off raft features off in the run's mask.
- `rMd_sync_b2`: synchronous storage and no batching in the run, from the mode.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2ParPhases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1SendWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Mono
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.SpecsB2
public import Spec.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.isRequest

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- **The pending messages' facts** out of `NodeOkD` (unbatched: `PendOk`). -/
theorem pendFactsD_of {R : AntSim.RunCfg} {dec : CCDec} {S : AntCheck.State} {net : List Msg}
    {j : Fin R.N} {v : AntSim.NodeView} (h : AntSim.NodeOkD R dec S net j v)
    (hbt : R.drv.batch = false) :
    ∀ q ∈ v.pend, AntSim.MsgMask R q ∧ AntSim.PendOk R.N (AntSim.nodeId j) v q :=
  fun q hq => ⟨(nodeOkD_facts h).2.2.2.2.2.2.1 q hq, h.2.2.2.2.2.2.2.2.2.2.1 hbt q hq⟩

/-- **A request has a protocol reading**: an append or a heartbeat (not a transfer message). -/
theorem req_absMsgOf {st : MsgSt} (hr : isRequestTy st.msg.Type' = true)
    (hax : (absMsgOf st).isSome ∨ (xmsgOf st).isSome) :
    ∃ q, absMsgOf st = some q ∧ AntSim.isReqM q = true := by
  rcases hax with h | h
  · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 h
    exact ⟨q, hq, by rw [isReqM_absMsgOf hq]; exact hr⟩
  · obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 h
    exfalso
    have ht := (xmsgOf_type hx).1
    unfold isRequestTy at hr
    rcases ht with h1 | h1 <;> rw [h1] at hr <;> revert hr <;> decide

/-- A request's reading is neither a proposal nor a snapshot. -/
theorem isReqM_ty {q : Msg} (h : AntSim.isReqM q = true) : q.ty ≠ .propose ∧ q.ty ≠ .snap := by
  unfold AntSim.isReqM at h
  have h' := of_decide_eq_true h
  rcases h' with h1 | h1 <;> rw [h1] <;> exact ⟨by decide, by decide⟩

/-- **B2's raft features off** (`DrainB2` over the run's mask, `ModeRun`). -/
theorem rMd_flags_b2 {s : H.Scope} {m : H.Mode} {R : AntSim.RunCfg} (hmr : ModeRun s m R)
    (hb2 : DrainB2 s m) :
    R.md.snapshots = false ∧ R.md.confChanges = false ∧ R.md.forwarding = false := by
  rw [hmr.2.2.2.2.1]
  obtain ⟨-, h1, h2, h3, -⟩ := hb2
  exact ⟨h1, h2, h3⟩

/-- **Synchronous storage and no batching in the run** (`ModeRun`: async storage and batching the
mode's). -/
theorem rMd_sync_b2 {s : H.Scope} {m : H.Mode} {R : AntSim.RunCfg} (hmr : ModeRun s m R)
    (has : m.Async' = false) (hbt : m.Batch' = false) :
    R.md.async = false ∧ R.drv.batch = false := by
  rw [hmr.2.2.2.2.1, hmr.2.2.2.2.2]
  exact ⟨has, hbt⟩

/-- `emit` on a dead node: nothing recorded, the fields kept. -/
theorem emitStep_dead (f : w64) : emitStep true f = (false, true, f) := by
  unfold emitStep; rfl

/-- `reportCause` on a dead node: the fields kept (recorded only with nothing to report). -/
theorem causeStep_dead (o : Option AntCheck.Event) (f : w64) :
    (causeStep o true f).2 = (true, f) := by
  unfold causeStep
  cases o <;> simp [emitStep_dead]

/-- `reportCause`'s outcome by whether a cause is pending. -/
theorem causeStep_isSome (o : Option AntCheck.Event) (b : Bool) (h : o.isSome = b) (d : Bool)
    (f : w64) : causeStep o d f = if b then emitStep d f else (true, d, f) := by
  unfold causeStep; rw [h]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- **(B2) Node `j`'s relation, read from the run's invariant** (`view_update.law` at `v' = v`):
some checker state and sent list at which node `j`, at its view `v`, is related (`NodeOkD`). -/
theorem drain_peekB2 (h_vu : view_update.law (GF := GF)) (c : Loc) (γ : AntNamesB2) (j : Fin γ.R.N)
    (q : Qp) (v : AntSim.NodeView) :
    antClusterB2 (GF := GF) c γ ∗ viewFrag γ.toAntNames j v ∗ runLive γ q ⊢
      |={⊤}=> ⌜∃ (S : AntCheck.State) (net : List Msg), AntSim.NodeOkD γ.R γ.dec S net j v⌝ ∗
        viewFrag γ.toAntNames j v ∗ runLive γ q := by
  iintro ⟨#Hc, Hv, Hl⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, -, -, -, -, -, -, -, -, -, #Hinv, %Hrf, -⟩
  iinv Hinv with >Hi Hclose
  iunfold antInvB2 at Hi
  icases Hi with (Hi | Hover)
  · iunfold antOpenB2 at Hi
    icases Hi with ⟨%evs, %S, %V, %net, %xnet, %G, Hstr, Hviews, Hnet, Hxnet, %Hpure, #HF⟩
    imod h_vu (⊤ \ ↑antN) γ.toAntNames j V v v $$ [Hv Hviews] with ⟨%HVj, Hv, Hviews⟩
    · iframe Hv Hviews
    rw [setV_self_s HVj]
    imod Hclose $$ [Hstr Hviews Hnet Hxnet] with -
    · inext
      iunfold antInvB2
      ileft
      iunfold antOpenB2
      iexists evs, S, V, net, xnet, G
      iframe Hstr Hviews Hnet Hxnet HF
      ipureintro; exact Hpure
    imodintro
    iframe Hv Hl
    ipureintro
    exact ⟨S, net, by rw [← HVj]; exact Hpure.1.2.1.2.2.2.2 j⟩
  · iexfalso
    iapply runLive_excl γ q
    iframe Hl Hover

/-- **The `Ready`'s requests frozen**, the other messages left owned. -/
theorem bigSepL_frozenReq : ∀ (L : List QMsg),
    ([∗list] m ∈ L, msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st) ⊢
      |==> [∗list] m ∈ L, if isRequestTy m.st.msg.Type' then frozenMsg (GF := GF) m.loc m.st
        else msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st
  | [] => by
    iintro -
    imodintro
    iapply (BigSepL.bigSepL_nil (Φ := fun _ (m : QMsg) => if isRequestTy m.st.msg.Type' then
      frozenMsg (GF := GF) m.loc m.st else msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st)).2
    iempintro
  | a :: L => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, Hl⟩
    imod bigSepL_frozenReq L $$ Hl with Hl
    iapply BigSepL.bigSepL_cons.2
    by_cases hr : isRequestTy a.st.msg.Type' = true
    · imod msgOwnZ_frozen _ _ _ $$ Ha with Ha
      imodintro
      simp only [hr, ↓reduceIte]
      iframe Ha Hl
    · imodintro
      simp only [hr, Bool.false_eq_true, ↓reduceIte]
      iframe Ha Hl

/-- After the loop: each request's frozen message is `msgPtsC` (`drainMsgsParB2`'s form). -/
theorem bigSepL_frozenReq_ptsC (L : List QMsg) :
    ([∗list] m ∈ L, if isRequestTy m.st.msg.Type' then frozenMsg (GF := GF) m.loc m.st
        else msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st) ⊢
      [∗list] m ∈ L, if isRequestTy m.st.msg.Type' then
        msgPtsC (GF := GF) m.loc DFrac.discard DFrac.discard false m.st
        else msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st := by
  apply BigSepL.bigSepL_mono
  intro _ m _
  by_cases hr : isRequestTy m.st.msg.Type' = true
  · simp only [hr, ↓reduceIte]; exact frozenMsg_ptsC _ _
  · simp only [hr, Bool.false_eq_true, ↓reduceIte]; exact .rfl

/-- The requests' frozen messages, kept apart as a persistent list. -/
theorem bigSepL_frozenReq_dup : ∀ (L : List QMsg),
    ([∗list] m ∈ L, if isRequestTy m.st.msg.Type' then frozenMsg (GF := GF) m.loc m.st
        else msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st) ⊢
      ([∗list] m ∈ L, if isRequestTy m.st.msg.Type' then frozenMsg (GF := GF) m.loc m.st
        else msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st) ∗
      □ [∗list] m ∈ L, if isRequestTy m.st.msg.Type' then frozenMsg (GF := GF) m.loc m.st else emp
  | [] => by
    iintro H
    iframe H
    imodintro
    iapply (BigSepL.bigSepL_nil (Φ := fun _ (m : QMsg) => if isRequestTy m.st.msg.Type' then
      frozenMsg (GF := GF) m.loc m.st else emp)).2
    iempintro
  | a :: L => by
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Ha, Hl⟩
    icases bigSepL_frozenReq_dup L $$ Hl with ⟨Hl, #Hp⟩
    by_cases hr : isRequestTy a.st.msg.Type' = true
    · simp only [hr, ↓reduceIte]
      icases Ha with #Ha
      isplitl [Hl]
      · iapply BigSepL.bigSepL_cons.2
        simp only [hr, ↓reduceIte]
        iframe Ha Hl
      · imodintro
        iapply BigSepL.bigSepL_cons.2
        simp only [hr, ↓reduceIte]
        iframe Ha Hp
    · simp only [hr, Bool.false_eq_true, ↓reduceIte]
      isplitl [Ha Hl]
      · iapply BigSepL.bigSepL_cons.2
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
        iframe Ha Hl
      · imodintro
        iapply BigSepL.bigSepL_cons.2
        simp only [hr, Bool.false_eq_true, ↓reduceIte]
        iframe Hp

end proof

section pure2
variable [GooseExts]

/-- `emit` on a live node that records: still alive. -/
theorem emitStep_rec {f : w64} (h : (emitStep false f).1 = true) : (emitStep false f).2.1 = false := by
  by_cases h1 : uint.Z f > 0 <;> by_cases h2 : f - W64 1 = W64 0 <;> simp_all [emitStep]

/-- `emit` on a live node that does not record: killed. -/
theorem emitStep_kill {f : w64} (h : (emitStep false f).1 = false) : (emitStep false f).2.1 = true := by
  by_cases h1 : uint.Z f > 0 <;> by_cases h2 : f - W64 1 = W64 0 <;> simp_all [emitStep]

theorem emitStep_dead1 (f : w64) : (emitStep true f).1 = false := by unfold emitStep; rfl
theorem emitStep_dead2 (f : w64) : (emitStep true f).2.1 = true := by unfold emitStep; rfl
theorem emitStep_dead3 (f : w64) : (emitStep true f).2.2 = f := by unfold emitStep; rfl
theorem causeStep_dead2 (o : Option AntCheck.Event) (f : w64) : (causeStep o true f).2.1 = true := by
  rw [causeStep_dead]
theorem causeStep_dead3 (o : Option AntCheck.Event) (f : w64) : (causeStep o true f).2.2 = f := by
  rw [causeStep_dead]

/-- A request is not a snapshot message. -/
theorem isRequestTy_ne_snap {t : w32} (h : isRequestTy t = true) : t ≠ MsgSnap := by
  intro hs; subst hs; revert h; decide

/-- A request's reading is pending at the loop's start. -/
theorem reqPend_mem0 {ms : List QMsg} {i : Nat} (hi : i < ms.length) {q : Msg}
    (hq : absMsgOf ms[i].st = some q) (hr : isRequestTy ms[i].st.msg.Type' = true) :
    q ∈ reqPend ms 0 := by
  unfold reqPend
  rw [List.drop_zero]
  exact List.mem_append_left _
    (List.mem_filterMap.2 ⟨ms[i], List.mem_filter.2 ⟨List.getElem_mem hi, hr⟩, hq⟩)

/-- **The request loop's pure invariant** after the first `i` messages: dead once dead, the sent
lists' lower bounds grown, and the view `v₁` but for its pending messages (alive: `reqPend … i`),
`told` (set or kept) and the undo record (kept, or none and made). -/
def ParInvB2 (v₁ : AntSim.NodeView) (net₁ : List Msg) (xnet₁ : List XMsg) (dead : Bool)
    (ms : List QMsg) (i : Nat) (dd : Bool) (vv : AntSim.NodeView) (net : List Msg)
    (xnet : List XMsg) : Prop :=
  (dead = true → dd = true) ∧ net₁ <+: net ∧ xnet₁ <+: xnet ∧
    (∃ (P : List Msg) (T : Bool) (U : Option AntSim.DurW) (M : Bool),
      vv = { v₁ with pend := P, told := T, undo := U, made := M } ∧
      ((U = v₁.undo ∧ M = v₁.made) ∨ (U = none ∧ M = true)) ∧ (T = v₁.told ∨ T = true) ∧
      (dd = false → P = reqPend ms i))

/-- A message that is no request: nothing changes but the index. -/
theorem parInvB2_other {v₁ : AntSim.NodeView} {net₁ : List Msg} {xnet₁ : List XMsg} {dead : Bool}
    {ms : List QMsg} {i : Nat} {dd : Bool} {vv : AntSim.NodeView} {net : List Msg}
    {xnet : List XMsg} (hi : i < ms.length) (hr : isRequestTy ms[i].st.msg.Type' = false)
    (h : ParInvB2 v₁ net₁ xnet₁ dead ms i dd vv net xnet) :
    ParInvB2 v₁ net₁ xnet₁ dead ms (i + 1) dd vv net xnet := by
  obtain ⟨hd, hn, hx, P, T, U, M, hv, hum, ht, hp⟩ := h
  exact ⟨hd, hn, hx, P, T, U, M, hv, hum, ht, fun h0 => (hp h0).trans (reqPend_succ_other hi hr)⟩

/-- Dead after the `i`th message, the view and lists kept. -/
theorem parInvB2_dead {v₁ : AntSim.NodeView} {net₁ : List Msg} {xnet₁ : List XMsg} {dead : Bool}
    {ms : List QMsg} {i : Nat} {dd : Bool} {vv : AntSim.NodeView} {net : List Msg}
    {xnet : List XMsg} (h : ParInvB2 v₁ net₁ xnet₁ dead ms i dd vv net xnet) :
    ParInvB2 v₁ net₁ xnet₁ dead ms (i + 1) true vv net xnet := by
  obtain ⟨-, hn, hx, P, T, U, M, hv, hum, ht, -⟩ := h
  exact ⟨fun _ => rfl, hn, hx, P, T, U, M, hv, hum, ht, fun h0 => by cases h0⟩

/-- `told` set by the cause's report (or kept): still within the invariant's shape. -/
theorem told_ok {v₁ vv : AntSim.NodeView} {P : List Msg} {T : Bool} {U : Option AntSim.DurW}
    {M : Bool} (hv : vv = { v₁ with pend := P, told := T, undo := U, made := M })
    (ht : T = v₁.told ∨ T = true) {b : Bool} (hb : b = vv.told ∨ b = true) :
    b = v₁.told ∨ b = true := by
  subst hv
  rcases hb with hb | hb
  · rw [hb]; exact ht
  · exact .inr hb

end pure2

section proof2
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

/-- A message's content form keeps its unknown fields' certificate (persistent). -/
theorem msgPtsCC_pb (l : Loc) (dq dqe : DFrac) (cap : Bool) (c : MsgC) :
    msgPtsCC (GF := GF) l dq dqe cap c ⊢
      msgPtsCC l dq dqe cap c ∗ pbMsg raftpb.Message l c.f.uf := by
  unfold msgPtsCC
  iintro ⟨%pty, %pto, %pfr, %pte, %plt, %pix, %pco, %pvo, %prj, %prh, %es, %els, %ps, %cs,
    %rsl, %Hnn, HTy, #cTy, HTo, #cTo, HFr, #cFr, HTe, #cTe, HLt, #cLt, HIx, #cIx, HCo, #cCo,
    HVo, #cVo, HRj, #cRj, HRh, #cRh, HEs, Hes, #Hents, Hcap, HSn, Hsn, HCx, #Hcx, HRs, Hrs, #Hp⟩
  isplitl
  · iexists pty, pto, pfr, pte, plt, pix, pco, pvo, prj, prh, es, els, ps, cs, rsl
    isplitr
    · ipureintro; exact Hnn
    iframe
    iframe cTy cTo cFr cTe cLt cIx cCo cVo cRj cRh Hents Hcx Hp
  · iexact Hp

/-- **A message raft handed out, read through today's form** (at its fraction, for `isRequest`),
and given back. -/
theorem msgOwnZ_ptsC_wand (l : Loc) (dq : DFrac) (st : MsgSt) :
    msgOwnZ (GF := GF) false l dq st ⊢ msgPtsC l dq DFrac.discard false st ∗
      (msgPtsC l dq DFrac.discard false st -∗ msgOwnZ false l dq st) := by
  unfold msgOwnZ
  iintro ⟨%c, Hc, %H⟩
  obtain ⟨rfl, hok⟩ := H
  icases msgPtsCC_pb l dq DFrac.discard false c $$ Hc with ⟨Hc, #Hp⟩
  ihave Hc := msgPtsCC_msgPtsC l dq DFrac.discard false c hok.1.1 $$ Hc
  iframe Hc
  iintro H2
  icases msgPtsC_msgPtsCC_uf l dq DFrac.discard false c.model c.f.uf $$ [$H2 $Hp] with
    ⟨%c', Hc', %H'⟩
  iexists c'
  iframe Hc'
  ipureintro
  obtain ⟨hm, hcs, huf⟩ := H'
  have hmm : c'.f.msgM = c.f.msgM := congrArg MsgSt.msg hm
  refine ⟨hm, ⟨hcs, fun ht => ?_⟩, fun h => by cases h⟩
  rw [huf]; exact hok.1.2 (hmm ▸ ht)

theorem ite_true_ent {P Q : IProp GF} {b : Bool} (h : b = true) : (if b then P else Q) ⊢ P := by
  subst h; exact .rfl

theorem ite_false_ent {P Q : IProp GF} {b : Bool} (h : b = false) : (if b then P else Q) ⊢ Q := by
  subst h; exact .rfl

theorem ite_true_intro {P Q : IProp GF} {b : Bool} (h : b = true) : P ⊢ (if b then P else Q) := by
  subst h; exact .rfl

theorem ite_false_intro {P Q : IProp GF} {b : Bool} (h : b = false) : Q ⊢ (if b then P else Q) := by
  subst h; exact .rfl

theorem parCauseB2_dead_null (γ : AntNamesB2) (j : Fin γ.R.N) (v : AntSim.NodeView) (net : List Msg)
    (xnet : List XMsg) : ⊢ parCauseB2 (GF := GF) γ j true v null net xnet := by
  unfold parCauseB2
  simp only [↓reduceIte]
  iexists none
  iunfold pendingCause
  ileft
  ipureintro; exact ⟨rfl, rfl⟩

theorem parCauseB2_dead (γ : AntNamesB2) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc)
    (net : List Msg) (xnet : List XMsg) :
    parCauseB2 (GF := GF) γ j true v cl net xnet ⊢ ∃ o : Option AntCheck.Event, pendingCause cl o := by
  unfold parCauseB2
  simp only [↓reduceIte]
  exact .rfl

theorem parCauseB2_alive (γ : AntNamesB2) (j : Fin γ.R.N) (v : AntSim.NodeView) (cl : Loc)
    (net : List Msg) (xnet : List XMsg) :
    parCauseB2 (GF := GF) γ j false v cl net xnet ⊣⊢
      causeOwn γ.toAntNames j v cl ∗ sentLb γ.toAntNames net ∗ xsentLb γ.toAntNames xnet := by
  unfold parCauseB2
  simp only [Bool.false_eq_true, ↓reduceIte]
  exact .rfl

/-- `reportCause` on a dead node asks for nothing. -/
theorem causeDead_pre (γr : GName) (o : Option AntCheck.Event) (f : w64) (g : AntCheck.Event → AntCheck.Event) :
    ⊢ if (causeStep o true f).1 then reports (GF := GF) γr (o.toList.map g) emp else emp := by
  cases o with
  | none => simp only [causeStep, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
      Option.toList_none, List.map_nil, reports]; iempintro
  | some e => simp only [causeStep, Option.isSome_some, ↓reduceIte, emitStep_dead,
      Bool.false_eq_true]; iempintro

/-- What the cause's report gives back to the request loop (`causeOwn_reportB2`'s `Φ`). -/
def parCauseQ (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (vv : AntSim.NodeView) (net : List Msg)
    (xnet : List XMsg) : IProp GF :=
  iprop(∃ (b : Bool) (net₂ : List Msg) (xnet₂ : List XMsg),
    ⌜(vv.byE = go!"recv" → b = true) ∧ (b = vv.told ∨ b = true) ∧ net <+: net₂ ∧ xnet <+: xnet₂⌝ ∗
    sentLb γ.toAntNames net₂ ∗ xsentLb γ.toAntNames xnet₂ ∗
    viewFrag γ.toAntNames j { vv with told := b } ∗ runLive γ q)

/-- What a request's `send` report gives back (`report_updB2`'s `Φ`). -/
def parSendQ (γ : AntNamesB2) (j : Fin γ.R.N) (q : Qp) (v' : AntSim.NodeView) (net₂ : List Msg)
    (xnet₂ : List XMsg) (add : List Msg) : IProp GF :=
  iprop(viewFrag γ.toAntNames j v' ∗ runLive γ q ∗
    (∃ (net : List Msg) (xnet : List XMsg), sentLb γ.toAntNames net ∗ xsentLb γ.toAntNames xnet ∗
      ⌜net₂ <+: net ∧ (∀ m ∈ add, m ∈ net) ∧ xnet₂ <+: xnet ∧ ∀ y ∈ ([] : List XMsg), y ∈ xnet⌝))

/-- **The request loop's invariant** (`parReqB2`'s, after the first `i` messages; `mp` the loop
variable's cell): the locals, the kill fields, the cause cell, the view's fragment, the requests
frozen and the others owned, the run's liveness share and the network's adder. -/
def parLoopB2 (np rdp bp c n : Loc) (γ : AntNamesB2) (j : Fin γ.R.N) (I : DrainIterB1)
    (v₁ : AntSim.NodeView) (net₁ : List Msg) (xnet₁ : List XMsg) (dead : Bool) (q : Qp) (mp : Loc)
    (i : Nat) : IProp GF :=
  iprop(∃ (dd : Bool) (ff : w64) (cc : Loc) (vv : AntSim.NodeView) (net : List Msg)
      (xnet : List XMsg) (x : Loc),
    np ↦ n ∗ bp ↦ I.v.byE ∗ rdp ↦ I.rd ∗ killOwn n dd ff ∗ n.[H.node, go!"cause"] ↦ cc ∗
    viewFrag γ.toAntNames j vv ∗ parCauseB2 γ j dd vv cc net xnet ∗
    ⌜ParInvB2 v₁ net₁ xnet₁ dead I.ms i dd vv net xnet⌝ ∗ mp ↦ x ∗
    ([∗list] m ∈ I.ms, if isRequestTy m.st.msg.Type' then frozenMsg m.loc m.st
      else msgOwnZ false m.loc (readyDq m.st) m.st) ∗
    runLive γ q ∗ netAdder c γ.toAntNames q ∗ threadTok)

end proof2

attribute [-instance] pure_wp_slice_for_range

section par
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [StorageModel GF]
variable [AntStor GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Assumptions]
variable [check_sem : github_com.mit_pdos.etcd_grove.examples.raft.antithesis.check.Assumptions]

set_option maxHeartbeats 8000000 in
/-- **`parReqB2.stmt`**: the range loop at `parLoopB2`. -/
theorem parReqB2
    (h_vu : view_update.law (GF := GF))
    (h_tlp : rnTermLB_persistent.law (GF := GF) (hG := hG))
    (h_le : rnTermLB_le.law (GF := GF) (hG := hG))
    (wp_isRequest : isRequest.spec (GF := GF) (hG := hG))
    (wp_reportCause : node.reportCause.specB2 (GF := GF) (hG := hG))
    (wp_sendEv : node.sendEv.specB2 (GF := GF) (hG := hG))
    (wp_emit : node.emit.specB2 (GF := GF) (hG := hG))
    (wp_sendMsg : node.sendMsg.specB2 (GF := GF) (hG := hG)) :
    parReqB2.stmt (GF := GF) (hG := hG) := by
  intro hTB np rdp bp c n γ j I msk v₁ net₁ xnet₁ dead fuse cl qp K Φ hmsk hinm has hbt hok hnorm hal
  haveI := h_tlp γ.raft I.rs.tc
  iintro ⟨#Hpkg, #Hc, #Hn, %Hb2, Hnp, Hbp, Hrdp, Hk, Hcl, Hvf, Hpc, #Htlb, Hsl, Hcap, Hown, #Hrm,
    %Hmok, Hl, Hadd, Htt, HΦ⟩
  ihave #Hc' := Hc
  iunfold antClusterB2 at Hc'
  icases Hc' with ⟨%cfg, %r, %ns, %stop, -, -, %Hmode, -⟩
  obtain ⟨hs, hcc, hfw⟩ := rMd_flags_b2 Hmode.2 Hb2
  obtain ⟨hasR, hbtR⟩ := rMd_sync_b2 Hmode.2 has hbt
  have hss : γ.mode.SnapStatus' = false := Hb2.1
  -- the pending messages' facts at `v₁`
  imod drain_peekB2 h_vu c γ j qp v₁ $$ [$Hc $Hvf $Hl] with ⟨%Hpk, Hvf, Hl⟩
  obtain ⟨S₀, netS, hok0⟩ := Hpk
  have hpk := pendFactsD_of hok0 hbtR
  -- the requests frozen
  imod bigSepL_frozenReq I.ms $$ Hown with Hfz
  icases bigSepL_frozenReq_dup I.ms $$ Hfz with ⟨Hfz, #Hfp⟩
  obtain ⟨-, -, -, -, -, -, hax, -, -, -, htc, -, -⟩ := hok
  unfold github_com.mit_pdos.etcd_grove.examples.raft.antithesis.node.parallel.reqE
  icases typedPointsto_not_null_dup _ _ _ $$ Hrdp with ⟨Hrdp, %Hrnn⟩
  iStructNamed Hrdp
  wp_pure
  wp_auto
  ihave Hrdp : (rdp ↦ I.rd : IProp GF) $$ [SoftState HardState ReadStates Entries Snapshot
      CommittedEntries Messages MustSync]
  · iapply typedPointsto_combine _ _ _ Hrnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  wp_apply (wp_slice_range_ro (V := Loc) _ I.rd.Messages' (I.ms.map QMsg.loc) (DFrac.own 1) _
    (parLoopB2 np rdp bp c n γ j I v₁ net₁ xnet₁ dead qp m_ptr))
    $$ Hsl [Hnp Hbp Hrdp Hk Hcl Hvf Hpc m Hfz Hl Hadd Htt]
  · iunfold parLoopB2
    iexists dead, fuse, cl, v₁, net₁, xnet₁, _
    iframe Hnp Hbp Hrdp Hk Hcl Hvf Hpc m Hfz Hl Hadd Htt
    ipureintro
    exact ⟨fun h => h, List.prefix_refl _, List.prefix_refl _, v₁.pend, v₁.told, v₁.undo, v₁.made,
      rfl, .inl ⟨rfl, rfl⟩, .inl rfl, fun h => (hal h).1⟩
  · imodintro
    iintro %i %x %hx HP Hs
    iunfold parLoopB2 at HP
    icases HP with ⟨%dd, %ff, %cc, %vv, %net, %xnet, %x0, Hnp, Hbp, Hrdp, Hk, Hcl, Hvf, Hpc, %Hinv,
      Hm, Hfz, Hl, Hadd, Htt⟩
    have hi : i < I.ms.length := by
      have := (List.getElem?_eq_some_iff.1 hx).1; simpa using this
    have hxe : x = I.ms[i].loc := by
      rw [List.getElem?_map, List.getElem?_eq_getElem hi] at hx
      exact (Option.some.inj hx).symm
    subst hxe
    have hmem : I.ms[i] ∈ I.ms := List.getElem_mem hi
    obtain ⟨hT, hN, hS⟩ := Hmok I.ms[i] hmem
    have hterm : uint.Z I.ms[i].st.msg.Term' < 2 ^ 61 := by omega
    ihave #Hrq := BigSepL.bigSepL_lookup (Φ := fun _ q => isRaftMsg (GF := GF) γ.raft.raftNames
      (AntSim.nodeId j) q.st) (List.getElem?_eq_getElem hi) $$ Hrm
    ihave %Hsent := isRaftMsg_shape_s γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st $$ Hrq
    ihave %Hres := isRaftMsg_resps γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st $$ Hrq
    wp_auto
    by_cases hr : isRequestTy I.ms[i].st.msg.Type' = true
    · -- a request
      ihave #Hfq0 := BigSepL.bigSepL_lookup (Φ := fun _ (m : QMsg) => if isRequestTy m.st.msg.Type'
        then frozenMsg (GF := GF) m.loc m.st else emp) (List.getElem?_eq_getElem hi) $$ Hfp
      ihave #Hfq := ite_true_ent hr $$ Hfq0
      ihave HpC := frozenMsg_ptsC _ _ $$ Hfq
      wp_apply wp_isRequest I.ms[i].loc DFrac.discard DFrac.discard false I.ms[i].st
        $$ [$Hpkg $HpC] as -
      rw [hr]
      obtain ⟨q, habs, hrq⟩ := req_absMsgOf hr (hax _ hmem)
      have hns : q.ty ≠ .snap := (isReqM_ty hrq).2
      have hprop : q.ty ≠ .propose := (isReqM_ty hrq).1
      have hnsT : I.ms[i].st.msg.Type' ≠ MsgSnap := isRequestTy_ne_snap hr
      have hnorm' : AllNormal I.ms[i].st.ents := hnorm _ hmem hr
      have hnums := hN q habs
      wp_auto
      rcases dd with _ | _
      · -- alive
        have Hinv0 := Hinv
        have hdead : dead = false := by
          cases hd : dead
          · rfl
          · exact absurd (Hinv.1 hd) (by decide)
        obtain ⟨hp1, hparts, hby⟩ := hal hdead
        obtain ⟨-, hn, hx, P, T, U, M, hvv, hUM, hTT, hP⟩ := Hinv
        have hPi := hP rfl
        have hq0 : q ∈ v₁.pend := hp1 ▸ reqPend_mem0 hi habs hr
        obtain ⟨hmq, hpq⟩ := hpk q hq0
        have hrest := reqPend_succ_req hi habs hr
        have hvby : vv.byE = I.v.byE := by rw [hvv]; exact hby
        have hvparts : vv.parts = [] := by rw [hvv]; exact hparts
        icases (parCauseB2_alive γ j vv cc net xnet).1 $$ Hpc with ⟨Hco, #Hlb, #Hxlb⟩
        by_cases hrec : (if decide (vv.byE = go!"recv" ∧ vv.told = false) then emitStep false ff
            else (true, false, ff)).1 = true
        · -- the cause reported (or none to report)
          ihave Hrep := causeOwn_reportB2 h_vu msk hmsk c γ j qp vv net xnet cc
            (parCauseQ γ j qp vv net xnet) hbtR hinm $$ [Hco Hvf Hl]
          · iframe Hc Hlb Hxlb Hco Hvf Hl
            iintro %b %net₂ %xnet₂ %Hb Hlb2 Hxlb2 Hvf Hl
            iunfold parCauseQ
            iexists b, net₂, xnet₂
            iframe Hlb2 Hxlb2 Hvf Hl
            ipureintro; exact Hb
          icases Hrep with ⟨%o, Hpco, %Ho, Hrep⟩
          have hcs := causeStep_isSome o _ Ho false ff
          have hc1 : (causeStep o false ff).1 = true := by rw [hcs]; exact hrec
          have hc2 : (causeStep o false ff).2.1 = false := by
            rw [hcs]
            cases hb : decide (vv.byE = go!"recv" ∧ vv.told = false) <;> simp [hb] at hrec ⊢
            exact emitStep_rec hrec
          ihave Hpre : (if (causeStep o false ff).1 then reports γ.strm
              (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) (parCauseQ γ j qp vv net xnet)
              else emp) $$ [Hrep]
          · iapply ite_true_intro hc1
            iexact Hrep
          wp_apply +noauto wp_reportCause c γ n j cc o (parCauseQ γ j qp vv net xnet) false ff
            $$ [$Hpkg $Hc $Hn $Hk $Hcl $Hpco $Hpre] as ⟨Hk, Hcl, HQ⟩
          ihave HQ := ite_true_ent hc1 $$ HQ
          rw [hc2]
          generalize (causeStep o false ff).2.2 = ff2
          iunfold parCauseQ at HQ
          icases HQ with ⟨%b, %net₂, %xnet₂, %Hb, #Hlb2, #Hxlb2, Hvf, Hl⟩
          wp_take_receipt as Hr2
          wp_apply +noauto wp_sendEv c γ n j I.v.byE I.ms[i].loc DFrac.discard DFrac.discard false
            I.ms[i].st hnsT hnorm' $$ [$Hpkg $Hc $Hn $HpC] as %p ⟨-, Hev, Hr3⟩
          wp_take_receipt as Hr4
          by_cases hrec2 : (emitStep false ff2).1 = true
          · -- the request's report recorded
            have hvb : ({ vv with told := b } : AntSim.NodeView).byE = I.v.byE := hvby
            have htold : AntSim.Told ({ vv with told := b } : AntSim.NodeView) := fun h => Hb.1 h
            have hpend' : ({ vv with told := b } : AntSim.NodeView).pend = q :: reqPend I.ms (i + 1) := by
              show vv.pend = _
              rw [hvv]; exact hPi.trans hrest
            ihave #Hmsg := isRaftMsg_isMessage_s γ.raft.raftNames (AntSim.nodeId j) I.ms[i].st q habs hns
              $$ Hrq
            ihave #Hext := sendExt_b1 γ.toAntNames q $$ Hmsg
            ihave Hrc : ⧗ (AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE
                q).weight $$ [Hr2 Hr3 Hr4]
            · rw [evSend_weight habs hns]
              iapply (receipt_add (GF := GF) (I.ms[i].st.ents.length + 1) 1).2
              iframe Hr4
              iapply (receipt_add (GF := GF) I.ms[i].st.ents.length 1).2
              iframe Hr3 Hr2
            ihave Hrep := report_updB2 h_vu c γ j qp { vv with told := b }
              (sendView { vv with told := b } (reqPend I.ms (i + 1)))
              (AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE q)
              net₂ [q] xnet₂ [] (fun G0 G => FactsLe γ.R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.MsgFacts G q)
              (parSendQ γ j qp (sendView { vv with told := b } (reqPend I.ms (i + 1))) net₂ xnet₂ [q])
              (evSend_numsOk habs hns hnums hterm _ _) (evSend_chgOk _ _ _)
              (sendHstepD msk hmsk j _ q _ net₂ xnet₂ hinm hasR hbtR hpend' htold (fun _ => hnums)
                hvparts (.inr hrq)) $$ [Hvf Hl Hrc]
            · iframe Hc Hlb2 Hxlb2 Hext Hrc Hvf Hl
              iintro H
              iunfold parSendQ
              iexact H
            have hev : atNode (AntSim.nameOf (AntSim.nodeId j)) (sendEvM I.v.byE I.ms[i].st) =
                AntSim.evSend (AntSim.nodeId j) ({ vv with told := b } : AntSim.NodeView).byE q := by
              rw [hvb]; exact sendEvM_abs habs hns hnums hterm _ _
            ihave Hpre2 : (if (emitStep false ff2).1 then reports γ.strm
                [atNode (AntSim.nameOf (AntSim.nodeId j)) (sendEvM I.v.byE I.ms[i].st)]
                (parSendQ γ j qp (sendView { vv with told := b } (reqPend I.ms (i + 1))) net₂ xnet₂ [q])
                else emp) $$ [Hrep]
            · iapply ite_true_intro hrec2
              rw [hev]
              iexact Hrep
            wp_apply +noauto wp_emit c γ n j p (sendEvM I.v.byE I.ms[i].st)
              (parSendQ γ j qp (sendView { vv with told := b } (reqPend I.ms (i + 1))) net₂ xnet₂ [q])
              false ff2 $$ [$Hpkg $Hc $Hn $Hk $Hev $Hpre2] as %b' ⟨Hk, %Hb', HQ⟩
            subst Hb'
            ihave HQ := ite_true_ent hrec2 $$ HQ
            rw [emitStep_rec hrec2]
            generalize (emitStep false ff2).2.2 = ff3
            iunfold parSendQ at HQ
            icases HQ with ⟨Hvf, Hl, %net₃, %xnet₃, #Hlb3, #Hxlb3, %Hn3⟩
            haveI := h_tlp γ.raft I.ms[i].st.msg.Term'
            ihave #Htq := h_le γ.raft I.rs.tc I.ms[i].st.msg.Term' hT $$ Htlb
            ihave Hsf : (⌜false = true⌝ ∨ sendFacts (GF := GF) γ.toAntNames I.ms[i].st) $$ []
            · iright
              iapply sendFacts_of γ.toAntNames (AntSim.nodeId j) I.ms[i].st q habs hns
                (netFacts_of_pend habs hmq hpq hprop Hsent hnums hterm hs hfw hcc)
              iframe Hrq Htq
              iapply sentW_of_lb γ.toAntNames net₃ q (Hn3.2.1 q List.mem_cons_self)
              iexact Hlb3
            try wp_auto
            wp_apply wp_sendMsg c γ n j I.ms[i].loc false I.ms[i].st qp false ff3
              $$ [$Hpkg $Hc $Hn $Hk $Hadd $Htt $HpC $Hsf] as ⟨Hk, Hadd, Htt, -⟩
            · ipureintro; exact ⟨hss, Hres⟩
            isplitr
            · ipureintro; rfl
            iframe Hs
            ihave Hco := causeOwn_told (GF := GF) γ.toAntNames j
              (sendView { vv with told := b } (reqPend I.ms (i + 1))) Hb.1
            iunfold parLoopB2
            iexists false, ff3, null, sendView { vv with told := b } (reqPend I.ms (i + 1)), net₃, xnet₃,
              I.ms[i].loc
            iframe Hnp Hbp Hrdp Hk Hcl Hvf Hm Hfz Hl Hadd Htt
            isplitl [Hco]
            · iapply (parCauseB2_alive γ j _ null net₃ xnet₃).2
              iframe Hco Hlb3 Hxlb3
            ipureintro
            refine ⟨(fun h => by rw [hdead] at h; cases h), hn.trans (Hb.2.2.1.trans Hn3.1),
              hx.trans (Hb.2.2.2.trans Hn3.2.2.1), reqPend I.ms (i + 1), b, none, true, ?_,
              .inr ⟨rfl, rfl⟩, told_ok hvv hTT Hb.2.1, fun _ => rfl⟩
            rw [hvv]
          · -- `emit`'s fuse kills
            have hrec2' : (emitStep false ff2).1 = false := by simpa using hrec2
            ihave Hpre2 : (if (emitStep false ff2).1 then reports γ.strm
                [atNode (AntSim.nameOf (AntSim.nodeId j)) (sendEvM I.v.byE I.ms[i].st)] (emp : IProp GF)
                else emp) $$ []
            · iapply ite_false_intro hrec2'
              iempintro
            wp_apply +noauto wp_emit c γ n j p (sendEvM I.v.byE I.ms[i].st) emp false ff2
              $$ [$Hpkg $Hc $Hn $Hk $Hev $Hpre2] as %b' ⟨Hk, -, -⟩
            rw [emitStep_kill hrec2']
            generalize (emitStep false ff2).2.2 = ff3
            ihave Hsf : (⌜true = true⌝ ∨ sendFacts (GF := GF) γ.toAntNames I.ms[i].st) $$ []
            · ileft; ipureintro; rfl
            try wp_auto
            wp_apply wp_sendMsg c γ n j I.ms[i].loc false I.ms[i].st qp true ff3
              $$ [$Hpkg $Hc $Hn $Hk $Hadd $Htt $HpC $Hsf] as ⟨Hk, Hadd, Htt, -⟩
            · ipureintro; exact ⟨hss, Hres⟩
            isplitr
            · ipureintro; rfl
            iframe Hs
            iunfold parLoopB2
            iexists true, ff3, null, { vv with told := b }, net₂, xnet₂, I.ms[i].loc
            iframe Hnp Hbp Hrdp Hk Hcl Hvf Hm Hfz Hl Hadd Htt
            isplitr
            · iapply (parCauseB2_dead_null (GF := GF) γ j { vv with told := b } net₂ xnet₂)
            ipureintro
            refine ⟨fun _ => rfl, hn.trans Hb.2.2.1, hx.trans Hb.2.2.2, P, b, U, M, ?_, hUM,
              told_ok hvv hTT Hb.2.1, fun h => by cases h⟩
            rw [hvv]
        · -- the cause's report kills
          icases causeOwn_pendingB2 γ.toAntNames j vv cc $$ Hco with ⟨%o, Hpco, %Ho⟩
          have hcs := causeStep_isSome o _ Ho false ff
          have hc1 : (causeStep o false ff).1 = false := by rw [hcs]; simpa using hrec
          have hc2 : (causeStep o false ff).2.1 = true := by
            rw [hcs]
            cases hb : decide (vv.byE = go!"recv" ∧ vv.told = false) <;> simp [hb] at hrec ⊢
            exact emitStep_kill hrec
          ihave Hpre : (if (causeStep o false ff).1 then reports γ.strm
              (o.toList.map (atNode (AntSim.nameOf (AntSim.nodeId j)))) (emp : IProp GF)
              else emp) $$ []
          · iapply ite_false_intro hc1
            iempintro
          wp_apply +noauto wp_reportCause c γ n j cc o emp false ff
            $$ [$Hpkg $Hc $Hn $Hk $Hcl $Hpco $Hpre] as ⟨Hk, Hcl, -⟩
          rw [hc2]
          generalize (causeStep o false ff).2.2 = ff2
          wp_auto
          wp_apply +noauto wp_sendEv c γ n j I.v.byE I.ms[i].loc DFrac.discard DFrac.discard false
            I.ms[i].st hnsT hnorm' $$ [$Hpkg $Hc $Hn $HpC] as %p ⟨-, Hev, -⟩
          ihave Hpre2 : (if (emitStep true ff2).1 then reports γ.strm
              [atNode (AntSim.nameOf (AntSim.nodeId j)) (sendEvM I.v.byE I.ms[i].st)] (emp : IProp GF)
              else emp) $$ []
          · iapply ite_false_intro (emitStep_dead1 ff2)
            iempintro
          wp_auto
          wp_apply +noauto wp_emit c γ n j p (sendEvM I.v.byE I.ms[i].st) emp true ff2
            $$ [$Hpkg $Hc $Hn $Hk $Hev $Hpre2] as %b' ⟨Hk, -, -⟩
          try rw [emitStep_dead2, emitStep_dead3]
          ihave Hsf : (⌜true = true⌝ ∨ sendFacts (GF := GF) γ.toAntNames I.ms[i].st) $$ []
          · ileft; ipureintro; rfl
          try wp_auto
          wp_apply wp_sendMsg c γ n j I.ms[i].loc false I.ms[i].st qp true ff2
            $$ [$Hpkg $Hc $Hn $Hk $Hadd $Htt $HpC $Hsf] as ⟨Hk, Hadd, Htt, -⟩
          · ipureintro; exact ⟨hss, Hres⟩
          isplitr
          · ipureintro; rfl
          iframe Hs
          iunfold parLoopB2
          iexists true, ff2, null, vv, net, xnet, I.ms[i].loc
          iframe Hnp Hbp Hrdp Hk Hcl Hvf Hm Hfz Hl Hadd Htt
          isplitr
          · iapply (parCauseB2_dead_null (GF := GF) γ j vv net xnet)
          ipureintro; exact parInvB2_dead Hinv0
      · -- dead
        icases parCauseB2_dead γ j vv cc net xnet $$ Hpc with ⟨%o, Hpco⟩
        ihave Hpre := causeDead_pre (GF := GF) γ.strm o ff (atNode (AntSim.nameOf (AntSim.nodeId j)))
        wp_apply +noauto wp_reportCause c γ n j cc o emp true ff
          $$ [$Hpkg $Hc $Hn $Hk $Hcl $Hpco $Hpre] as ⟨Hk, Hcl, -⟩
        rw [causeStep_dead2, causeStep_dead3]
        wp_auto
        wp_apply +noauto wp_sendEv c γ n j I.v.byE I.ms[i].loc DFrac.discard DFrac.discard false
          I.ms[i].st hnsT hnorm' $$ [$Hpkg $Hc $Hn $HpC] as %p ⟨-, Hev, -⟩
        ihave Hpre2 : (if (emitStep true ff).1 then reports γ.strm
            [atNode (AntSim.nameOf (AntSim.nodeId j)) (sendEvM I.v.byE I.ms[i].st)] (emp : IProp GF)
            else emp) $$ []
        · iapply ite_false_intro (emitStep_dead1 ff)
          iempintro
        wp_auto
        wp_apply +noauto wp_emit c γ n j p (sendEvM I.v.byE I.ms[i].st) emp true ff
          $$ [$Hpkg $Hc $Hn $Hk $Hev $Hpre2] as %b' ⟨Hk, -, -⟩
        try rw [emitStep_dead2, emitStep_dead3]
        ihave Hsf : (⌜true = true⌝ ∨ sendFacts (GF := GF) γ.toAntNames I.ms[i].st) $$ []
        · ileft; ipureintro; rfl
        try wp_auto
        wp_apply wp_sendMsg c γ n j I.ms[i].loc false I.ms[i].st qp true ff
          $$ [$Hpkg $Hc $Hn $Hk $Hadd $Htt $HpC $Hsf] as ⟨Hk, Hadd, Htt, -⟩
        · ipureintro; exact ⟨hss, Hres⟩
        isplitr
        · ipureintro; rfl
        iframe Hs
        iunfold parLoopB2
        iexists true, ff, null, vv, net, xnet, I.ms[i].loc
        iframe Hnp Hbp Hrdp Hk Hcl Hvf Hm Hfz Hl Hadd Htt
        isplitr
        · iapply (parCauseB2_dead_null (GF := GF) γ j vv net xnet)
        ipureintro; exact parInvB2_dead Hinv
    · -- not a request
      have hr' : isRequestTy I.ms[i].st.msg.Type' = false := by simpa using hr
      ihave Hacc := (BigSepL.bigSepL_lookup_acc (Φ := fun _ (m : QMsg) => if isRequestTy m.st.msg.Type'
        then frozenMsg (GF := GF) m.loc m.st else msgOwnZ (GF := GF) false m.loc (readyDq m.st) m.st)
        (List.getElem?_eq_getElem hi)).1 $$ Hfz
      icases Hacc with ⟨Hq, Hback⟩
      ihave Hq := ite_false_ent hr' $$ Hq
      icases msgOwnZ_ptsC_wand _ _ _ $$ Hq with ⟨HpC, Hw⟩
      wp_apply wp_isRequest I.ms[i].loc (readyDq I.ms[i].st) DFrac.discard false I.ms[i].st
        $$ [$Hpkg $HpC] as HpC
      ihave Hq := Hw $$ HpC
      ihave Hq := ite_false_intro (P := frozenMsg (GF := GF) I.ms[i].loc I.ms[i].st) hr' $$ Hq
      ihave Hfz := Hback $$ %I.ms[i] Hq
      rw [List.set_getElem_self, hr']
      wp_auto
      isplitr
      · ipureintro; rfl
      iframe Hs
      iunfold parLoopB2
      iexists dd, ff, cc, vv, net, xnet, I.ms[i].loc
      iframe Hnp Hbp Hrdp Hk Hcl Hvf Hpc Hm Hfz Hl Hadd Htt
      ipureintro; exact parInvB2_other hi hr' Hinv
  iintro HP Hs
  iunfold parLoopB2 at HP
  icases HP with ⟨%dd, %ff, %cc, %vv, %net, %xnet, %x0, Hnp, Hbp, Hrdp, Hk, Hcl, Hvf, Hpc, %Hinv,
    Hm, Hfz, Hl, Hadd, Htt⟩
  rw [List.length_map] at Hinv
  wp_auto
  iapply HΦ $$ %dd %ff %cc %vv %net %xnet
  iframe Hnp Hbp Hrdp Hk Hcl Hvf Hpc Hl Hadd Htt
  isplitr
  · ipureintro; exact Hinv
  iunfold drainMsgsParB2
  iframe Hs Hcap Hrm
  isplitl
  · iapply bigSepL_frozenReq_ptsC
    iexact Hfz
  ipureintro; exact Hmok

end par

end AntHarness
end EtcdGrove
end Perennial
