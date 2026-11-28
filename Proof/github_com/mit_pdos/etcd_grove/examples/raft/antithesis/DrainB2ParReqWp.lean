/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: the pieces of `parReqB2.stmt`'s proof
(`node.parallel`'s request loop):
- `drain_peekB2`: node `j`'s B2 relation (`NodeOkD`) read from the run's invariant at its view;
- `pendFactsD_of`: the pending messages' facts out of it (unbatched);
- `bigSepL_frozenReq`: the `Ready`'s requests frozen, the other messages left owned;
- `req_absMsgOf`: a request (`isRequest`) has a protocol reading, an append or a heartbeat;
- `rMd_flags_b2`: B2's masked-off raft features off in the run's mask.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2ParPhases
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB1SendWp
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.Mono

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

end AntHarness
end EtcdGrove
end Perennial
