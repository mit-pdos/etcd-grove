/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **the requests a `-parallel` leader
sends before its write** (`parallel`'s `for _, m := range rd.Messages { if isRequest(m) { ... } }`),
pure parts:
- `isReqM_absMsgOf`: Go's `isRequest` is the Sim's `isReqM` on a message's protocol reading;
- `reqPend`: the view's pending messages at the loop's `i`th message (the requests from the `i`th
  on, then every other message), its start (`reqPend_zero`, `antSim_quietP_in`'s order), its steps
  (`reqPend_succ_req`, `reqPend_succ_other`) and its end (`reqPend_length`, `parallel`'s post);
- `sendHstepD`: a request's `send` report's B2 step (`antSim_sendD_in.law`), `DrainSteps.sendHstep`'s.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Cause
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSteps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace AntHarness

open go_etcd_io.raft.v3

section pure
variable [GooseExts]

/-- `isRequest` on a known message type: an append or a heartbeat. -/
theorem isRequestTy_mtypeOf {t : w32} {ty : MsgType} (H : mtypeOf t = some ty) :
    isRequestTy t = decide (ty = .app ∨ ty = .heartbeat) := by
  have key : ∀ k : Int, uint.Z t = k → t = W32 k := fun k hk => by rw [← hk]; simp
  unfold mtypeOf at H
  split at H <;> cases H <;> (rename_i hk; rw [key _ hk]; decide)

/-- **Go's `isRequest` is the Sim's `isReqM`** on a message's protocol reading. -/
theorem isReqM_absMsgOf {st : MsgSt} {q : Msg} (h : absMsgOf st = some q) :
    AntSim.isReqM q = isRequestTy st.msg.Type' := by
  unfold absMsgOf at h
  split at h
  · cases h
  · rename_i hty
    obtain ⟨sv, -, rfl⟩ := Option.map_eq_some_iff.1 h
    rw [isRequestTy_mtypeOf hty]; rfl
  · rename_i ty _ hty
    cases h
    rw [isRequestTy_mtypeOf hty]; rfl

/-- `filterMap` past a `filter` that agrees with one on the images. -/
theorem filterMap_filter_comm {α β : Type _} (f : α → Option β) (p : β → Bool) (p' : α → Bool)
    (hp : ∀ a b, f a = some b → p b = p' a) :
    ∀ l : List α, (l.filterMap f).filter p = (l.filter p').filterMap f
  | [] => rfl
  | a :: l => by
    have ih := filterMap_filter_comm f p p' hp l
    rcases hfa : f a with _ | b
    · cases hpa : p' a <;> simp [List.filterMap_cons, List.filter_cons, hfa, hpa, ih]
    · have hb := hp a b hfa
      cases hpa : p' a <;> simp [List.filterMap_cons, List.filter_cons, hfa, hpa, hb, ih]

/-- **The pending messages at the request loop's `i`th message**: the requests from the `i`th on,
then every other message of the `Ready`. -/
def reqPend (ms : List QMsg) (i : Nat) : List Msg :=
  ((ms.drop i).filter (fun m => isRequestTy m.st.msg.Type')).filterMap (fun m => absMsgOf m.st) ++
    (ms.filter (fun m => !isRequestTy m.st.msg.Type')).filterMap (fun m => absMsgOf m.st)

/-- The loop's start: `antSim_quietP_in`'s pending order (requests first). -/
theorem reqPend_zero (ms : List QMsg) :
    reqPend ms 0 =
      (ms.filterMap (fun m => absMsgOf m.st)).filter AntSim.isReqM ++
        (ms.filterMap (fun m => absMsgOf m.st)).filter (fun q => !AntSim.isReqM q) := by
  unfold reqPend
  rw [List.drop_zero,
    filterMap_filter_comm _ AntSim.isReqM (fun m => isRequestTy m.st.msg.Type')
      (fun _ _ h => isReqM_absMsgOf h),
    filterMap_filter_comm _ (fun q => !AntSim.isReqM q) (fun m => !isRequestTy m.st.msg.Type')
      (fun _ _ h => by rw [isReqM_absMsgOf h])]

/-- A request with a protocol reading `q`: the next pending message. -/
theorem reqPend_succ_req {ms : List QMsg} {i : Nat} (hi : i < ms.length) {q : Msg}
    (hq : absMsgOf ms[i].st = some q) (hr : isRequestTy ms[i].st.msg.Type' = true) :
    reqPend ms i = q :: reqPend ms (i + 1) := by
  unfold reqPend
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.filter_cons, hr, ite_true, List.filterMap_cons, hq, List.cons_append]

/-- Any other message: nothing is pending for it in the loop. -/
theorem reqPend_succ_other {ms : List QMsg} {i : Nat} (hi : i < ms.length)
    (hr : isRequestTy ms[i].st.msg.Type' = false) :
    reqPend ms i = reqPend ms (i + 1) := by
  unfold reqPend
  rw [List.drop_eq_getElem_cons hi]
  simp only [List.filter_cons, hr, Bool.false_eq_true, ite_false]

/-- A request without a protocol reading (none: an append or a heartbeat has one). -/
theorem reqPend_succ_none {ms : List QMsg} {i : Nat} (hi : i < ms.length)
    (hq : absMsgOf ms[i].st = none) :
    reqPend ms i = reqPend ms (i + 1) := by
  unfold reqPend
  rw [List.drop_eq_getElem_cons hi]
  cases hr : isRequestTy ms[i].st.msg.Type' <;>
    simp only [List.filter_cons, hr, Bool.false_eq_true, ite_false, ite_true, List.filterMap_cons, hq]

/-- The loop's end: the other messages (`parallel`'s post). -/
theorem reqPend_length (ms : List QMsg) :
    reqPend ms ms.length =
      (ms.filter (fun m => !isRequestTy m.st.msg.Type')).filterMap (fun m => absMsgOf m.st) := by
  unfold reqPend
  rw [List.drop_length]; rfl

/-- **A request's `send` report's B2 step** (`sendHstep`'s over `SimPreD`, `antSim_sendD_in.law`):
the next pending message `q`, its facts grown by the message's (`sendExt_b1`'s). -/
theorem sendHstepD (h_send : antSim_sendD_in.law) {R : AntSim.RunCfg} {dec : CCDec}
    (msk : AntSim.SimMask) (hmsk : msk ≤ AntSim.mskB2) (j : Fin R.N) (v : AntSim.NodeView) (q : Msg)
    (rest : List Msg) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSimD R dec S V net xnet → AntSim.InMask msk R net xnet)
    (hasync : R.md.async = false) (hbat : R.drv.batch = false) (hpend : v.pend = q :: rest)
    (htold : AntSim.Told v) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPreD R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      (FactsLe R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.MsgFacts G q) →
      V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStepD R dec evs G (AntSim.evSend (AntSim.nodeId j) v.byE q)
          (AntSim.setV V j (sendView v rest)) (net ++ [q]) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j (sendView v rest) i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs ⟨hle, hL, hmf⟩ hVj _ _
  subst hVj
  have hpre' : AntSim.SimPreD R dec S V net xnet evs G :=
    ⟨hpre.1, hpre.2.1, hL, globalOk_mono hpre.2.2.2 hle⟩
  refine ⟨?_, hL, setV_logs hlogs hle.2.2.2.1 (hle.2.2.2.1 _ (hlogs j))⟩
  simp only [List.append_nil]
  exact h_send msk hmsk R dec S V net xnet evs G j q rest (hinm S V net xnet hpre.2.1) hpre' hasync
    hbat hpend htold hmf

end pure

end AntHarness
end EtcdGrove
end Perennial
