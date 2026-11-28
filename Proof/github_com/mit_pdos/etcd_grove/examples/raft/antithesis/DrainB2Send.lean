/-
Lean-first (no Rocq counterpart). #33 parity B2, driver group E: **the requests a `-parallel` leader
sends before its write** (`parallel`'s `for _, m := range rd.Messages { if isRequest(m) { ... } }`),
pure parts:
- `isReqM_absMsgOf`: Go's `isRequest` is the Sim's `isReqM` on a message's protocol reading;
- `reqPend`: the view's pending messages at the loop's `i`th message (the requests from the `i`th
  on, then every other message), its start (`reqPend_zero`, `antSim_quietP_in`'s order), its steps
  (`reqPend_succ_req`, `reqPend_succ_other`) and its end (`reqPend_length`, `parallel`'s post);
- `sendHstepD`: a request's `send` report's B2 step (`Sim/SendD`'s `antSim_sendD_in`), `DrainSteps.sendHstep`'s;
- `memHstepD`, `writeHstepD`, `wroteHstepD`: the `mem`, `write` and `wrote` reports' B2 steps
  (`StmtsB2`'s `antSim_memP_in`, `antSim_write_in`, `antSim_wrote_in`), in `report_updB2`'s shape.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainB2Cause
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.DrainSteps
public import Proof.github_com.mit_pdos.etcd_grove.examples.raft.antithesis.Sim.SendD

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

/-- **A request's `send` report's B2 step** (`sendHstep`'s over `SimPreD`, `AntSim.antSim_sendD_in`):
the next pending message `q`, its facts grown by the message's (`sendExt_b1`'s). -/
theorem sendHstepD {R : AntSim.RunCfg} {dec : CCDec}
    (msk : AntSim.SimMask) (hmsk : msk ≤ AntSim.mskB2) (j : Fin R.N) (v : AntSim.NodeView) (q : Msg)
    (rest : List Msg) (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSimD R dec S V net xnet → AntSim.InMask msk R net xnet)
    (hasync : R.md.async = false) (hbat : R.drv.batch = false) (hpend : v.pend = q :: rest)
    (htold : AntSim.Told v) (hnum : q.ty = .readIndexResp → AntSim.MsgNums (2 ^ 61) q)
    (hparts : v.parts = []) (hmr : v.mems = [] ∨ AntSim.isReqM q = true) :
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
  exact AntSim.antSim_sendD_in msk hmsk R dec S V net xnet evs G j q rest (hinm S V net xnet hpre.2.1)
    hpre' hasync hbat hpend htold hmf hnum hparts hmr

/-- B2's masks are B2.5's. -/
theorem mskB25_of_le {msk : AntSim.SimMask} (h : msk ≤ AntSim.mskB2) : msk ≤ AntSim.mskB25 := by
  have h' : AntSim.SimMask.Le msk AntSim.mskB2 := h
  obtain ⟨⟨m1, m2, m3, m4, m5, m6, m7, -, m9⟩, hk, h3, h4, h5, h6, -, h8⟩ := h'
  show AntSim.SimMask.Le msk AntSim.mskB25
  exact ⟨⟨m1, m2, m3, m4, m5, m6, m7, fun _ => rfl, m9⟩, hk, h3, h4, h5, h6, fun _ => rfl, h8⟩

/-- **`-parallel`'s `mem` report's B2 step** (`antSim_memP_in.stmt` in `report_updB2`'s shape): at a
reported leader's `Ready` (`ReachIn` over the lower bounds, `ReadyOutP`), raft's facts grown by the
`Ready`'s (`FactsLe`, lawful, `ReadyFacts`); the view the drain's, its requests first, the write
queued when it writes. -/
theorem memHstepD (h_mem : AntSim.antSim_memP_in.stmt) {R : AntSim.RunCfg} {dec : CCDec}
    {Adm : List EntryM → CCState → Prop} (msk : AntSim.SimMask) (hmsk : msk ≤ AntSim.mskB2)
    (j : Fin R.N) (v : AntSim.NodeView) (r₁ : RState) (rd : AntSim.ReadyD) (w : Bool)
    (net₀ : List Msg) (xnet₀ : List XMsg)
    (hinm : ∀ S V net xnet, AntSim.AntSimD R dec S V net xnet → AntSim.InMask msk R net xnet)
    (hasync : R.md.async = false) (hbat : R.drv.batch = false) (hpar : R.drv.parallel = true)
    (hreach : AntSim.ReachIn msk R dec Adm net₀ xnet₀ j v r₁) (hout : AntSim.ReadyOutP R j v r₁ rd)
    (hlead : rd.role = .leader) (hsnap : rd.snap = none) (hrep : AntSim.Reported v rd)
    (hw : w = true ↔ AntSim.Writes v rd) (htold : AntSim.Told v) (hterm : AntSim.TermRoom v) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPreD R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      (FactsLe R G0 G ∧ AntSim.RaftLaws G ∧ AntSim.ReadyFacts G (AntSim.nodeId j) r₁) →
      V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStepD R dec evs G
          (AntSim.evMem (AntSim.nodeId j) v.byE (AntSim.roleStr rd.pre rd.role) rd.term rd.vote
            rd.commit rd.ents none w)
          (AntSim.setV V j { (v.drainOf r₁ rd) with
            pend := rd.msgs.filter AntSim.isReqM ++ rd.msgs.filter (fun q => !AntSim.isReqM q),
            mems := if w then v.mems ++ [rd.memRec v] else v.mems }) (net ++ []) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j { (v.drainOf r₁ rd) with
            pend := rd.msgs.filter AntSim.isReqM ++ rd.msgs.filter (fun q => !AntSim.isReqM q),
            mems := if w then v.mems ++ [rd.memRec v] else v.mems } i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs ⟨hle, hL, hrf⟩ hVj hn hx
  subst hVj
  have hpre' : AntSim.SimPreD R dec S V net xnet evs G :=
    ⟨hpre.1, hpre.2.1, hL, globalOk_mono hpre.2.2.2 hle⟩
  refine ⟨?_, hL, setV_logs hlogs hle.2.2.2.1 hrf.1⟩
  simp only [List.append_nil]
  exact h_mem msk hmsk R dec S V net xnet evs G j r₁ rd w Adm (hinm S V net xnet hpre.2.1) hpre'
    hasync hbat hpar (hreach.mono hn hx) hout hlead hsnap hrep hw htold hrf hterm

/-- **`-parallel`'s `write` report's B2 step** (`antSim_write_in.stmt`): the oldest queued `mem`'s
write announced, its undo the disk before it; raft's facts unchanged. -/
theorem writeHstepD (h_write : AntSim.antSim_write_in.stmt) {R : AntSim.RunCfg} {dec : CCDec}
    (msk : AntSim.SimMask) (hmsk : msk ≤ AntSim.mskB2) (j : Fin R.N) (v : AntSim.NodeView)
    (m : AntSim.MemRec) (rest : List AntSim.MemRec)
    (hinm : ∀ S V net xnet, AntSim.AntSimD R dec S V net xnet → AntSim.InMask msk R net xnet)
    (hbat : R.drv.batch = false) (hpar : R.drv.parallel = true) (hasync : R.md.async = false)
    (hmems : v.mems = m :: rest) (net₀ : List Msg) (xnet₀ : List XMsg) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPreD R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      G = G0 → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStepD R dec evs G (AntSim.evWrite (AntSim.nodeId j) m.term m.vote m.commit m.ents m.snap)
          (AntSim.setV V j { v with dur := v.dur.write m, undo := some v.dur, made := false, mems := rest, jobs := AntSim.markHead v.jobs }) (net ++ []) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j { v with dur := v.dur.write m, undo := some v.dur, made := false, mems := rest, jobs := AntSim.markHead v.jobs } i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs hG hVj _ _
  subst hG hVj
  refine ⟨?_, hpre.2.2.1, setV_logs hlogs (fun _ h => h) (hlogs j)⟩
  simp only [List.append_nil]
  exact h_write msk (mskB25_of_le hmsk) R dec S V net xnet evs G j m rest (hinm S V net xnet hpre.2.1)
    hpre hbat (.inr hpar) hmems (fun h => by rw [hasync] at h; cases h)

/-- **`wrote`'s B2 step** (`antSim_wrote_in.stmt`, `-parallel`): the announced write made. -/
theorem wroteHstepD (h_wrote : AntSim.antSim_wrote_in.stmt) {R : AntSim.RunCfg} {dec : CCDec}
    (msk : AntSim.SimMask) (hmsk : msk ≤ AntSim.mskB2) (j : Fin R.N) (v : AntSim.NodeView)
    (hinm : ∀ S V net xnet, AntSim.AntSimD R dec S V net xnet → AntSim.InMask msk R net xnet)
    (hpar : R.drv.parallel = true) (hundo : v.undo ≠ none) (net₀ : List Msg) (xnet₀ : List XMsg) :
    ∀ (evs : List AntCheck.Event) (S : AntCheck.State) (V : Fin R.N → AntSim.NodeView)
      (net : List Msg) (xnet : List XMsg) (G0 G : AntSim.RaftFacts),
      AntSim.SimPreD R dec S V net xnet evs G0 → (∀ i : Fin R.N, (V i).r.full ∈ G0.logs) →
      G = G0 → V j = v → net₀ <+: net → xnet₀ <+: xnet →
      AntSim.SimStepD R dec evs G (AntSim.evWrote (AntSim.nodeId j))
          (AntSim.setV V j { v with undo := none, made := true }) (net ++ []) (xnet ++ []) ∧
        AntSim.RaftLaws G ∧
        ∀ i : Fin R.N, (AntSim.setV V j { v with undo := none, made := true } i).r.full ∈ G.logs := by
  intro evs S V net xnet G0 G hpre hlogs hG hVj _ _
  subst hG hVj
  refine ⟨?_, hpre.2.2.1, setV_logs hlogs (fun _ h => h) (hlogs j)⟩
  simp only [List.append_nil]
  exact h_wrote msk hmsk R dec S V net xnet evs G j (hinm S V net xnet hpre.2.1) hpre
    (.inr (.inl hpar)) hundo

end pure

end AntHarness
end EtcdGrove
end Perennial
