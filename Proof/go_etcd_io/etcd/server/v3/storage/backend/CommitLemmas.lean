/-
The views across the batch transaction's write-back and commit (`Model2.lean`): what the
readers see after a write-back (`ovB_wbMerge`), after a commit (`vData_reset`), and the views off
the hook's buckets as finite maps (`vData_eq_of_agree`). Lean-first (no Rocq counterpart).
-/
module

public import Proof.go_etcd_io.etcd.server.v3.storage.backend.BatchLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace backend

/-! ## Buckets -/

theorem bkOf_bksResetC (B : GMap w64 (List Ent)) (i : w64) : bkOf (bksReset B) i = [] := by
  unfold bkOf bksReset
  show (((B.filter _).fmap _).lookup i).getD [] = []
  rw [show ((B.filter (fun _ es => !es.isEmpty)).fmap (fun _ => ([] : List Ent))).lookup i =
    ((B.lookup i).filter (fun es => !es.isEmpty)).map (fun _ => []) from rfl]
  cases B.lookup i with
  | none => rfl
  | some es => simp only [Option.filter]; split <;> rfl

theorem bkOf_wbMerge (W R : GMap w64 (List Ent)) (i : w64) :
    bkOf (wbMerge W R) i =
      match W.lookup i with
      | some es => canon (bkOf R i ++ es)
      | none => bkOf R i := by
  unfold bkOf wbMerge
  show (((((W.lookup i).map _)).or (R.lookup i)).getD []) = _
  cases W.lookup i with
  | none => rfl
  | some es => rfl

theorem bkOf_wbMerge' (W R : GMap w64 (List Ent)) (i : w64) :
    lastVal (bkOf (wbMerge W R) i) = fun k => (lastVal (bkOf W i) k).or (lastVal (bkOf R i) k) := by
  funext k
  rw [bkOf_wbMerge]
  unfold bkOf
  cases hw : W.lookup i with
  | none => simp [lastVal]
  | some es =>
    simp only [Option.getD_some]
    rw [lastVal_canon]
    unfold lastVal
    rw [List.reverse_append, List.find?_append]
    cases es.reverse.find? (fun e => decide (e.1 = k)) <;> simp

theorem length_bkOf_wbMerge (W R : GMap w64 (List Ent)) (i : w64) :
    (bkOf (wbMerge W R) i).length ≤ (bkOf R i).length + (bkOf W i).length := by
  rw [bkOf_wbMerge]
  unfold bkOf
  cases W.lookup i with
  | none => simp
  | some es =>
    simp only [Option.getD_some]
    have := canon_length_le ((R.lookup i).getD [] ++ es)
    simp only [List.length_append] at this
    omega

/-! ## Views -/

/-- Empty buffer buckets add nothing to a view. -/
theorem ovB_empty (BT : GMap GoString w64) (B : GMap w64 (List Ent)) (f : VFun)
    (h : ∀ i, bkOf B i = []) : ovB BT B f = f := by
  funext n k
  unfold ovB
  cases BT.lookup n with
  | none => rfl
  | some i => simp [h i, lastVal]

/-- The write-back's read buffer reads as the write buffer over the read buffer. -/
theorem ovB_wbMerge (BT : GMap GoString w64) (W R : GMap w64 (List Ent)) (f : VFun) :
    ovB BT (wbMerge W R) f = ovB BT W (ovB BT R f) := by
  funext n k
  unfold ovB
  cases BT.lookup n with
  | none => rfl
  | some i =>
    simp only [Option.bind_some]
    rw [bkOf_wbMerge']
    show ((lastVal (bkOf W i) k).or (lastVal (bkOf R i) k)).or (f n k) = _
    generalize lastVal (bkOf W i) k = a
    generalize lastVal (bkOf R i) k = c
    cases a <;> cases c <;> rfl

/-- Write-buffer buckets empty off the hook's buckets add nothing there. -/
theorem agreeOff_ovB_nonHB (P : BParams) (W : GMap w64 (List Ent)) (f : VFun)
    (h : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf W i = []) :
    agreeOff P.HB (ovB P.BT W f) f := by
  intro n hn k
  unfold ovB
  cases hb : P.BT.lookup n with
  | none => rfl
  | some i => simp [h n i hb hn, lastVal]

/-- Two readers' states with views agreeing off the hook's buckets have one `vData`. -/
theorem vData_eq_of_agree (P : BParams) (rv rv' : RView)
    (h : agreeOff P.HB (vOf P rv) (vOf P rv')) : vData P rv = vData P rv' := by
  apply GMap.ext
  intro nk
  show (if P.HB nk.1 then none else vOf P rv nk.1 nk.2) =
    (if P.HB nk.1 then none else vOf P rv' nk.1 nk.2)
  cases hh : P.HB nk.1
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact h nk.1 hh nk.2
  · rfl

/-- And conversely. -/
theorem agree_of_vData_eq (P : BParams) (rv rv' : RView) (h : vData P rv = vData P rv') :
    agreeOff P.HB (vOf P rv) (vOf P rv') := by
  intro n hn k
  have := congrArg (fun m => GMap.lookup m (n, k)) h
  change (if P.HB n then none else vOf P rv n k) = (if P.HB n then none else vOf P rv' n k) at this
  simpa [hn] using this

theorem vOf_emptyR (P : BParams) (C : Data) : vOf P (C, ⟨∅, W64 0⟩) = dget C := by
  unfold vOf
  exact ovB_empty P.BT ∅ (dget C) (fun i => rfl)

theorem vOf_resetC (P : BParams) (C : Data) (R : RBuf) : vOf P (C, R.reset) = dget C := by
  unfold vOf
  exact ovB_empty P.BT _ (dget C) (fun i => bkOf_bksResetC R.bks i)

/-- After a commit, the readers see the committed data. -/
theorem vData_reset (P : BParams) (C : Data) (R : RBuf) : vData P (C, R.reset) = sData P C := by
  unfold sData
  apply vData_eq_of_agree
  rw [vOf_resetC, vOf_emptyR]
  intro _ _ _
  rfl

theorem sData_agree (P : BParams) (S S' : Data) (h : sData P S = sData P S') :
    agreeOff P.HB (dget S) (dget S') := by
  have := agree_of_vData_eq P _ _ h
  rw [vOf_emptyR, vOf_emptyR] at this
  exact this

theorem agreeOff_trans {HB : GoString → Bool} {f g h : VFun} (h1 : agreeOff HB f g)
    (h2 : agreeOff HB g h) : agreeOff HB f h :=
  fun n hn k => (h1 n hn k).trans (h2 n hn k)

theorem agreeOff_symm {HB : GoString → Bool} {f g : VFun} (h1 : agreeOff HB f g) :
    agreeOff HB g f :=
  fun n hn k => (h1 n hn k).symm

/-- At a free lock, the readers see the writer's contents (off the hook's buckets). -/
theorem vData_free (P : BParams) (st : BSess) (hst : sessWf P st) (hn : st.ndel = W64 0)
    (hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = []) :
    vData P (st.C, st.R) = sData P st.S := by
  unfold sData
  apply vData_eq_of_agree
  rw [vOf_emptyR]
  have hag := hst.2.2.2.2.2.2.2.2.2.1 hn
  exact agreeOff_symm (agreeOff_trans hag (agreeOff_ovB_nonHB P st.W.bks _ hW))

/-- A free state changed nothing the readers see. -/
theorem viewSame_of_freeOk {P : BParams} {st : BSess} (h : freeOk P st) : viewSame P st :=
  ⟨vData_free P st h.1 h.2.2.1 h.2.2.2.1, h.2.2.2.1⟩

/-- A read buffer's empty (or absent) bucket is gone after its reset. -/
theorem RBuf.reset_lookup_none {R : RBuf} {i : w64} (h : bkOf R.bks i = []) :
    R.reset.bks.lookup i = none := by
  unfold RBuf.reset bksReset
  show ((R.bks.filter (fun _ es => !es.isEmpty)).fmap (fun _ => ([] : List Ent))).lookup i = none
  rw [show ((R.bks.filter (fun _ es => !es.isEmpty)).fmap (fun _ => ([] : List Ent))).lookup i =
    ((R.bks.lookup i).filter (fun es => !es.isEmpty)).map (fun _ => []) from rfl]
  unfold bkOf at h
  cases hl : R.bks.lookup i with
  | none => rfl
  | some es => rw [hl] at h; simp at h; subst h; rfl

/-- After the commit's reset of the read buffer, out of the hook's window, a write-buffer bucket
may still repeat a key only where the read buffer has none. -/
theorem wfR_reset {W : WBuf} {st : BSess} (h : W.WfR (wbDupOk st)) (cnt' : BCnt) :
    W.WfR (wbDupOk { st with R := st.R.reset, cnt := cnt' }) := by
  apply h.mono
  intro i hi
  left
  show st.R.reset.bks.lookup i = none
  rcases hi with hi | ⟨-, hi⟩
  · have : bkOf st.R.bks i = [] := by unfold bkOf; rw [hi]; rfl
    exact RBuf.reset_lookup_none this
  · exact RBuf.reset_lookup_none hi

theorem idsOk_bksReset {P : BParams} {B : GMap w64 (List Ent)} (h : idsOk P B) :
    idsOk P (bksReset B) := by
  intro i es hi
  unfold bksReset at hi
  change ((B.lookup i).filter _).map _ = some es at hi
  cases hb : B.lookup i with
  | none => rw [hb] at hi; simp at hi
  | some es0 => exact h i es0 hb

theorem hookStep_refl (P : BParams) (st : BSess) : hookStep P st st :=
  ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl, Int.le_refl _, by omega, Int.le_refl _, rfl, rfl⟩

/-- A free state leaves room for a commit's hook. -/
theorem room_of_freeOk {P : BParams} {st : BSess} (hP : P.Wf) (h : freeOk P st) :
    sint.Z st.pend + P.hookMax < 2 ^ 58 := by
  have h1 := h.2.1
  have h2 := hP.2.2.1
  have h3 := hP.2.2.2.1
  omega

/-! ## The hook's window -/

/-- The state with the hook's window flag set to `x` (the commit opens it for its hook). -/
def BSess.setHw (st : BSess) (x : Bool) : BSess := { st with cnt := { st.cnt with hw := x } }

section setHw_proj
variable (st : BSess) (x : Bool)
theorem setHw_C : (st.setHw x).C = st.C := rfl
theorem setHw_S : (st.setHw x).S = st.S := rfl
theorem setHw_R : (st.setHw x).R = st.R := rfl
theorem setHw_W : (st.setHw x).W = st.W := rfl
theorem setHw_pend : (st.setHw x).pend = st.pend := rfl
theorem setHw_ndel : (st.setHw x).ndel = st.ndel := rfl
theorem setHw_tx : (st.setHw x).tx = st.tx := rfl
theorem setHw_hw : (st.setHw x).cnt.hw = x := rfl
end setHw_proj

/-- Opening the hook's window keeps the state's facts (it only allows more). -/
theorem sessWf_setHw {P : BParams} {st : BSess} (h : sessWf P st) : sessWf P (st.setHw true) := by
  obtain ⟨hWf, rest⟩ := h
  refine ⟨hWf.mono (fun i hi => ?_), rest⟩
  rcases hi with hi | ⟨-, hi⟩
  · exact Or.inl hi
  · exact Or.inr ⟨rfl, hi⟩

theorem bgOk_setHw {P : BParams} {st : BSess} {free : Bool} {n w u : Nat} (x : Bool)
    (h : bgOk P st free n w u) : bgOk P (st.setHw x) free n w u := h

/-- The hook's window, at a commit (every put written back: `p0 = pend`): the write buffer
holds only the hook's leftovers, `hookMax` a commit since the last write-back, and the read
buffer is empty after a commit until the next write-back. -/
theorem hookWin_of {P : BParams} {st : BSess} {n w u : Nat} (hb : bgOk P st false n w u)
    (hp0 : st.cnt.p0 = sint.nat st.pend) :
    ∀ i, bkOf st.W.bks i = [] ∨ bkOf st.R.bks i = [] := by
  obtain ⟨-, -, -, -, ⟨-, hc⟩, -, h7, -, -⟩ := hb
  intro i
  rcases hc with hc | hc
  · left
    have := (h7 i).1
    rw [hc, hp0, Nat.mul_zero] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  · right; exact hc i

/-! ## The commit -/

/-- The state after a commit (`unsafeCommit`): the committed data `C'` (the writer's contents,
or unchanged if nothing was committed), the read buffer reset, nothing pending, bbolt's write
transaction `tx'`, the counters `cnt'`. -/
def commitSt (st : BSess) (C' : Data) (tx' : Loc) (cnt' : BCnt) : BSess :=
  { st with C := C', R := st.R.reset, pend := W64 0, ndel := W64 0, tx := tx', cnt := cnt' }

section commitSt_proj
variable (st : BSess) (C' : Data) (tx' : Loc) (cnt' : BCnt)
theorem commitSt_C : (commitSt st C' tx' cnt').C = C' := rfl
theorem commitSt_S : (commitSt st C' tx' cnt').S = st.S := rfl
theorem commitSt_R : (commitSt st C' tx' cnt').R = st.R.reset := rfl
theorem commitSt_W : (commitSt st C' tx' cnt').W = st.W := rfl
theorem commitSt_pend : (commitSt st C' tx' cnt').pend = W64 0 := rfl
theorem commitSt_ndel : (commitSt st C' tx' cnt').ndel = W64 0 := rfl
theorem commitSt_tx : (commitSt st C' tx' cnt').tx = tx' := rfl
theorem commitSt_cnt : (commitSt st C' tx' cnt').cnt = cnt' := rfl
end commitSt_proj

/-- The views and the free lock's facts after a commit from `st` (where the hook ran into
`st'`), the write buffer empty off the hook's buckets and every put written back before. -/
theorem commit_final {P : BParams} {st st' : BSess} {C' : Data} {tx' : Loc} {cnt' : BCnt}
    (hP : P.Wf) (hst : sessWf P st) (hcnt : cnt'.hw = false)
    (hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = [])
    (hs : hookStep P st st') (hst' : sessWf P st')
    (hC' : C' = st'.S ∨ (st'.pend = W64 0 ∧ C' = st'.C)) :
    sessWf P (commitSt st' C' tx' cnt') ∧ freeOk P (commitSt st' C' tx' cnt') ∧
      vData P (C', st'.R.reset) = sData P st.S := by
  obtain ⟨hsC, hsR, hsS, hsW, hsp1, hsp2, hsn, hstx, hscnt⟩ := hs
  have hW' : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st'.W.bks i = [] :=
    fun n i h1 h2 => (hsW n i h1 h2).trans (hW n i h1 h2)
  -- the committed data reads, off the hook's buckets, as the writer's contents before the hook
  have hCS : agreeOff P.HB (dget C') (dget st.S) := by
    rcases hC' with rfl | ⟨hp0, rfl⟩
    · exact sData_agree P _ _ hsS
    · have hp : st.pend = W64 0 := by
        have h1 := hst.2.2.2.2.1
        have : sint.Z st'.pend = 0 := by rw [hp0]; rfl
        word
      have hn : st.ndel = W64 0 := by
        have h1 := hst.2.2.2.2.2.2.1
        have h2 := hst.2.2.2.2.2.2.2.1
        have : sint.Z st.pend = 0 := by rw [hp]; rfl
        word
      have hag := hst.2.2.2.2.2.2.2.2.2.1 hn
      have hR := hst.2.2.2.2.2.2.2.2.1 hp
      rw [hsC]
      unfold viewOf at hag
      rw [ovB_empty P.BT st.R.bks _ hR] at hag
      exact agreeOff_symm (agreeOff_trans hag (agreeOff_ovB_nonHB P st.W.bks _ hW))
  have hv : vData P (C', st'.R.reset) = sData P st.S := by
    rw [vData_reset]
    unfold sData
    apply vData_eq_of_agree
    rw [vOf_emptyR, vOf_emptyR]
    exact hCS
  have hsw : sessWf P (commitSt st' C' tx' cnt') := by
    obtain ⟨h1, h2, h3, h4, -, -, -, -, -, -, hsf'⟩ := hst'
    have hsafe : safeSt P (commitSt st' C' tx' cnt') := by
      refine ⟨?_, fun n i hn hsb => ⟨?_, ?_⟩⟩
      · intro n i _ _ kc vc e _ he
        exact absurd he (by show e ∉ bkOf (bksReset st'.R.bks) i; rw [bkOf_bksResetC]; simp)
      · intro kc vc e _ he
        have hHB : P.HB n = false := hP.2.2.2.2 n hsb
        have : bkOf st'.W.bks i = [] := hW' n i hn hHB
        exact absurd he (by show e ∉ bkOf st'.W.bks i; rw [this]; simp)
      · intro kc vc hc
        show ∃ vs, (bktOf st'.S n).lookup kc = some vs
        rcases hC' with rfl | ⟨_, rfl⟩
        · exact ⟨vc, hc⟩
        · exact (hsf'.2 n i hn hsb).2 kc vc hc
    refine ⟨wfR_reset h1 cnt', RBuf.reset_wf h2, h3, idsOk_bksReset h4, by simp [commitSt], by simp [commitSt],
      by simp [commitSt], by simp [commitSt], fun _ i => bkOf_bksResetC _ i, fun _ => ?_, hsafe⟩
    show agreeOff P.HB (dget st'.S) (ovB P.BT st'.W.bks (ovB P.BT (bksReset st'.R.bks) (dget C')))
    rw [ovB_empty P.BT _ _ (bkOf_bksResetC st'.R.bks)]
    refine agreeOff_trans ?_ (agreeOff_symm (agreeOff_ovB_nonHB P st'.W.bks _ hW'))
    exact agreeOff_trans (sData_agree P _ _ hsS) (agreeOff_symm hCS)
  refine ⟨hsw, ⟨hsw, ?_, rfl, hW', hcnt⟩, hv⟩
  have := hP.2.1
  simp only [commitSt]
  exact this

/-- The bounds after a commit from `st` (the hook ran into `st'`; every put written back before
the hook: `p0 = pend`), with the new counters `k'` paid commits and `c + 1` commits, given the
budget. -/
theorem commit_bgOk {P : BParams} {st st' : BSess} {C' : Data} {tx' : Loc} {n w u k' : Nat}
    (hW : ∀ n i, P.BT.lookup n = some i → P.HB n = false → bkOf st.W.bks i = [])
    (hp0 : st.cnt.p0 = sint.nat st.pend) (hs : hookStep P st st') (hst : sessWf P st)
    (hb' : bgOk P st' false n w u) (n' w' u' : Nat)
    (hbud : uint.Z st.R.ver + n' + k' < 2 ^ 40) (huw : u' ≤ w')
    (hc : st.cnt.c + 1 ≤ k' + 1 + (if u' = w' then 1 else 0)) :
    bgOk P (commitSt st' C' tx' ⟨k', st.cnt.c + 1, 0, 0, false⟩) true n' w' u' := by
  obtain ⟨hsC, hsR, hsS, hsW, hsp1, hsp2, hsn, hstx, hscnt⟩ := hs
  obtain ⟨-, -, -, h4, -, -, h7, -, -⟩ := hb'
  have hp := hst.2.2.2.2.1
  refine ⟨?_, huw, hc, by simp [commitSt],
    ⟨Or.inl rfl, Or.inr (fun i => bkOf_bksResetC _ i)⟩, Nat.zero_le _, ?_, ?_, ?_⟩
  · show uint.Z (bksReset st'.R.bks, st'.R.ver).2 + n' + k' < 2 ^ 40
    rw [hsR]; exact hbud
  · intro i
    refine ⟨?_, by show (bkOf (bksReset st'.R.bks) i).length ≤ _; rw [bkOf_bksResetC]; simp⟩
    obtain ⟨a1, -⟩ := h7 i
    rw [hscnt, hp0] at a1
    show (bkOf st'.W.bks i).length ≤ sint.nat (W64 0) - 0 + P.hookMax * (st.cnt.c + 1)
    have : sint.nat st'.pend - sint.nat st.pend ≤ P.hookMax := by
      have := hst.2.2.2.2.1
      word
    rw [Nat.mul_succ]
    simp only [sint.nat, show sint.Z (W64 0) = 0 from rfl]
    omega
  · intro nm i h1 h2
    show (bkOf st'.W.bks i).length ≤ _
    rw [(hsW nm i h1 h2).trans (hW nm i h1 h2)]
    simp
  · intro _
    exact ⟨rfl, fun h => absurd rfl h⟩

end backend
end EtcdGrove
end Perennial
