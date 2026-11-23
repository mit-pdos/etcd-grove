/-
The pop of a component in `strongconnect` (exec.go), its pure side: the component is the
model's `sccReady` (`pop_sccReady`, from Tarjan's `pop_ready`), `nodeArray.Less` is a strict weak
order (`keyLt_swo`, for `sort.Sort`), and the state while the sorted component's instances are
executed one by one (`PopOk`: the instances done are `EXECUTED`, nothing else changed but the
store), preserved by the per-command step (`popOk_cmd`) and the instance's end (`popOk_done`),
and what it gives at the end (`popOk_final`, for `pop_inv`). Also the store's agreement between
`state.Command.Execute`'s map and the model's (`execCmd_agree`).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.epaxos.ExecLemmas
public import Perennial.Proof.sort.Link

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos_epaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net github_com.imdea_software.swiftpaxos_epaxos.kvs
open model tarjan epaxosProof BigSepL

attribute [local instance] GooseGlobalGS.gooseInvGS

variable [GooseExts]

/-! ## The component -/

theorem pop_sccReady {σc : RState} {tc : St InstId} {A0 S0 T : List InstId} {v : InstId}
    (h : TInv (gr σc) tc) (hA : tc.A = A0 ++ [v]) (hS : tc.S = S0 ++ v :: T)
    (hlv : tc.low v = tc.num v) (hdv : DoneAll (gr σc) tc v) : sccReady σc (v :: T) := by
  obtain ⟨hnd, hrd, hcl, hsc⟩ := pop_ready h hA hS hlv hdv
  exact ⟨List.cons_ne_nil _ _, hnd, fun x hx => (hrd x hx).1, hcl, hsc⟩

/-! ## The sort's order -/

theorem keyLt_irrefl (σ : RState) (a : InstId) : ¬ keyLt σ a a := by
  unfold keyLt; intro h; rcases h with h | ⟨-, h⟩ <;> omega

theorem keyLt_trans (σ : RState) (a b c : InstId) (h1 : keyLt σ a b) (h2 : keyLt σ b c) :
    keyLt σ a c := by
  unfold keyLt at *
  generalize ((σ.inst a).map (·.seq)).getD 0 = sa at *
  generalize ((σ.inst b).map (·.seq)).getD 0 = sb at *
  generalize ((σ.inst c).map (·.seq)).getD 0 = sc at *
  rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
  · exact Or.inl (by omega)
  · subst e2; exact Or.inl h1
  · subst e1; exact Or.inl h2
  · subst e1; subst e2; exact Or.inr ⟨rfl, by omega⟩

theorem keyLt_incomp (σ : RState) (a b : InstId) (h1 : ¬ keyLt σ a b) (h2 : ¬ keyLt σ b a) :
    a = b :=
  sccLe_antisymm σ a b ((sccLe_iff σ a b).mpr h2) ((sccLe_iff σ b a).mpr h1)

theorem keyLt_swo (σ : RState) : slices.StrictWeakOrder (keyLt σ) where
  strict_weak_order_irrefl := keyLt_irrefl σ
  strict_weak_order_trans := keyLt_trans σ
  strict_weak_order_equiv := by
    constructor
    · intro x; exact ⟨keyLt_irrefl σ x, keyLt_irrefl σ x⟩
    · intro x y h; exact ⟨h.2, h.1⟩
    · intro x y z h1 h2
      have e1 := keyLt_incomp σ x y h1.1 h1.2
      have e2 := keyLt_incomp σ y z h2.1 h2.2
      subst e1; subst e2; exact h1

/-! ## Executing the sorted component -/

/-- `w` executed. -/
def exStat (w : InstRec) : InstRec := { w with status := stEXECUTED }

/-- The state `σk` after executing the instances `D` of the component (from `σc`). -/
structure PopOk (σc : RState) (D : List InstId) (σk : RState) : Prop where
  rel : ExRel σc σk
  wf : ExecWf σk
  ib : instBounds σk.inst
  inst : ∀ z, σk.inst z = if z ∈ D then (σc.inst z).map exStat else σc.inst z

theorem PopOk.init {σc : RState} (hwf : ExecWf σc) (hib : instBounds σc.inst) :
    PopOk σc [] σc :=
  ⟨ExRel.refl σc, hwf, hib, fun z => by simp⟩

theorem PopOk.inst_of {σc σk : RState} {D : List InstId} (h : PopOk σc D σk) {x : InstId}
    (hx : x ∉ D) : σk.inst x = σc.inst x := by
  rw [h.inst x, if_neg hx]

theorem popOk_cmd {σc σk : RState} {D : List InstId} (h : PopOk σc D σk) {x : InstId}
    {w : InstRec} (hw : σk.inst x = some w) (hc : isCommitted w.status) (idx : Nat) :
    PopOk σc D (execCmdAt σk w idx).1 := by
  obtain ⟨st, e⟩ := execCmdAt_fst σk w idx
  refine ⟨h.rel.trans (ExRel.execCmdAt σk w idx), h.wf.execCmdAt hw hc idx, ?_, ?_⟩
  · rw [e]; exact h.ib
  · rw [e]; exact h.inst

theorem popOk_done {σc σk : RState} {D : List InstId} (h : PopOk σc D σk) {x : InstId}
    {w : InstRec} (hx : x ∉ D) (hw : σc.inst x = some w) (hc : isCommitted w.status) :
    PopOk σc (D ++ [x]) (execDone σk x) := by
  have hwk : σk.inst x = some w := by rw [h.inst_of hx]; exact hw
  have e : execDone σk x = σk.setInst x (exStat w) := by unfold execDone; rw [hwk]; rfl
  refine ⟨h.rel.trans (ExRel.execDone σk x), h.wf.execDone hwk hc, ?_, ?_⟩
  · rw [e]; intro z hz
    simp only [RState.setInst, upd]
    split
    · subst_vars; rw [h.ib z hz] at hwk; cases hwk
    · exact h.ib z hz
  · intro z
    rw [e]; simp only [RState.setInst, upd, List.mem_append, List.mem_singleton]
    by_cases hz : z = x
    · subst hz; simp [hw]
    · simp only [hz, if_false, or_false]; exact h.inst z

theorem popOk_final {σc σ' : RState} {D C : List InstId} (h : PopOk σc D σ') (hp : D.Perm C)
    (hC : ∀ x ∈ C, ∃ w, σc.inst x = some w) :
    (gr σ').E = (gr σc).E ∧ (∀ z, (gr σ').ex z ↔ (gr σc).ex z ∨ z ∈ C) ∧
      (∀ z, z ∉ C → (gr σc).rd z → (gr σ').rd z) := by
  refine ⟨h.rel.gE, fun z => ?_, fun z hz hr => ?_⟩
  · show σ'.executed z ↔ σc.executed z ∨ z ∈ C
    by_cases hzC : z ∈ C
    · obtain ⟨w, hw⟩ := hC z hzC
      have : σ'.inst z = some (exStat w) := by rw [h.inst z, if_pos (hp.mem_iff.mpr hzC), hw]; rfl
      exact ⟨fun _ => Or.inr hzC, fun _ => ⟨_, this, rfl⟩⟩
    · have hzD : z ∉ D := fun hd => hzC (hp.mem_iff.mp hd)
      unfold RState.executed
      rw [h.inst_of hzD]; simp [hzC]
  · have hzD : z ∉ D := fun hd => hz (hp.mem_iff.mp hd)
    show σ'.ready z
    unfold RState.ready at *; rw [h.inst_of hzD]; exact hr

theorem execDone_inst {σ : RState} {x : InstId} {w : InstRec} (h : σ.inst x = some w) :
    (execDone σ x).inst = upd σ.inst x (some (exStat w)) := by
  unfold execDone; rw [h]; rfl

theorem execDone_store (σ : RState) (x : InstId) : (execDone σ x).store = σ.store := by
  unfold execDone; split <;> rfl

theorem ixOk_exec (y : epaxos.Instance) (w : InstRec) (il : Option (Nat × Nat)) (h : ixOk y w il) :
    ixOk { y with Status' := stEXECUTED } (exStat w) il := by
  rcases il with _ | ⟨a, b⟩
  · intro hn; exact absurd rfl hn
  · exact h

theorem execCmdAt_none (σ : RState) (w : InstRec) (idx : Nat)
    (h : ((w.cmds.getD []).getD idx default).op = opNONE) : execCmdAt σ w idx = (σ, []) := by
  unfold execCmdAt; dsimp only; rw [if_pos h]

theorem execCmdAt_noreply_put (σ : RState) (w : InstRec) (idx : Nat)
    (h1 : ((w.cmds.getD []).getD idx default).op ≠ opNONE) (h2 : w.lb.bind (·.clientProposals) = none)
    (h3 : ((w.cmds.getD []).getD idx default).op = opPUT) :
    execCmdAt σ w idx = ({ σ with store := (model.execCmd σ.store ((w.cmds.getD []).getD idx default)).1 }, []) := by
  unfold execCmdAt; dsimp only; rw [if_neg h1, h2]; dsimp only; rw [if_pos h3]

theorem execCmdAt_noreply_other (σ : RState) (w : InstRec) (idx : Nat)
    (h1 : ((w.cmds.getD []).getD idx default).op ≠ opNONE) (h2 : w.lb.bind (·.clientProposals) = none)
    (h3 : ((w.cmds.getD []).getD idx default).op ≠ opPUT) : execCmdAt σ w idx = (σ, []) := by
  unfold execCmdAt; dsimp only; rw [if_neg h1, h2]; dsimp only; rw [if_neg h3]

theorem execCmdAt_reply (σ : RState) (w : InstRec) (idx : Nat) (ps : List Proposal)
    (h1 : ((w.cmds.getD []).getD idx default).op ≠ opNONE) (h2 : w.lb.bind (·.clientProposals) = some ps) :
    execCmdAt σ w idx = ({ σ with store := (model.execCmd σ.store ((w.cmds.getD []).getD idx default)).1 },
      [Out.reply (ps.getD idx default) (model.execCmd σ.store ((w.cmds.getD []).getD idx default)).2]) := by
  unfold execCmdAt; dsimp only; rw [if_neg h1, h2]

/-- (stage 2, S5) A client command's result fits `Value.Marshal`'s 16-bit length when the
store's values are below `2^15` bytes (a SCAN reads at most two keys). -/
theorem execCmd_res_len (st : w64 → Option (List w8)) (c : WCmd)
    (h : ∀ k v, st k = some v → k.toNat < 2 ∧ v.length < 2 ^ 15) (hok : OpCmdOk c) :
    (model.execCmd st c).2.length < 2 ^ 16 := by
  unfold model.execCmd
  split
  · simp
  · split
    · rcases hk : st c.key with _ | v
      · simp
      · simp only [Option.getD_some]; have := (h _ _ hk).2; omega
    · split
      · rename_i hs
        have hlen := model.rangeKeys_length_le c hok hs
        have hb := model.filterMap_flatten_len st (rangeKeys c) (fun k v hk => (h k v hk).2)
        have : (rangeKeys c).length * 32767 ≤ 2 * 32767 := Nat.mul_le_mul_right _ hlen
        simp only; omega
      · simp

/-! ## `Execute`'s store against the model's -/

theorem execCmd_agree (S : GMap w64 (List w8)) (st : w64 → Option (List w8)) (c : WCmd)
    (h : ∀ k, S.lookup k = st k) :
    (∀ k, (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.execCmd S c).1.lookup k =
      (model.execCmd st c).1 k) ∧
    (_root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.execCmd S c).2 = (model.execCmd st c).2 := by
  have hf : S.lookup = st := funext h
  unfold _root_.Perennial.github_com.imdea_software.swiftpaxos_epaxos.execCmd model.execCmd
  split
  · refine ⟨fun k => ?_, rfl⟩
    simp only [upd]
    by_cases hk : c.key = k
    · subst hk; simp [GMap.lookup_insert]
    · rw [GMap.lookup_insert_ne _ _ hk, if_neg (Ne.symm hk)]; exact h k
  · split
    · exact ⟨h, by rw [h]⟩
    · split
      · exact ⟨h, by rw [hf]⟩
      · exact ⟨h, rfl⟩

/-! ## Two slots at once (`nodeArray.Less` reads two instances) -/

theorem bigSepL_acc2 {PROP : Type _} [BI PROP] {A : Type _} {Φ : Nat → A → PROP} {l : List A}
    {i j : Nat} {x y : A} (hi : l[i]? = some x) (hj : l[j]? = some y) (hij : i ≠ j) :
    ([∗list] k ↦ z ∈ l, Φ k z) ⊢ Φ i x ∗ Φ j y ∗ (Φ i x -∗ Φ j y -∗ [∗list] k ↦ z ∈ l, Φ k z) := by
  have e1 := bigSepL_delete_cond (Φ := Φ) hi
  have e2 := bigSepL_delete_cond (Φ := fun k z => if k = i then emp else Φ k z) hj
  have hj' : (if j = i then (emp : PROP) else Φ j y) = Φ j y := by simp [Ne.symm hij]
  simp only [hj'] at e2
  iintro H
  icases e1.1 $$ H with ⟨Hx, H⟩
  icases e2.1 $$ H with ⟨Hy, H⟩
  iframe Hx Hy
  iintro Hx Hy
  iapply e1.2; iframe Hx; iapply e2.2; iframe Hy H

/-! ## The edge loop after an edge `v → y` is handled -/

theorem merge_ix (t : St InstId) (A0 : List InstId) (v y x : InstId) :
    (t.merge A0 v y).ix x = if x = v then some (t.num v, min (t.low v) (t.low y)) else t.ix x := rfl

theorem setLow_vis' {t : St InstId} {v : InstId} {l : Nat} (hv : t.vis v) (x : InstId) :
    (t.setLow v l).vis x ↔ t.vis x := setLow_vis t v x hv

theorem VisCount_setLow {t : St InstId} {v : InstId} {l : Nat} (hv : t.vis v) (h : VisCount t) :
    VisCount (t.setLow v l) := by
  obtain ⟨V, h1, h2, h3, h4⟩ := h
  exact ⟨V, h1, fun x => (setLow_vis' hv x).trans (h2 x), h3, h4⟩

theorem VisCount_merge {t : St InstId} {A0 : List InstId} {v y : InstId} (hv : t.vis v)
    (h : VisCount t) : VisCount (t.merge A0 v y) :=
  VisCount_setLow (t := { t with A := A0 ++ [v] }) hv h

theorem Done_setLow {g : Gr InstId} {t : St InstId} {v z : InstId} {l : Nat} (hv : t.vis v)
    (hl : l ≤ t.low v) (h : Done g t v z) : Done g (t.setLow v l) v z :=
  setLow_done hv h (fun _ => hl)

/-- The callee `y` returned `true` (popped, or finished on the stack): `v.Lowlink` takes the
minimum (`St.merge`), the edge `v → y` is handled. -/
theorem LoopOk.callee {σ σc σ'' : RState} {t tc t'' : St InstId} {v y : InstId}
    {B : InstId → Prop} (h : LoopOk σ t v σc tc B) (hvis : ¬ t.vis v) (hR : ExRel σc σ'')
    (hwf : ExecWf σ'') (hib : instBounds σ''.inst) (hcnt : VisCount t'')
    (hext : Ext (gr σc) tc (gr σ'') t'') (hn : tc.n ≤ t''.n) (hT : TInv (gr σ'') t'')
    (hsc : scTrue σ'' t'' tc.A y tc.n) (hvisy : ¬ tc.vis y) (he : σc.depEdge v y) :
    LoopOk σ t v σ'' (t''.merge t.A v y) (fun z => B z ∨ z = y) := by
  have hvS : v ∈ tc.S := h.inv.actS v (by rw [h.act]; simp)
  have hvv : tc.vis v := (h.inv.onS v hvS).1
  have hvv'' : t''.vis v := hext.vis hvv
  obtain ⟨lv, hlv⟩ := h.ixv
  have hlv'' : t''.ix v = some (t.n, lv) := by rw [hext.ix v hvv]; exact hlv
  have hvS'' : v ∈ t''.S := by obtain ⟨T, hT2⟩ := hext.stk; rw [hT2]; exact List.mem_append_left _ hvS
  have hlowv : t''.low v ≤ t''.num v := (hT.lowW v hvS'').1
  have hnumv : t''.num v = t.n := by simp [St.num, hlv'']
  have htn : t.n < tc.n := by have := h.n; omega
  obtain ⟨lv', hly, hcase⟩ := hsc
  have hnumy : t''.num y = tc.n := by simp [St.num, hly]
  have hlowy : t''.low y = lv' := by simp [St.low, hly]
  have hR' := h.rel.trans hR
  have hE : (gr σ'').E = (gr σc).E := hR.gE
  have hlowm : (t''.merge t.A v y).low v = min (t''.low v) (t''.low y) := by
    simp [St.low, merge_ix]
  have hnumm : ∀ x, (t''.merge t.A v y).num x = t''.num x := fun x =>
    setLow_num ({ t'' with A := t.A ++ [v] } : St InstId) v x hvv''
  have hinv : TInv (gr σ'') (t''.merge t.A v y) := by
    rcases hcase with ⟨hex, hlv', hA⟩ | ⟨hyS, hlt, hA, hdw, hpar⟩
    · -- popped: no change
      have hmin : min (t''.low v) (t''.low y) = t''.low v := by
        rw [hlowy, hlv']; omega
      have heq : t''.merge t.A v y = t'' := by
        obtain ⟨S, A, ix, par, n⟩ := t''
        simp only [St.merge, St.setLow] at *
        rw [hmin]
        have hA' : A = t.A ++ [v] := by rw [hA, h.act]
        subst hA'
        congr 1
        funext x
        by_cases hx : x = v
        · subst hx; simp [St.num, St.low, hlv'']
        · simp [hx]
      rw [heq]; exact hT
    · have hA' : t''.A = t.A ++ [v, y] := by rw [hA, h.act]; simp
      have hpar' : t''.par y = v := by rw [hpar, h.act]; simp
      have hlw : t''.low y < t''.num y := by rw [hlowy, hnumy]; exact hlt
      have he' : (gr σ'').E v y := by rw [hE]; exact he
      exact merge_inv hT hA' hlw hdw hpar' he'
  refine ⟨hR', hwf, hib, VisCount_merge hvv'' hcnt, ?_, by show t.n + 1 ≤ t''.n; have := h.n; omega,
    hinv, rfl, ⟨min (t''.low v) (t''.low y), by rw [merge_ix]; simp [hnumv]⟩, ?_, ?_, ?_⟩
  · have e1 := h.ext.trans hext
    exact e1.setIx hvis _ rfl (fun x hx => by rw [merge_ix]; simp [hx]) rfl
  · show t''.par v = _; rw [hext.par v hvv]; exact h.parv
  · obtain ⟨T, hT1⟩ := h.stk; obtain ⟨T2, hT2⟩ := hext.stk
    exact ⟨T ++ T2, by show t''.S = _; rw [hT2, hT1]; simp⟩
  · intro z hz hB
    have hlm : min (t''.low v) (t''.low y) ≤ t''.low v := Nat.min_le_left _ _
    rcases hB with hB | rfl
    · have hz' : σc.depEdge v z := by rw [← hR.depEdge]; exact hz
      have hd := hext.done hvv (fun x hx => (h.inv.onS x hx).1) (h.done z hz' hB)
      exact setLow_done hvv'' hd (fun _ => hlm)
    · rcases hcase with ⟨hex, -, -⟩ | ⟨hyS, hlt, -, -, -⟩
      · exact Or.inl hex
      · right; refine ⟨hyS, ?_⟩
        rw [hlowm, hnumm, hnumy]; omega

theorem LoopOk.mono {σ σc : RState} {t tc : St InstId} {v : InstId} {B B' : InstId → Prop}
    (h : LoopOk σ t v σc tc B) (hB : ∀ z, B' z → B z) : LoopOk σ t v σc tc B' :=
  ⟨h.rel, h.wf, h.ib, h.cnt, h.ext, h.n, h.inv, h.act, h.ixv, h.parv, h.stk,
    fun z hz hb => h.done z hz (hB z hb)⟩

/-- The edge `v → y` to a node on the stack: `if y.Index < v.Lowlink { v.Lowlink = y.Index }`. -/
theorem LoopOk.stacked {σ σc : RState} {t tc : St InstId} {v y : InstId} {B : InstId → Prop}
    (h : LoopOk σ t v σc tc B) (hvis : ¬ t.vis v) (hyS : y ∈ tc.S) (he : σc.depEdge v y) :
    LoopOk σ t v σc (if tc.num y < tc.low v then tc.setLow v (tc.num y) else tc)
      (fun z => B z ∨ z = y) := by
  have hvS : v ∈ tc.S := h.inv.actS v (by rw [h.act]; simp)
  have hvv : tc.vis v := (h.inv.onS v hvS).1
  have hA : tc.A = t.A ++ [v] := h.act
  split
  · rename_i hlt
    obtain ⟨lv, hlv⟩ := h.ixv
    refine ⟨h.rel, h.wf, h.ib, VisCount_setLow hvv h.cnt, ?_, h.n, lowStack_inv h.inv hA hyS he hlt,
      h.act, ⟨tc.num y, by simp [St.setLow, St.num, hlv]⟩, h.parv, h.stk, ?_⟩
    · exact h.ext.setIx hvis _ rfl (fun x hx => by simp [St.setLow, hx]) rfl
    · intro z hz hB
      rcases hB with hB | rfl
      · exact setLow_done hvv (h.done z hz hB) (fun _ => Nat.le_of_lt hlt)
      · right; refine ⟨hyS, ?_⟩; rw [setLow_low, setLow_num _ _ _ hvv]; simp
  · rename_i hge
    refine ⟨h.rel, h.wf, h.ib, h.cnt, h.ext, h.n, h.inv, h.act, h.ixv, h.parv, h.stk, ?_⟩
    intro z hz hB
    rcases hB with hB | rfl
    · exact h.done z hz hB
    · right; exact ⟨hyS, by omega⟩

section heap
variable [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] [go.Semantics]
variable [epaxos.Assumptions] [HasExt netExt] [π : NetProtoGS]
variable [state.Assumptions] [github_com.emirpasic.gods.maps.treemap.Assumptions] [TH : TreemapHyp GF]

theorem repInstsX_acc2 (γ : EpNames) (i : Nat) (r : Loc) (F : Nat → List Loc)
    (inst : InstId → Option InstRec) (ix : InstId → Option (Nat × Nat)) (x z : InstId)
    (hxz : x ≠ z) (hxq : x.q < nR) (hxi : x.i < MAX_INSTANCE) (hzq : z.q < nR)
    (hzi : z.i < MAX_INSTANCE) :
    repInstsX (GF := GF) γ i r F inst ix ⊢
      slotT γ i x (ptrOf F x) (inst x) (ix x) ∗ slotT γ i z (ptrOf F z) (inst z) (ix z) ∗
      (slotT γ i x (ptrOf F x) (inst x) (ix x) -∗ slotT γ i z (ptrOf F z) (inst z) (ix z) -∗
        repInstsX γ i r F inst ix) := by
  obtain ⟨xq, xi⟩ := x; obtain ⟨zq, zi⟩ := z
  dsimp only at *
  unfold repInstsX
  iintro ⟨%iss, %rows, #Hiss, #Hrows, %Hlen, Hrs⟩
  obtain ⟨rowx, Hrowx⟩ : ∃ row, rows[xq]? = some row :=
    ⟨rows[xq]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  obtain ⟨rowz, Hrowz⟩ : ∃ row, rows[zq]? = some row :=
    ⟨rows[zq]'(by omega), List.getElem?_eq_getElem (by omega)⟩
  by_cases hq : xq = zq
  · subst hq
    rw [Hrowx] at Hrowz; cases Hrowz
    have hii : xi ≠ zi := fun h => hxz (by rw [h])
    icases (bigSepL_lookup_acc Hrowx).1 $$ Hrs with ⟨⟨Hr, %Hl, Hps⟩, Hclose⟩
    have Hpx := ptrOf_get F ⟨xq, xi⟩ Hl hxi
    have Hpz := ptrOf_get F ⟨xq, zi⟩ Hl hzi
    icases bigSepL_acc2 Hpx Hpz hii $$ Hps with ⟨Hx, Hz, Hpclose⟩
    iframe Hx Hz
    iintro Hx Hz
    ihave Hps := Hpclose $$ Hx Hz
    ihave Hrs := Hclose $$ %rowx [Hr Hps]
    · iframe Hr Hps; ipureintro; exact Hl
    have hset : rows.set xq rowx = rows := by
      have := List.getElem?_eq_some_iff.mp Hrowx
      rw [← this.2]; exact List.set_getElem_self this.1
    rw [hset]
    iexists iss, rows; iframe Hiss Hrows Hrs; ipureintro; exact Hlen
  · icases bigSepL_acc2 Hrowx Hrowz hq $$ Hrs with ⟨⟨Hrx, %Hlx, Hpsx⟩, ⟨Hrz, %Hlz, Hpsz⟩, Hclose⟩
    have Hpx := ptrOf_get F ⟨xq, xi⟩ Hlx hxi
    have Hpz := ptrOf_get F ⟨zq, zi⟩ Hlz hzi
    icases (bigSepL_lookup_acc Hpx).1 $$ Hpsx with ⟨Hx, Hcx⟩
    icases (bigSepL_lookup_acc Hpz).1 $$ Hpsz with ⟨Hz, Hcz⟩
    iframe Hx Hz
    iintro Hx Hz
    ihave Hpsx := Hcx $$ %(ptrOf F ⟨xq, xi⟩) Hx
    ihave Hpsz := Hcz $$ %(ptrOf F ⟨zq, zi⟩) Hz
    have hsx : (F xq).set xi (ptrOf F ⟨xq, xi⟩) = F xq := by
      have := List.getElem?_eq_some_iff.mp Hpx
      rw [← this.2]; exact List.set_getElem_self this.1
    have hsz : (F zq).set zi (ptrOf F ⟨zq, zi⟩) = F zq := by
      have := List.getElem?_eq_some_iff.mp Hpz
      rw [← this.2]; exact List.set_getElem_self this.1
    rw [hsx] at *; rw [hsz]
    ihave Hrs := Hclose $$ [Hrx Hpsx] [Hrz Hpsz]
    · iframe Hrx; rw [hsx]; iframe Hpsx; ipureintro; exact Hlx
    · iframe Hrz Hpsz; ipureintro; exact Hlz
    iexists iss, rows; iframe Hiss Hrows Hrs; ipureintro; exact Hlen

/-! ## Held proposals: the reply token is spent -/

theorem propHeld_true (γ : EpNames) (i : Nat) (b : Bool) (g : Loc) (p : Proposal) :
    propHeld (GF := GF) γ i b g p ⊢ propHeld γ i true g p := by
  unfold propHeld
  iintro ⟨%pp, %w, %mu, %proxy, %addr, %c, %inp, %cv, H1, H2, H3, H4, H5, H6, -⟩
  iexists pp, w, mu, proxy, addr, c, inp, cv
  iframe H1 H2 H3 H4 H5 H6
  simp only [↓reduceIte]
  ipureintro; trivial

theorem propHeld_open (γ : EpNames) (i : Nat) (executed : Bool) (g : Loc) (p : Proposal) :
    propHeld (GF := GF) γ i executed g p ⊢
      ∃ (pp w mu : Loc) (proxy : Bool) (addr : GoString) (c : w64) (inp : KvI) (cv : state.Command),
        g ↦□ replica.defs.GPropose.mk pp w mu proxy addr ∗
        pp ↦□ replica.defs.Propose.mk (W32 0) (W32 (uint.Z c)) cv (W64 0) ∗ cmdOk cv (cmdOf inp) ∗
        clientConn γ p.cid c inp ∗ ⌜p.cmd = cmdOf inp⌝ ∗ clientWriter γ i w p.cid ∗
        (if executed then iprop(True) else replyTok γ i w) := by
  unfold propHeld; exact .rfl

theorem propHeld_eq (γ : EpNames) (i : Nat) (b b' : Bool) (g : Loc) (p : Proposal) (h : b = b') :
    propHeld (GF := GF) γ i b g p ⊢ propHeld γ i b' g p := by subst h; exact .rfl

theorem ownLbF_mono (γ : EpNames) (i : Nat) (f f' : Nat → Bool) (lbp : Loc) (lb : LbRec)
    (h : ∀ k, f k = true → f' k = true) :
    ownLbF (GF := GF) γ i f lbp lb ⊢ ownLbF γ i f' lbp lb := by
  unfold ownLbF
  iintro ⟨%y, %gs, %prs, Hy, %Hyf, Hps, Hrest⟩
  iexists y, gs, prs
  iframe Hy Hrest
  isplitr
  · ipureintro; exact Hyf
  rcases lb.clientProposals with _ | ps
  · iexact Hps
  · icases Hps with ⟨%Hp, #Hgs, Hbig⟩
    isplitr
    · ipureintro; exact Hp
    isplitr
    · iexact Hgs
    iapply (bigSepL_mono ?_) $$ Hbig
    intro k g _
    rcases hfk : f' k
    · have : f k = false := by
        rcases hf : f k
        · rfl
        · rw [h k hf] at hfk; cases hfk
      rw [this]
    · exact propHeld_true γ i _ g _

/-- `e.r.ReplyProposeTS(...)` through the embedded framework. -/
theorem wp_ep_ReplyProposeTS (hRP : replica.Replica.ReplyProposeTS.spec (GF := GF)) (γ : EpNames) (r rr : Loc)
    (i : Nat) (L : List GoString) (p : FwPtrs) (Rext : IProp GF) (reply wr mu : Loc)
    (cid : Nat) (o : KvO) (v : List w8) (vsl : GoSlice) (ts : w64) (dq dq' : DFrac) :
    {{ pkgInit_epaxos (GF := GF) ∗ pkgInit_replica ∗ efld r go!"Replica" ↦□ rr ∗
        ⌜replyValOk o v ∧ v.length < 2 ^ 16⌝ ∗ isReplicaFw γ rr i L p Rext ∗
        reply ↦{dq} replica.defs.ProposeReplyTS.mk okTRUE (W32 0) vsl ts ∗ vsl ↦*{dq'} v ∗
        clientWriter γ i wr cid ∗ replyTok γ i wr ∗ fired γ cid o }}
      (App (App (App (Val (r @!! go.GoType.PointerType epaxos.Replica.ty @!! go!"ReplyProposeTS"))
        (Val #reply)) (Val #wr)) (Val #mu))
    {{ RET #(); reply ↦{dq} replica.defs.ProposeReplyTS.mk okTRUE (W32 0) vsl ts ∗ vsl ↦*{dq'} v }} := by
  wp_start as ⟨#Hrr, %Hv, #Hfw, Hrep, Hvs, #Hcw, Htok, #Hf⟩
  wp_auto
  wp_apply (hRP γ rr i L p Rext reply wr mu cid o v vsl ts dq dq') $$ [$Hfw $Hrep $Hvs $Hcw $Htok $Hf]
  · ipureintro; exact Hv
  iintro Hpost
  iapply HΦ $$ Hpost

/-- An instance's bookkeeping field `lb'` with image `o` and per-proposal flags `f`. -/
def lbRes (γ : EpNames) (i : Nat) (f : Nat → Bool) (yl : Loc) : Option LbRec → IProp GF
  | none => iprop(⌜yl = null⌝)
  | some lb => iprop(⌜yl ≠ null⌝ ∗ ownLbF γ i f yl lb)

theorem lbRes_mono (γ : EpNames) (i : Nat) (f f' : Nat → Bool) (yl : Loc) (o : Option LbRec)
    (h : ∀ k, f k = true → f' k = true) : lbRes (GF := GF) γ i f yl o ⊢ lbRes γ i f' yl o := by
  rcases o with _ | lb
  · exact .rfl
  · exact sep_mono_right (ownLbF_mono γ i f f' yl lb h)

end heap

end Perennial.github_com.imdea_software.swiftpaxos_epaxos
