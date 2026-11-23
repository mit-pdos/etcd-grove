/-
Ported from dsverify-lab examples/gryff/proof/GryffProof/PureLa/Defs.lean (run gryff-bump-1, lab master 915f964; notes/dsv-gryff.md).

Unit L-a: **the tag bound** over every carrier of tags in a configuration (stores, `prevValTag`,
copies' bases and recovery candidates, the coordinator's read and write records, every message in
flight): `ts ∈ [0, T]`, `rmwc ∈ [0, E]`. `T` is a potential over the configuration (client
requests handled minus write records that have not chosen their `WriteTag`: it grows by one when a
`WriteTag` is chosen, `ts + 1`); `E` counts the executions with a result so far (an execution's
result is its base's or `prevValTag`'s tag with `rmwc + 1`).

This module: the predicates and their frame lemmas.
-/
module

public import Dsverify.Proof.gryff.PureL.Frame

@[expose] public section

set_option linter.unusedSectionVars false

namespace Perennial.gryff.pure.La

open model kahn Perennial.gryff.pure

/-- A tag within the bounds. -/
structure TB (T E : Int) (t : model.Tag) : Prop where
  ts0 : 0 ≤ sint.Z t.ts
  ts1 : sint.Z t.ts ≤ T
  r0 : 0 ≤ sint.Z t.rmwc
  r1 : sint.Z t.rmwc ≤ E

def OVB (T E : Int) (o : Option ValTag) : Prop := ∀ v, o = some v → TB T E v.t

def CB (T E : Int) (c : Copy) : Prop :=
  TB T E c.base.t ∧ ∀ lb, c.lb = some lb → ∀ ri, lb.recoveryInst = some ri → TB T E ri.base.t

def WOB (T E : Int) (w : WriteOp) : Prop :=
  TB T E w.maxValTag.t ∧ ∀ t, w.writeTag = some t → TB T E t

def ROB (T E : Int) (r : ReadOp) : Prop := OVB T E r.maxValTag ∧ OVB T E r.readValTag

/-- A replica state's carriers within the bounds. -/
structure SB (T E : Int) (s : RState) : Prop where
  tag : TB T E s.tag
  pvt : OVB T E s.prevValTag
  inst : ∀ q i c, s.inst q i = some c → CB T E c
  wops : ∀ e ∈ s.wops, WOB T E e.2
  rops : ∀ e ∈ s.rops, ROB T E e.2

/-- A message's carriers within the bounds (a `Write1`'s dependency has no key: never read). -/
def MB (T E : Int) : Msg → Prop
  | .read1 m => TB T E m.d.vt.t ∧ TB T E m.vt.t
  | .read2 m => TB T E m.vt.t
  | .read1Reply m => TB T E m.vt.t
  | .read2Reply _ => True
  | .write1 m => slt m.d.key 0 = true
  | .write2 m => TB T E m.vt.t
  | .write1Reply m => TB T E m.vt.t
  | .write2Reply _ => True
  | .preAccept m => TB T E m.base.t
  | .preAcceptReply m => TB T E m.base.t
  | .preAcceptOK _ => True
  | .accept m => TB T E m.base.t
  | .acceptReply _ => True
  | .commit m => TB T E m.base.t
  | .prepare _ => True
  | .prepareReply m => TB T E m.base.t
  | .executed _ => True
  | .executeOverwrite m => TB T E m.t

def OutB (T E : Int) : Out → Prop
  | .send _ m => MB T E m
  | .ext _ => True

def OB (T E : Int) (o : List Out) : Prop := ∀ x ∈ o, OutB T E x

/-! ## Monotonicity -/

section mono
variable {T E T' E' : Int} (hT : T ≤ T') (hE : E ≤ E')
include hT hE

theorem TB.mono {t : model.Tag} (h : TB T E t) : TB T' E' t :=
  ⟨h.ts0, by have := h.ts1; omega, h.r0, by have := h.r1; omega⟩

theorem OVB.mono {o : Option ValTag} (h : OVB T E o) : OVB T' E' o :=
  fun v hv => (h v hv).mono hT hE

theorem CB.mono {c : Copy} (h : CB T E c) : CB T' E' c :=
  ⟨h.1.mono hT hE, fun lb hl ri hr => (h.2 lb hl ri hr).mono hT hE⟩

theorem SB.mono {s : RState} (h : SB T E s) : SB T' E' s where
  tag := h.tag.mono hT hE
  pvt := h.pvt.mono hT hE
  inst q i c hc := (h.inst q i c hc).mono hT hE
  wops e he := ⟨(h.wops e he).1.mono hT hE, fun t ht => ((h.wops e he).2 t ht).mono hT hE⟩
  rops e he := ⟨(h.rops e he).1.mono hT hE, (h.rops e he).2.mono hT hE⟩

theorem MB.mono {m : Msg} (h : MB T E m) : MB T' E' m := by
  cases m <;> simp only [MB] at h ⊢
  all_goals first
    | trivial
    | exact h
    | exact h.mono hT hE
    | exact ⟨h.1.mono hT hE, h.2.mono hT hE⟩

theorem OB.mono {o : List Out} (h : OB T E o) : OB T' E' o := by
  intro x hx
  have := h x hx
  cases x with
  | send d m => exact MB.mono hT hE this
  | ext => trivial
end mono

/-! ## Tags -/

theorem TB_tag0 {T E : Int} (hT : 0 ≤ T) (hE : 0 ≤ E) : TB T E tag0 := by
  have : sint.Z (0 : w32) = 0 := by decide
  exact ⟨by simp only [tag0, this]; omega, by simp only [tag0, this]; omega,
    by simp only [tag0, this]; omega, by simp only [tag0, this]; omega⟩

theorem TB_vt0 {T E : Int} (hT : 0 ≤ T) (hE : 0 ≤ E) : TB T E vt0.t := TB_tag0 hT hE

/-! ## Outputs -/

theorem OB_nil {T E : Int} : OB T E [] := by simp [OB]
theorem OB_append {T E : Int} {a b : List Out} (ha : OB T E a) (hb : OB T E b) : OB T E (a ++ b) := by
  intro x hx; rcases List.mem_append.1 hx with h | h
  · exact ha x h
  · exact hb x h
theorem OB_ext {T E : Int} {x : Ext} : OB T E [.ext x] := by
  intro y hy; simp at hy; subst hy; trivial

theorem OB_sendTo {T E : Int} {q : w32} {m : Msg} {x : Out} (h : sendTo q m = some x)
    (hm : MB T E m) : OB T E [x] := by
  obtain ⟨d, -, rfl⟩ := sendTo_out h
  intro y hy; simp at hy; subst hy; exact hm

theorem OB_sendPeer {T E : Int} {s : RState} {q : w32} {m : Msg} {x : Out}
    (h : sendPeer s q m = some x) (hm : MB T E m) : OB T E [x] := by
  unfold sendPeer at h; split at h
  · cases h
  · exact OB_sendTo h hm

theorem OB_mapM_sendTo {T E : Int} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendTo q m) = some r) (hm : MB T E m) : OB T E r := by
  intro y hy
  obtain ⟨a, -, ha⟩ := mapM_some_mem h y hy
  exact OB_sendTo ha hm y (List.mem_singleton_self _)

theorem OB_mapM_sendPeer {T E : Int} {s : RState} {l : List w32} {m : Msg} {r : List Out}
    (h : l.mapM (fun q => sendPeer s q m) = some r) (hm : MB T E m) : OB T E r := by
  intro y hy
  obtain ⟨a, -, ha⟩ := mapM_some_mem h y hy
  exact OB_sendPeer ha hm y (List.mem_singleton_self _)

theorem OB_bcast {T E : Int} {s : RState} {m : Msg} {r : List Out} (h : bcast s m = some r)
    (hm : MB T E m) : OB T E r := OB_mapM_sendPeer h hm

/-! ## States -/

theorem SB.of_eq {T E : Int} {s s' : RState} (h : SB T E s) (e1 : s'.tag = s.tag)
    (e2 : s'.prevValTag = s.prevValTag) (e3 : s'.inst = s.inst) (e4 : s'.wops = s.wops)
    (e5 : s'.rops = s.rops) : SB T E s' where
  tag := e1 ▸ h.tag
  pvt := e2 ▸ h.pvt
  inst := e3 ▸ h.inst
  wops := e4 ▸ h.wops
  rops := e5 ▸ h.rops

theorem SB.setInst {T E : Int} {s : RState} (h : SB T E s) {q i : w32} {c : Copy}
    (hc : CB T E c) : SB T E (s.setInst q i c) := by
  refine ⟨h.tag, h.pvt, fun q' i' c' hc' => ?_, h.wops, h.rops⟩
  simp only [RState.setInst] at hc'
  split at hc'
  · cases hc'; exact hc
  · exact h.inst q' i' c' hc'

theorem SB.setCrt {T E : Int} {s : RState} (h : SB T E s) {q x : w32} : SB T E (s.setCrt q x) :=
  h.of_eq rfl rfl rfl rfl rfl

theorem updateConflicts_fields (s : RState) (cmds : List Cmd) (q i sq : w32) :
    let s' := updateConflicts s cmds q i sq
    s'.tag = s.tag ∧ s'.prevValTag = s.prevValTag ∧ s'.inst = s.inst ∧ s'.wops = s.wops ∧
      s'.rops = s.rops ∧ s'.nReqs = s.nReqs := by
  unfold updateConflicts
  apply forIn_id_inv (P := fun x : RState => x.tag = s.tag ∧ x.prevValTag = s.prevValTag ∧
    x.inst = s.inst ∧ x.wops = s.wops ∧ x.rops = s.rops ∧ x.nReqs = s.nReqs) _ _ _
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro a b hb
  simpa using hb

theorem SB.updateConflicts {T E : Int} {s : RState} (h : SB T E s) {cmds : List Cmd}
    {q i sq : w32} : SB T E (updateConflicts s cmds q i sq) := by
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := updateConflicts_fields s cmds q i sq
  exact h.of_eq e1 e2 e3 e4 e5

theorem updateCommitted_fields {s s' : RState} {q : w32} (h : updateCommitted s q = some s') :
    s'.tag = s.tag ∧ s'.prevValTag = s.prevValTag ∧ s'.inst = s.inst ∧ s'.wops = s.wops ∧
      s'.rops = s.rops ∧ s'.nReqs = s.nReqs := by
  unfold updateCommitted at h; opeel h
  all_goals (cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)

theorem SB.updateCommitted {T E : Int} {s s' : RState} (h : SB T E s) {q : w32}
    (hu : updateCommitted s q = some s') : SB T E s' := by
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := updateCommitted_fields hu
  exact h.of_eq e1 e2 e3 e4 e5

theorem SB.overwrite {T E : Int} {s : RState} (h : SB T E s) {v : w64} {t : model.Tag}
    (ht : TB T E t) : SB T E (s.overwrite v t) := by
  unfold RState.overwrite; split
  · exact ⟨ht, h.pvt, h.inst, h.wops, h.rops⟩
  · exact h

end Perennial.gryff.pure.La
