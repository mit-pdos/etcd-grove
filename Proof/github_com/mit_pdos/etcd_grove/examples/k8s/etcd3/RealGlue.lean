/-
Lean-first (no Rocq counterpart).

# `realCheck`'s pure glue (k8s 7g step 5)

What `realCheck`'s proof needs of the history, stated over one ghost value per operation (`GOp`: its input,
output, unary answer and watch events, as `opsIoOk (k8setcd3S g0)` gives them, `GOk`):

- `histR lops vs`: the history as recorded operations (`ROp`); `kM_lin`: the driver's linearization of
  `histOf lops` is one of `histR lops vs` for `kM g0`;
- `realM_lin_iff`: a history of boxed checker operations (`L`, `P`) linearizes for `realM L init` exactly
  when its unary values do for `realS init`;
- `realCheck_pure`: B2's linearization of the unary operations, and for any linearization of them, B4's
  replay (each operation validating, with `Replay.Validate`'s premises) and B5 for every watch that ran.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealMS
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealRun
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealLin
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealWatch
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchRep

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris k8s_etcd3 k8sDeep github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section go
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- One operation's ghost value in `realCheck`'s proof: its input, output, unary answer (`rawOk`'s) and
watch events (`wrawOk`'s). -/
abbrev GOp := Input × Output × RResp × List REv

/-- The recorded operation of a ghost value. -/
def ropOf (v : GOp) : ROp := (v.1, plainOut v.2.1, v.2.2.1)

/-- **The history as recorded operations.** -/
def histR (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp) : List (Op ROp) :=
  List.zipWith (fun o v => (⟨ropOf v, sint.Z o.Call', sint.Z o.Return'⟩ : Op ROp)) lops vs

/-- **What `opsIoOk (k8setcd3S g0)` and `failureFree` give of one operation**, with its ghost value. -/
def GOk (s0 : w64) (o : github_com.anishathalye.porcupine.Operation) (v : GOp) : Prop :=
  o.Input' = boxIn v.1 ∧ o.Output' = boxOut v.2.1 ∧ GenInA v.1 ∧ FloorOk s0 v.1 ∧
  okOut v.1 v.2.1 = true ∧
  (v.1.Kind' = W64 5 → v.2.1.Err' ≠ W64 4 ∧ ∀ n, parseRVD v.1.MinRV' = some n → uint.Z n < 2 ^ 63) ∧
  (v.1.Kind' ≠ W64 5 → RawRel v.1 (plainOut v.2.1) v.2.2.1) ∧
  (v.1.Kind' = W64 5 → v.1.Skip' = false →
    decWEventsL v.2.1.WEvents' = some (v.2.2.2.map toWEvL) ∧ WatchFromL s0 v.1 (v.2.2.2.map toWEvL))

/-- **The ghost values of a history.** -/
def GOks (s0 : w64) (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp) : Prop :=
  vs.length = lops.length ∧ ∀ (k : Nat) (o : github_com.anishathalye.porcupine.Operation) (v : GOp),
    lops[k]? = some o → vs[k]? = some v → GOk s0 o v

theorem histR_length (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp)
    (h : vs.length = lops.length) : (histR lops vs).length = lops.length := by
  unfold histR; rw [List.length_zipWith, h, Nat.min_self]

theorem histR_getElem? (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp) (k : Nat)
    (o : github_com.anishathalye.porcupine.Operation) (v : GOp)
    (ho : lops[k]? = some o) (hv : vs[k]? = some v) :
    (histR lops vs)[k]? = some ⟨ropOf v, sint.Z o.Call', sint.Z o.Return'⟩ := by
  unfold histR; rw [List.getElem?_zipWith, ho, hv]

theorem mem_histR (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp)
    (h : vs.length = lops.length) (o : Op ROp) (ho : o ∈ histR lops vs) :
    ∃ (k : Nat) (op : github_com.anishathalye.porcupine.Operation) (v : GOp), lops[k]? = some op ∧
      vs[k]? = some v ∧ o = ⟨ropOf v, sint.Z op.Call', sint.Z op.Return'⟩ := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ho
  have hk' : k < lops.length := by rw [histR_length lops vs h] at hk; exact hk
  have hkv : k < vs.length := by rw [h]; exact hk'
  refine ⟨k, lops[k], vs[k], List.getElem?_eq_getElem hk', List.getElem?_eq_getElem hkv, ?_⟩
  have := histR_getElem? lops vs k lops[k] vs[k] (List.getElem?_eq_getElem hk')
    (List.getElem?_eq_getElem hkv)
  rw [List.getElem?_eq_getElem hk] at this
  exact Option.some.inj this

/-- A unary operation's answer has `Model.Step`'s pure premises (`stepIn`). -/
theorem rawRel_stepIn (x : Input) (y : Output) (r : RResp) (hx : GenIn x) (hraw : RawRel x y r) :
    stepIn x r := by
  have key : flatE r.err ∧ (x.Kind' = W64 4 → listOrNilD r.obj) ∧
      (isWriteL x = false → x.Kind' ≠ W64 4 → objOrNilD r.obj) := by
    unfold RawRel at hraw
    split at hraw
    · split at hraw
      · obtain ⟨its, -, -, rfl⟩ := hraw
        exact ⟨trivial, fun _ => trivial, fun _ h => absurd ‹_› h⟩
      · subst hraw
        exact ⟨trivial, fun h => absurd h ‹_›, fun _ _ => trivial⟩
    · split at hraw
      · subst hraw; exact ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩
      · split at hraw
        · subst hraw; exact ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩
        · split at hraw
          · subst hraw
            refine ⟨?_, fun _ => trivial, fun _ _ => trivial⟩
            dsimp only
            split <;> trivial
          · split at hraw
            · subst hraw; exact ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩
            · split at hraw
              · subst hraw; exact ⟨trivial, fun _ => trivial, fun _ _ => trivial⟩
              · exact hraw.elim
  exact genIn_stepIn x r hx key.1 key.2.1 key.2.2

/-- A unary input `Gen` may return is not a watch's. -/
theorem genIn_of_genInA (x : Input) (hx : GenInA x) (h5 : x.Kind' ≠ W64 5) : GenIn x :=
  hx.elim id fun hw => absurd hw.1 h5

/-- **B1's facts of an operation** (`OpOk`), the step's fit (`OpFits`) and `stepIn` of a unary one. -/
theorem gOk_facts (s0 : w64) (o : github_com.anishathalye.porcupine.Operation) (v : GOp)
    (h : GOk s0 o v) :
    OpOk (ropOf v) ∧ (v.1.Kind' ≠ W64 5 → OpFits v.1 ∧ stepIn v.1 v.2.2.1) := by
  obtain ⟨-, -, hA, -, hokO, hw, hraw, -⟩ := h
  have hun : v.1.Kind' ≠ W64 5 → OpFits v.1 ∧ stepIn v.1 v.2.2.1 := by
    intro h5
    have hg := genIn_of_genInA v.1 hA h5
    have hs := rawRel_stepIn v.1 _ v.2.2.1 hg (hraw h5)
    exact ⟨⟨hs.2.1, by have := hg.2.2.1; omega⟩, hs⟩
  refine ⟨⟨?_, fun h5 => ⟨hraw h5, fun h4 => ?_, fun h4 => (hun h5).2.2.2.1 h4⟩⟩, hun⟩
  · show v.2.1.Err' ≠ W64 4
    by_cases h5 : v.1.Kind' = W64 5
    · exact (hw h5).1
    · unfold okOut at hokO; rw [if_neg h5] at hokO; exact of_decide_eq_true hokO
  · have hg := genIn_of_genInA v.1 hA h5
    exact ⟨(hg.1.2.2.2.2.2 h4).1, genIn_listConsL v.1 hg h4, ((hun h5).2.2.2.2 h4).2⟩

include sem package_sem in
/-- **The driver's linearization, on recorded operations.** -/
theorem kM_lin (g0 : HSt) (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp)
    (hvs : GOks g0.st.rv lops vs)
    (hlin : IsLinearization (linkv.pM (kSpec g0) decOp) (github_com.anishathalye.porcupine.histOf lops)
      (List.range lops.length)) :
    IsLinearization (kM g0) (histR lops vs) (List.range lops.length) := by
  refine isLinearization_map (linkv.pM (kSpec g0) decOp) (kM g0) _ _ _ ?_ ?_ rfl hlin
  · unfold github_com.anishathalye.porcupine.histOf; rw [List.length_map, histR_length lops vs hvs.1]
  · intro k o o' ho ho'
    unfold github_com.anishathalye.porcupine.histOf at ho
    rw [List.getElem?_map] at ho
    cases hl : lops[k]? with
    | none => rw [hl] at ho; cases ho
    | some op =>
      rw [hl] at ho
      have hkv : k < vs.length := by
        rw [hvs.1]; exact (List.getElem?_eq_some_iff.1 hl).1
      have hv := List.getElem?_eq_getElem hkv
      rw [histR_getElem? lops vs k op vs[k] hl hv] at ho'
      cases ho; cases ho'
      obtain ⟨hi, hout, -⟩ := hvs.2 k op vs[k] hl hv
      refine ⟨rfl, rfl, fun s => ?_⟩
      simp only [github_com.anishathalye.porcupine.opOf, linkv.pM, hi, hout, ropOf]
      rw [decOp_box (sem := sem) (package_sem := package_sem)]

/-- A history of boxed checker operations: the entries' boxes, at the unary operations' times. -/
def boxH (L : List (github_com.anishathalye.porcupine.OpV × (Input × RResp))) (U : List (Op (Input × RResp))) :
    List (Op github_com.anishathalye.porcupine.OpV) :=
  List.zipWith (fun e u => (⟨e.1, u.call, u.ret⟩ : Op github_com.anishathalye.porcupine.OpV)) L U

/-- **A history of boxed checker operations linearizes for `realM` exactly when its values do for
`realS`.** -/
theorem realM_lin_iff (init : RM) (L : List (github_com.anishathalye.porcupine.OpV × (Input × RResp)))
    (U : List (Op (Input × RResp))) (hag : StepAgree L) (hlen : L.length = U.length)
    (hval : ∀ (k : Nat) (e : github_com.anishathalye.porcupine.OpV × (Input × RResp)) (u : Op (Input × RResp)),
      L[k]? = some e → U[k]? = some u → e.2 = u.val) (π : List Nat) :
    IsLinearization (realS init) U π ↔
      IsLinearization (realM L init) (boxH L U) π := by
  have hlen' : U.length = (boxH L U).length := by
    unfold boxH; rw [List.length_zipWith, hlen, Nat.min_self]
  have hat : ∀ (k : Nat) (u : Op (Input × RResp)) (o' : Op github_com.anishathalye.porcupine.OpV),
      U[k]? = some u → (boxH L U)[k]? = some o' →
      ∃ e, L[k]? = some e ∧ e ∈ L ∧ o' = ⟨e.1, u.call, u.ret⟩ ∧ e.2 = u.val := by
    intro k u o' hu ho'
    unfold boxH at ho'
    rw [List.getElem?_zipWith, hu] at ho'
    cases hl : L[k]? with
    | none => rw [hl] at ho'; cases ho'
    | some e =>
      rw [hl] at ho'
      cases ho'
      exact ⟨e, rfl, List.mem_of_getElem? hl, rfl, hval k e u hl hu⟩
  constructor
  · refine isLinearization_map _ _ _ _ _ hlen' ?_ rfl
    intro k u o' hu ho'
    obtain ⟨e, -, he, rfl, hev⟩ := hat k u o' hu ho'
    refine ⟨rfl, rfl, fun s => ?_⟩
    rw [realM_step L init hag e he s, hev]
  · refine isLinearization_map _ _ _ _ _ hlen'.symm ?_ rfl
    intro k o' u ho' hu
    obtain ⟨e, -, he, rfl, hev⟩ := hat k u o' hu ho'
    refine ⟨rfl, rfl, fun s => ?_⟩
    rw [realM_step L init hag e he s, hev]

/-- The seeded store's objects fit the checker's model (`itemsFitL`). -/
theorem itemsFitL_absR (st : GSt) (hst : StOk st) (hok : ∀ it ∈ st.items, itemOk it.obj') :
    itemsFitL (absR st) := by
  intro k o hk
  have hm := ofList_lookup_mem _ k o hk
  obtain ⟨it, hit, he⟩ := List.mem_map.1 hm
  cases he
  exact ⟨(hok it hit).1, hst.2 it hit⟩

/-- The seeded store's keys are distinct (`initialModel`'s premise). -/
theorem storeKeys_nodup (st : GSt) (hst : StOk st) : (st.items.map fun it => storeKeyL it.key').Nodup := by
  have h1 : (st.items.map item.key').Pairwise go.GoStringLt := hst.1
  unfold List.Nodup
  rw [List.pairwise_map] at h1 ⊢
  exact h1.imp fun {a b} (h : go.GoStringLt a.key' b.key') (e : storeKeyL a.key' = storeKeyL b.key') =>
    go.goStringLt_irrefl b.key' (by rw [storeKeyL_inj e] at h; exact h)

theorem mem_vals {α : Type} (h : List (Op α)) (π : List Nat) (a : α) (ha : a ∈ vals h π) :
    ∃ o ∈ h, o.val = a := by
  unfold vals at ha
  obtain ⟨k, -, hk⟩ := List.mem_filterMap.1 ha
  cases e : h[k]? with
  | none => rw [e] at hk; cases hk
  | some o => rw [e] at hk; cases hk; exact ⟨o, List.mem_of_getElem? e, rfl⟩

theorem mem_fmapH {α β : Type} (f : α → Option β) (h : List (Op α)) (u : Op β)
    (hu : u ∈ github_com.anishathalye.porcupine.Theory.fmapH f h) : ∃ o ∈ h, f o.val = some u.val := by
  unfold github_com.anishathalye.porcupine.Theory.fmapH at hu
  obtain ⟨o, ho, he⟩ := List.mem_filterMap.1 hu
  cases e : f o.val with
  | none => rw [e] at he; cases he
  | some b => rw [e] at he; cases he; exact ⟨o, ho, e⟩

include sem package_sem in
/-- **`realCheck`'s pure core.** From the driver's `Ok` (its linearization, the operations' facts) and the
seeded configuration's: B2's linearization of the unary operations for `realS`; and along any
linearization of them, B4's replay (every operation validating, with `Replay.Validate`'s premises) and B5's
acceptance of every watch that ran (with `ValidateWatch`'s input premise). -/
theorem realCheck_pure (g0 : HSt) (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp)
    (hvs : GOks g0.st.rv lops vs)
    (hlin : IsLinearization (linkv.pM (kSpec g0) decOp) (github_com.anishathalye.porcupine.histOf lops)
      (List.range lops.length))
    (hrun0 : RunOk g0) (hn : uint.nat g0.st.rv + lops.length < 2 ^ 63) :
    (∃ π2, IsLinearization (realS (absR g0.st)) (fmapH unaryOf (histR lops vs)) π2) ∧
    itemsFitL (absR g0.st) ∧
    (∀ op ∈ (fmapH unaryOf (histR lops vs)).map Op.val, stepIn op.1 op.2) ∧
    ∀ lin2, IsLinearization (realS (absR g0.st)) (fmapH unaryOf (histR lops vs)) lin2 →
      ∃ R, replayL (absR g0.st) (vals (fmapH unaryOf (histR lops vs)) lin2) = some R ∧
        (∀ op ∈ vals (fmapH unaryOf (histR lops vs)) lin2, rvalidateL R op.1 op.2 = true ∧
          (op.1.Kind' = W64 4 → listExpOk R op.1 op.2)) ∧
        ∀ (k : Nat) (v : GOp), vs[k]? = some v → v.1.Kind' = W64 5 → v.1.Skip' = false →
          wInPre v.1 ∧ validateWatchL R v.1 (realEventsL v.1 v.2.2.2) = true := by
  have hlen := histR_length lops vs hvs.1
  have hkM := kM_lin (sem := sem) (package_sem := package_sem) g0 lops vs hvs hlin
  -- every recorded operation's facts
  have hfacts : ∀ o ∈ histR lops vs, ∃ (k : Nat) (op : github_com.anishathalye.porcupine.Operation) (v : GOp),
      lops[k]? = some op ∧ vs[k]? = some v ∧
      o.val = ropOf v ∧ GOk g0.st.rv op v := by
    intro o ho
    obtain ⟨k, op, v, hl, hv, rfl⟩ := mem_histR lops vs hvs.1 o ho
    exact ⟨k, op, v, hl, hv, rfl, hvs.2 k op v hl hv⟩
  have hops : ∀ o ∈ histR lops vs, OpOk o.val := by
    intro o ho
    obtain ⟨k, op, v, -, -, he, hg⟩ := hfacts o ho
    rw [he]; exact (gOk_facts _ op v hg).1
  have hpres : ∀ o ∈ histR lops vs, ∀ h, RunOk h → uint.nat h.st.rv + 1 < 2 ^ 63 → o.val.1.Kind' ≠ W64 5 →
      RunOk (kstepL o.val.1 h).1 ∧ uint.nat (kstepL o.val.1 h).1.st.rv ≤ uint.nat h.st.rv + 1 := by
    intro o ho h hr hroom h5
    obtain ⟨k, op, v, -, -, he, hg⟩ := hfacts o ho
    rw [he] at h5 ⊢
    exact kstepL_runOk _ h hr hroom ((gOk_facts _ op v hg).2 h5).1
  have hfl : ∀ o ∈ histR lops vs, FloorOk g0.st.rv o.val.1 := by
    intro o ho
    obtain ⟨k, op, v, -, -, he, hg⟩ := hfacts o ho
    rw [he]; exact hg.2.2.2.1
  have hn' : uint.nat g0.st.rv + (histR lops vs).length < 2 ^ 63 := by rw [hlen]; exact hn
  have hstep : ∀ op ∈ (fmapH unaryOf (histR lops vs)).map Op.val, stepIn op.1 op.2 ∧
      ∃ y, RawRel op.1 y op.2 := by
    intro op hop
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hop
    obtain ⟨o, ho, hf⟩ := mem_fmapH unaryOf _ u hu
    obtain ⟨k, op', v, -, -, he, hg⟩ := hfacts o ho
    rw [he] at hf
    unfold unaryOf ropOf at hf
    by_cases h5 : v.1.Kind' = W64 5
    · rw [if_pos h5] at hf; cases hf
    · rw [if_neg h5] at hf
      rw [← Option.some.inj hf]
      exact ⟨((gOk_facts _ op' v hg).2 h5).2, _, hg.2.2.2.2.2.2.1 h5⟩
  have hfit := itemsFitL_absR g0.st hrun0.1.1 hrun0.1.2.1
  refine ⟨⟨_, realS_isLinearization g0 (histR lops vs) _ RunOk hkM hops (fun h hr => hr.1) hrun0
    hpres hn'⟩, hfit, fun op hop => (hstep op hop).1, fun lin2 h2 => ?_⟩
  obtain ⟨R, hR, hval, hw⟩ := realReplay_ok g0 (histR lops vs) (List.range lops.length) hkM hops hrun0 hpres hfl hn' lin2 h2
  refine ⟨R, hR, fun op hop => ?_, fun k v hv h5 hsk => ?_⟩
  · have hmem : op ∈ (fmapH unaryOf (histR lops vs)).map Op.val := by
      obtain ⟨u, hu, rfl⟩ := mem_vals _ _ op hop
      exact List.mem_map_of_mem hu
    obtain ⟨hs, y, hraw⟩ := hstep op hmem
    exact ⟨hval op hop, fun h4 => listExpOk_of R op.1 y op.2 hraw hs h4 (hval op hop)⟩
  · have hk : k < lops.length := by rw [← hvs.1]; exact (List.getElem?_eq_some_iff.1 hv).1
    have hl := List.getElem?_eq_getElem hk
    have hg := hvs.2 k lops[k] v hl hv
    have ho : (⟨ropOf v, sint.Z lops[k].Call', sint.Z lops[k].Return'⟩ : Op ROp) ∈ histR lops vs :=
      List.mem_of_getElem? (histR_getElem? lops vs k lops[k] v hl hv)
    obtain ⟨hv', hR', hrun', hle, hok⟩ := hw _ ho h5
    obtain ⟨-, -, hA, -, hokO, hwk, -, hwr⟩ := hg
    have hW : GenInW v.1 := hA.elim (fun hg => absurd h5 (by
      rcases hg.2.1 with e | e | e | e | e <;> rw [e] <;> decide)) id
    obtain ⟨-, -, -, hWs⟩ := hW
    obtain ⟨hpfx, hpk, -, n, hn1, hn2, hwin, hb, hsi, hlim⟩ := hWs hsk
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hpk
    have hfail : v.2.1.WFailed' = false := by
      unfold okOut at hokO; rw [if_pos h5, hsk] at hokO
      simpa using hokO
    obtain ⟨hdec, hfrom⟩ := hwr h5 hsk
    have hlenv : hv'.hist.length = uint.nat hv'.st.rv := hrun'.2.1.1
    refine ⟨⟨by rw [prepareKeyM_nil hp]; rfl, hlim, n, hn1, by omega, hwin, hb, hsi⟩, ?_⟩
    exact validateWatchL_of_watchOkL g0.st.rv R hv' v.1 (plainOut v.2.1) v.2.2.2 hlenv
      (histWf_of_histGood v.1 _ hrun'.2.2.2.1 (by rw [hlenv]; exact hrun'.2.2.2.2)) hrun'.2.2.1
      (by have := hrun0.1.2.2.2.1; omega) hle hR' (fun n hn => by have := (hwk h5).2 n hn; word) hsk hfail hdec hfrom hok

/-! ## `realCheck`'s first loop -/

/-- The unary operations among the first `j`. -/
abbrev Uj (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp) (j : Nat) :
    List (Op (Input × RResp)) :=
  fmapH unaryOf ((histR lops vs).take j)

theorem Uj_succ (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp) (j : Nat)
    (o : github_com.anishathalye.porcupine.Operation) (v : GOp) (ho : lops[j]? = some o) (hv : vs[j]? = some v) :
    Uj lops vs (j + 1) = Uj lops vs j ++
      (if v.1.Kind' = W64 5 then [] else [⟨(v.1, v.2.2.1), sint.Z o.Call', sint.Z o.Return'⟩]) := by
  unfold Uj
  rw [List.take_add_one, histR_getElem? lops vs j o v ho hv]
  unfold fmapH
  rw [List.filterMap_append]
  congr 1
  simp only [Option.toList_some, List.filterMap_cons, List.filterMap_nil, unaryOf, ropOf]
  by_cases h5 : v.1.Kind' = W64 5
  · rw [if_pos h5, if_pos h5]; rfl
  · rw [if_neg h5, if_neg h5]; rfl

theorem Uj_full (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp)
    (h : vs.length = lops.length) : Uj lops vs lops.length = fmapH unaryOf (histR lops vs) := by
  unfold Uj; rw [List.take_of_length_le (Nat.le_of_eq (histR_length lops vs h))]

/-! ## The ghost values, from `opsIoOk` -/

/-- **A ghost value's persistent facts**: a unary operation's answer is its raw response's (`rawOk`), a watch
that ran has its events (`wrawOk`). -/
def gRep (v : GOp) : IProp GF :=
  iprop((⌜v.1.Kind' = W64 5⌝ ∨ respRep (rawResp v.2.1) v.2.2.1) ∗
    (⌜v.1.Kind' ≠ W64 5 ∨ v.1.Skip' = true⌝ ∨ evsRO v.2.1.Raw'.Events' v.2.2.2))

instance gRep_persistent (v : GOp) : Iris.BI.Persistent (gRep (GF := GF) v) := by unfold gRep; infer_instance

open Iris.BI Iris.ProofMode in
include sem package_sem in
/-- **The ghost values of a history `RunLin2` answered `Ok` on, with `failureFree`'s answer.** -/
theorem gOks_collect (g0 : HSt) : ∀ (lops : List github_com.anishathalye.porcupine.Operation),
    (∀ o ∈ lops, ∀ x y, o.Input' = boxIn x → o.Output' = boxOut y → okOut x y = true) →
    github_com.anishathalye.porcupine.opsIoOk (k8setcd3S g0) lops ⊢
      ∃ vs : List GOp, ⌜GOks g0.st.rv lops vs⌝ ∗ [∗list] v ∈ vs, gRep (GF := GF) v
  | [], _ => by
    iintro -
    iexists []
    isplitr
    · ipureintro; exact ⟨rfl, fun k o v h => by simp at h⟩
    · iapply BigSepL.bigSepL_nil.2
      itrivial
  | o :: lops, hok => by
    iintro #H
    iunfold github_com.anishathalye.porcupine.opsIoOk at H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#Ho, #Hr⟩
    ihave #Hr : github_com.anishathalye.porcupine.opsIoOk (k8setcd3S g0) lops $$ [Hr]
    · iunfold github_com.anishathalye.porcupine.opsIoOk; iexact Hr
    ihave ⟨%vs, %Hvs, #Hvs⟩ := gOks_collect g0 lops (fun o' ho' => hok o' (List.mem_cons_of_mem _ ho')) $$ Hr
    unfold k8setcd3S
    icases Ho with ⟨%x, %y, ⟨%hi, %ho, %hw, %hA, %hF⟩, #Hraw, #Hwraw⟩
    have hokO := hok o List.mem_cons_self x y hi ho
    -- the unary answer
    ihave ⟨%r, #Hr1, %Hr2⟩ : ∃ r : RResp, (⌜x.Kind' = W64 5⌝ ∨ respRep (rawResp y) r) ∗
        ⌜x.Kind' ≠ W64 5 → RawRel x (plainOut y) r⌝ $$ [Hraw]
    · icases Hraw with (%h | Hraw)
      · iexists ⟨.nil, .none⟩
        isplitl
        · ileft; ipureintro
          rcases h with h | h
          · exact h
          · by_cases h5 : x.Kind' = W64 5
            · exact h5
            · exfalso
              unfold okOut at hokO; rw [if_neg h5] at hokO
              have : y.Err' = W64 4 := by
                have := congrArg Output.Err' h; simpa [otherL, errOutL] using this
              simp [this] at hokO
        · ipureintro; intro h5
          rcases h with h | h
          · exact absurd h h5
          · exfalso; unfold okOut at hokO; rw [if_neg h5] at hokO
            have : y.Err' = W64 4 := by
              have := congrArg Output.Err' h; simpa [otherL, errOutL] using this
            simp [this] at hokO
      · iunfold rawOk at Hraw
        icases Hraw with ⟨%r, #Hr1, %Hr2⟩
        iexists r
        isplitl
        · iright; iexact Hr1
        · ipureintro; exact fun _ => Hr2
    -- the watch's events
    ihave ⟨%rs, #Hrs1, %Hrs2⟩ : ∃ rs : List REv, (⌜x.Kind' ≠ W64 5 ∨ x.Skip' = true⌝ ∨ evsRO y.Raw'.Events' rs) ∗
        ⌜x.Kind' = W64 5 → x.Skip' = false →
          decWEventsL y.WEvents' = some (rs.map toWEvL) ∧ WatchFromL g0.st.rv x (rs.map toWEvL)⌝ $$ [Hwraw]
    · icases Hwraw with (%h | Hwraw)
      · iexists []
        isplitl
        · ileft; ipureintro; left; exact h
        · ipureintro; intro h5; exact absurd h5 h
      · iunfold wrawOk at Hwraw
        icases Hwraw with (%h | ⟨%rs, #He, %hd, %hf⟩)
        · iexists []
          isplitl
          · ileft; ipureintro
            by_cases h5 : x.Kind' = W64 5
            · right
              cases hs : x.Skip'
              · exfalso
                rcases h with h | h
                · rw [hs] at h; cases h
                · unfold okOut at hokO; rw [if_pos h5, h, hs] at hokO; simp at hokO
              · rfl
            · left; exact h5
          · ipureintro; intro h5 hs
            rcases h with h | h
            · rw [hs] at h; cases h
            · exfalso; unfold okOut at hokO; rw [if_pos h5, h, hs] at hokO; simp at hokO
        · iexists rs
          isplitl
          · iright; iexact He
          · ipureintro; exact fun _ _ => ⟨hd, hf⟩
    iexists (x, y, r, rs) :: vs
    isplitr
    · ipureintro
      refine ⟨by simp [Hvs.1], fun k o' v ho' hv => ?_⟩
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at ho' hv
        subst ho' hv
        exact ⟨hi, ho, hA, hF, hokO, hw, Hr2, Hrs2⟩
      | succ k =>
        simp only [List.getElem?_cons_succ] at ho' hv
        exact Hvs.2 k o' v ho' hv
    · iapply BigSepL.bigSepL_cons.2
      isplitl
      · iunfold gRep
        isplitl
        · iexact Hr1
        · iexact Hrs1
      · iexact Hvs

open Iris.BI Iris.ProofMode in
/-- **Every operation of a history `RunLin2` answered `Ok` on is boxed** (`failureFree`'s premise). -/
theorem opsIoOk_boxes (g0 : HSt) : ∀ (lops : List github_com.anishathalye.porcupine.Operation),
    github_com.anishathalye.porcupine.opsIoOk (k8setcd3S (GF := GF) g0) lops ⊢
      ⌜∀ o ∈ lops, ∃ x y, o.Input' = boxIn x ∧ o.Output' = boxOut y⌝
  | [] => by
    iintro -
    ipureintro
    intro o ho; cases ho
  | o :: lops => by
    iintro #H
    iunfold github_com.anishathalye.porcupine.opsIoOk at H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨#Ho, #Hr⟩
    ihave #Hr : github_com.anishathalye.porcupine.opsIoOk (k8setcd3S g0) lops $$ [Hr]
    · iunfold github_com.anishathalye.porcupine.opsIoOk; iexact Hr
    ihave %hr := opsIoOk_boxes g0 lops $$ Hr
    unfold k8setcd3S
    icases Ho with ⟨%x, %y, ⟨%hi, %ho, -⟩, -, -⟩
    ipureintro
    intro o' ho'
    rcases List.mem_cons.1 ho' with rfl | ho'
    · exact ⟨x, y, hi, ho⟩
    · exact hr o' ho'

/-- **The checker's model's entries** (`realMS`'s `L`): each checker operation's boxes with its unary value. -/
def Lof (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) : List (github_com.anishathalye.porcupine.OpV × (Input × RResp)) :=
  List.zipWith (fun c u => ((boxReq c.Request', boxResp c.Response'), u.val)) os U

theorem boxH_Lof_snoc (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) (c : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (u : Op (Input × RResp)) (h : os.length = U.length) :
    boxH (Lof (os ++ [c]) (U ++ [u])) (U ++ [u]) =
      boxH (Lof os U) U ++ [⟨(boxReq c.Request', boxResp c.Response'), u.call, u.ret⟩] := by
  unfold boxH Lof
  rw [List.zipWith_append h, List.zipWith_append (by rw [List.length_zipWith, h, Nat.min_self])]
  rfl

theorem Lof_length (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) (h : os.length = U.length) : (Lof os U).length = U.length := by
  unfold Lof; rw [List.length_zipWith, h, Nat.min_self]

/-- **A watch `realCheck` validates**: one that ran, its request and its (cut) events. -/
def wRep (vs : List GOp) (w : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchOperation) :
    IProp GF :=
  iprop(∃ (k : Nat) (v : GOp), ⌜vs[k]? = some v ∧ v.1.Kind' = W64 5 ∧ v.1.Skip' = false ∧
    w.Response'.Err' = GoInterface.nil⌝ ∗ wreqRep w.Request' v.1 ∗
    evsRO w.Response'.Events' (realEventsL v.1 v.2.2.2))

instance wRep_persistent (vs : List GOp) (w : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.WatchOperation) :
    Iris.BI.Persistent (wRep (GF := GF) vs w) := by unfold wRep; infer_instance

theorem Lof_getElem? (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) (k : Nat) (e : github_com.anishathalye.porcupine.OpV × (Input × RResp))
    (he : (Lof os U)[k]? = some e) :
    ∃ c u, os[k]? = some c ∧ U[k]? = some u ∧ e = ((boxReq c.Request', boxResp c.Response'), u.val) := by
  unfold Lof at he
  rw [List.getElem?_zipWith] at he
  cases h1 : os[k]? with
  | none => rw [h1] at he; cases he
  | some c =>
    cases h2 : U[k]? with
    | none => rw [h1, h2] at he; cases he
    | some u => rw [h1, h2] at he; cases he; exact ⟨c, u, rfl, rfl, rfl⟩

theorem histOf_boxH_getElem? (ps : List github_com.anishathalye.porcupine.Operation)
    (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) (hps : github_com.anishathalye.porcupine.histOf ps = boxH (Lof os U) U)
    (k : Nat) (p : github_com.anishathalye.porcupine.Operation) (hp : ps[k]? = some p) :
    ∃ c u, os[k]? = some c ∧ U[k]? = some u ∧ p.Input' = boxReq c.Request' ∧ p.Output' = boxResp c.Response' ∧
      sint.Z p.Call' = u.call ∧ sint.Z p.Return' = u.ret := by
  have h1 : (github_com.anishathalye.porcupine.histOf ps)[k]? = some (github_com.anishathalye.porcupine.opOf p) := by
    unfold github_com.anishathalye.porcupine.histOf; rw [List.getElem?_map, hp]; rfl
  rw [hps] at h1
  unfold boxH at h1
  rw [List.getElem?_zipWith] at h1
  cases hL : (Lof os U)[k]? with
  | none => rw [hL] at h1; cases h1
  | some e =>
    obtain ⟨c, u, hc, hu, rfl⟩ := Lof_getElem? os U k e hL
    rw [hL, hu] at h1
    simp only [Option.map_some, Option.bind_some, Option.some.injEq,
      github_com.anishathalye.porcupine.opOf, Op.mk.injEq, Prod.mk.injEq] at h1
    exact ⟨c, u, hc, hu, h1.1.1.symm, h1.1.2.symm, h1.2.1.symm, h1.2.2.symm⟩

theorem mem_fmapH_time {α β : Type} (f : α → Option β) (h : List (Op α)) (u : Op β)
    (hu : u ∈ github_com.anishathalye.porcupine.Theory.fmapH f h) : ∃ o ∈ h, o.call = u.call ∧ o.ret = u.ret := by
  unfold github_com.anishathalye.porcupine.Theory.fmapH at hu
  obtain ⟨o, ho, he⟩ := List.mem_filterMap.1 hu
  cases e : f o.val with
  | none => rw [e] at he; cases he
  | some b => rw [e] at he; cases he; exact ⟨o, ho, rfl, rfl⟩

theorem boxH_length (L : List (github_com.anishathalye.porcupine.OpV × (Input × RResp)))
    (U : List (Op (Input × RResp))) (h : L.length = U.length) : (boxH L U).length = U.length := by
  unfold boxH; rw [List.length_zipWith, h, Nat.min_self]

/-- **The unary checker operations satisfy `CheckOperationsVerbose`'s premise** (`HistOk`). -/
theorem histOk_ps (lops : List github_com.anishathalye.porcupine.Operation) (vs : List GOp)
    (hvs : vs.length = lops.length) (hh : github_com.anishathalye.porcupine.HistOk lops)
    (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (ps : List github_com.anishathalye.porcupine.Operation) (hos : os.length = (fmapH unaryOf (histR lops vs)).length)
    (hps : github_com.anishathalye.porcupine.histOf ps =
      boxH (Lof os (fmapH unaryOf (histR lops vs))) (fmapH unaryOf (histR lops vs))) :
    github_com.anishathalye.porcupine.HistOk ps ∧ ps.length = (fmapH unaryOf (histR lops vs)).length := by
  have hlen : ps.length = (fmapH unaryOf (histR lops vs)).length := by
    have := congrArg List.length hps
    unfold github_com.anishathalye.porcupine.histOf at this
    rw [List.length_map, boxH_length _ _ (Lof_length os _ hos)] at this
    exact this
  have hle : (fmapH unaryOf (histR lops vs)).length ≤ lops.length := by
    unfold fmapH; rw [← histR_length lops vs hvs]; exact List.length_filterMap_le _ _
  refine ⟨⟨by have := hh.1; omega, fun p hp => ?_⟩, hlen⟩
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 hp
  obtain ⟨c, u, -, hu, -, -, hc, hr⟩ := histOf_boxH_getElem? ps os _ hps k p hk
  obtain ⟨o, ho, hoc, hor⟩ := mem_fmapH_time unaryOf _ u (List.mem_of_getElem? hu)
  obtain ⟨k', op, v, hl, -, rfl⟩ := mem_histR lops vs hvs o ho
  rw [hc, hr, ← hoc, ← hor]
  exact hh.2 op (List.mem_of_getElem? hl)

/-! ## The checker's requests and responses are determined by their values -/

include sem package_sem in
theorem getOptions_intoVal_inj : Function.Injective (intoVal (V := k8s_io.apiserver.pkg.storage.GetOptions)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.GetOptions.TypeAssumptions.get'IgnoreNotFound x) (k8s_io.apiserver.pkg.storage.GetOptions.TypeAssumptions.get'IgnoreNotFound y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.GetOptions.TypeAssumptions.get'ResourceVersion x) (k8s_io.apiserver.pkg.storage.GetOptions.TypeAssumptions.get'ResourceVersion y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem selPred_intoVal_inj : Function.Injective (intoVal (V := k8s_io.apiserver.pkg.storage.SelectionPredicate)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Label x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Label y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Field x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Field y) h))
  have := intoVal_inj_func (hG := hG) (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'GetAttrs x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'GetAttrs y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'IndexLabels x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'IndexLabels y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'IndexFields x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'IndexFields y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Limit x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Limit y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Continue x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'Continue y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'AllowWatchBookmarks x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'AllowWatchBookmarks y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'ShardSelector x) (k8s_io.apiserver.pkg.storage.SelectionPredicate.TypeAssumptions.get'ShardSelector y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem listOptions_intoVal_inj : Function.Injective (intoVal (V := k8s_io.apiserver.pkg.storage.ListOptions)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'ResourceVersion x) (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'ResourceVersion y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'ResourceVersionMatch x) (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'ResourceVersionMatch y) h))
  have := selPred_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'Predicate x) (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'Predicate y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'Recursive x) (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'Recursive y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'ProgressNotify x) (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'ProgressNotify y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'SendInitialEvents x) (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'SendInitialEvents y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'RecordTimestamps x) (k8s_io.apiserver.pkg.storage.ListOptions.TypeAssumptions.get'RecordTimestamps y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem createReq_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.CreateRequest)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.CreateRequest.TypeAssumptions.get'Object x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.CreateRequest.TypeAssumptions.get'Object y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem getReq_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.GetRequest)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := getOptions_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.GetRequest.TypeAssumptions.get'Options x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.GetRequest.TypeAssumptions.get'Options y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem listReq_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListRequest)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := listOptions_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListRequest.TypeAssumptions.get'Options x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ListRequest.TypeAssumptions.get'Options y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem deleteReq_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.DeleteRequest)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.DeleteRequest.TypeAssumptions.get'Preconditions x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.DeleteRequest.TypeAssumptions.get'Preconditions y) h))
  have := intoVal_inj_func (hG := hG) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.DeleteRequest.TypeAssumptions.get'ValidateDeletion x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.DeleteRequest.TypeAssumptions.get'ValidateDeletion y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.DeleteRequest.TypeAssumptions.get'CachedExistingObject x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.DeleteRequest.TypeAssumptions.get'CachedExistingObject y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem updateReq_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := intoVal_inj_func (hG := hG) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'UpdateFunc x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'UpdateFunc y) h))
  have := GoGlobalContext.intoVal_inj_bool (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'IgnoreNotFound x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'IgnoreNotFound y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'Preconditions x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'Preconditions y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'CachedExistingObject x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.UpdateRequest.TypeAssumptions.get'CachedExistingObject y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem compactReq_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.CompactRequest)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.CompactRequest.TypeAssumptions.get'ResourceVersion x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.CompactRequest.TypeAssumptions.get'ResourceVersion y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem request_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Op x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Op y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Key x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Key y) h))
  have := createReq_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Create x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Create y) h))
  have := getReq_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Get x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Get y) h))
  have := listReq_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'List x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'List y) h))
  have := deleteReq_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Delete x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Delete y) h))
  have := updateReq_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Update x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Update y) h))
  have := compactReq_intoVal_inj (sem := sem) (package_sem := package_sem) (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Compact x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.TypeAssumptions.get'Compact y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem response_intoVal_inj : Function.Injective (intoVal (V := github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.TypeAssumptions.get'Object x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.TypeAssumptions.get'Object y) h))
  have := go.intoVal_inj (Expr.Val.inj (proj_eq
    (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.TypeAssumptions.get'Err x) (github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.TypeAssumptions.get'Err y) h))
  cases x; cases y; simp_all

include sem package_sem in
theorem boxReq_inj {a b : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request}
    (h : boxReq a = boxReq b) : a = b :=
  request_intoVal_inj (sem := sem) (package_sem := package_sem) (GoInterfaceOk.mk.inj (GoInterface.ok.inj h)).2

include sem package_sem in
theorem boxResp_inj {a b : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response}
    (h : boxResp a = boxResp b) : a = b :=
  response_intoVal_inj (sem := sem) (package_sem := package_sem) (GoInterfaceOk.mk.inj (GoInterface.ok.inj h)).2

open Iris.BI Iris.ProofMode in
/-- **`CheckOperationsVerbose`'s `opsIoOk` of the unary checker operations**, from their reps. -/
theorem realMS_opsIoOk (init : RM)
    (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) (ps : List github_com.anishathalye.porcupine.Operation)
    (hps : github_com.anishathalye.porcupine.histOf ps = boxH (Lof os U) U)
    (hst : ∀ op ∈ U.map Op.val, stepIn op.1 op.2) :
    (□ [∗list] c;u ∈ os;U, opRep (GF := GF) c u.val ∗ reqPin c.Request' u.val.1) ⊢
      github_com.anishathalye.porcupine.opsIoOk (realMS (Lof os U) init) ps := by
  unfold github_com.anishathalye.porcupine.opsIoOk
  refine BigSepL.bigSepL_intro fun k p hp => ?_
  obtain ⟨c, u, hc, hu, hi, ho, -, -⟩ := histOf_boxH_getElem? ps os U hps k p hp
  iintro #H
  ihave %hlen := BigSepL2.bigSepL2_length $$ H
  have he : (((boxReq c.Request', boxResp c.Response'), u.val) : github_com.anishathalye.porcupine.OpV ×
      (Input × RResp)) ∈ Lof os U := by
    have : (Lof os U)[k]? = some ((boxReq c.Request', boxResp c.Response'), u.val) := by
      unfold Lof; rw [List.getElem?_zipWith, hc, hu]
    exact List.mem_of_getElem? this
  obtain ⟨e', he', he1, hdec⟩ := decR_mem _ _ he
  obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 he'
  obtain ⟨c', u', hc', hu', rfl⟩ := Lof_getElem? os U k' e' hk'
  ihave #H' := BigSepL2.bigSepL2_lookup (Φ := fun _ c u => iprop(opRep (GF := GF) c u.val ∗
    reqPin c.Request' u.val.1)) hc' hu' $$ H
  icases H' with ⟨Hop, -⟩
  iunfold opRep at Hop
  icases Hop with ⟨#Hrq, #Hrs⟩
  simp only [realMS]
  iexists c'.Request', c'.Response', u'.val.1, u'.val.2
  isplitr
  · ipureintro
    simp only [Prod.mk.injEq] at he1
    refine ⟨hi.trans he1.1.symm, ho.trans he1.2.symm, ?_, hst _ (List.mem_map_of_mem (List.mem_of_getElem? hu'))⟩
    rw [hi, ho]; exact hdec
  isplitl
  · iexact Hrq
  · iexact Hrs

open Iris.BI Iris.ProofMode in
/-- **The checker's model's entries step alike** (`StepAgree`), from their reps. -/
theorem stepAgree_of (os : List github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
    (U : List (Op (Input × RResp))) (hst : ∀ op ∈ U.map Op.val, stepIn op.1 op.2) :
    (□ [∗list] c;u ∈ os;U, opRep (GF := GF) c u.val ∗ reqPin c.Request' u.val.1) ⊢ ⌜StepAgree (Lof os U)⌝ := by
  iintro #H
  ihave %hall : ⌜∀ (k k' : Nat) (c c' : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Operation)
      (u u' : Op (Input × RResp)), os[k]? = some c → U[k]? = some u → os[k']? = some c' → U[k']? = some u' →
      boxReq c.Request' = boxReq c'.Request' → boxResp c.Response' = boxResp c'.Response' →
      ∀ (init m : RM), (realS init).step m u.val = (realS init).step m u'.val⌝ $$ [H]
  · iintro %k %k' %c %c' %u %u' %hc %hu %hc' %hu' %hq %hr
    have eq := boxReq_inj (sem := sem) (package_sem := package_sem) hq
    have er := boxResp_inj (sem := sem) (package_sem := package_sem) hr
    have hs1 := hst _ (List.mem_map_of_mem (List.mem_of_getElem? hu))
    have hs2 := hst _ (List.mem_map_of_mem (List.mem_of_getElem? hu'))
    have hne : ∀ r : RResp, flatE r.err → r.err ≠ .other := fun r hf h => by rw [h] at hf; exact hf
    ihave #H1 := BigSepL2.bigSepL2_lookup (Φ := fun _ c u => iprop(opRep (GF := GF) c u.val ∗
      reqPin c.Request' u.val.1)) hc hu $$ H
    ihave #H2 := BigSepL2.bigSepL2_lookup (Φ := fun _ c u => iprop(opRep (GF := GF) c u.val ∗
      reqPin c.Request' u.val.1)) hc' hu' $$ H
    icases H1 with ⟨Hop1, #Hp1⟩
    icases H2 with ⟨Hop2, #Hp2⟩
    iunfold opRep at Hop1 Hop2
    icases Hop1 with ⟨#Hq1, #Hr1⟩
    icases Hop2 with ⟨#Hq2, #Hr2⟩
    rw [← eq, ← er]
    ihave %hx := reqRep_agree c.Request' u.val.1 u'.val.1 $$ [$Hq1 $Hp1 $Hq2 $Hp2]
    ihave %hr' := respRep_agree c.Response' u.val.2 u'.val.2 (hne _ hs1.1.2.2.2.1) (hne _ hs2.1.2.2.2.1)
      $$ [$Hr1 $Hr2]
    ipureintro
    intro init m
    simp only [realS, hx, hr']
  ipureintro
  intro e he e' he' heq init m
  obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 he
  obtain ⟨k', hk'⟩ := List.mem_iff_getElem?.1 he'
  obtain ⟨c, u, hc, hu, rfl⟩ := Lof_getElem? os U k e hk
  obtain ⟨c', u', hc', hu', rfl⟩ := Lof_getElem? os U k' e' hk'
  simp only [Prod.mk.injEq] at heq
  exact hall k k' c c' u u' hc hu hc' hu' heq.1 heq.2 init m

open Iris.BI Iris.ProofMode in
/-- **Picking entries of two related lists by the same indices** keeps them related (persistent relation). -/
theorem bigSepL2_pick {A B C : Type} (Φ : A → B → IProp GF) [∀ a b, Persistent (Φ a b)]
    (l1 : List A) (l2 : List B) (idx : C → Nat) : ∀ π : List C,
    ([∗list] a;b ∈ l1;l2, Φ a b) ⊢
      [∗list] a;b ∈ π.filterMap (fun c => l1[idx c]?);π.filterMap (fun c => l2[idx c]?), Φ a b
  | [] => by
    iintro -
    simp only [List.filterMap_nil]
    iapply BigSepL2.bigSepL2_nil.2
    itrivial
  | c :: π => by
    iintro #H
    ihave %hlen := BigSepL2.bigSepL2_length $$ H
    ihave #Hr := bigSepL2_pick Φ l1 l2 idx π $$ H
    simp only [List.filterMap_cons]
    cases h1 : l1[idx c]? with
    | none =>
      have h2 : l2[idx c]? = none := by
        rw [List.getElem?_eq_none_iff] at h1 ⊢; omega
      simp only [h2]
      iexact Hr
    | some a =>
      obtain ⟨b, h2⟩ : ∃ b, l2[idx c]? = some b := by
        have : idx c < l2.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 h1).1
        exact ⟨_, List.getElem?_eq_getElem this⟩
      simp only [h2]
      ihave #Hab := BigSepL2.bigSepL2_lookup (Φ := fun _ a b => Φ a b) h1 h2 $$ H
      iapply BigSepL2.bigSepL2_cons.2
      isplitl
      · iexact Hab
      · iexact Hr

end go

end k8s_correctness
end EtcdGrove
end Perennial
