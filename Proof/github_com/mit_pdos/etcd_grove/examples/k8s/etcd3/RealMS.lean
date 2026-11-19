/-
Lean-first (no Rocq counterpart).

# `toPorcupineModel`'s model spec (k8s 7g step 5, decision 1)

The `ModelSpec` the spec of `toPorcupineModel` claims: `realM L init` (`RealModel`), a state value a frozen
`*correctness.Model` (`modelAt`) of a state whose items fit, and an operation's values boxed `Request`/`Response`
whose decoded view (`decR L`) has its own `reqRep`/`respRep` and `Model.Step`'s pure premises at every state
(`stepIn`).

- `rexecL_notOther`: the model's own answer is never `RErr.other` on an input with a key `PrepareKey` accepts
  (a list's: its key and consistency accepted, its continue token defined by scope);
- `itemsFitL_step`: `Step` keeps the items fitting; `replayPre_of`: `NewReplay`'s premises from `stepIn`;
- `genIn_stepIn`: `stepIn` of an input `Gen` may return (its list options: `genIn_listConsL`);
- `okOut x y`: `failureFree`'s test of an operation;
- `stepIn x r`, `realMS L init`.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealModel
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.RealAgreeReq
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.ReplayRep
public import Proof.github_com.anishathalye.porcupine.Defs

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_correctness

open Iris Iris.BI Iris.ProofMode k8s_etcd3 k8sDeep github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Obj Input Output item)

section pure
variable [GooseExts]

/-- A list's continue token is defined when it has more (`encOkL`), for a key `PrepareKey` accepts. -/
theorem encOkL_scopeR (x : Input) (m : RM) (p : GoString)
    (hp : k8s.prepareKeyM [] x.ListKey' x.Recursive' = some p)
    (hm : (ListModel.loop (selOkL x) (limitN x) (scopeR x.ListKey' x.Recursive' m)).more = true) :
    encOkL ((ListModel.loop (selOkL x) (limitN x) (scopeR x.ListKey' x.Recursive' m)).last.getD [] ++
      [W8 0]) p = true := by
  have hinv : LastInv (fun k => p <+: k) (fun _ : Obj => True)
      (ListModel.loop (selOkL x) (limitN x) (scopeR x.ListKey' x.Recursive' m)) := by
    apply lastInv_loop
    intro ko hko
    unfold scopeR at hko
    rw [List.mem_filter] at hko
    exact ⟨prepared_scope hp hko.2, trivial⟩
  obtain ⟨h1, h2, h3, -⟩ := hinv
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 (h2 (h1 hm))
  rw [hk]
  unfold encOkL
  simp only [Option.getD_some, decide_eq_true_eq]
  exact ⟨prepared_ne hp, (h3 k hk).trans (List.prefix_append _ _)⟩

/-- **The model's own answer is never `RErr.other`** on an input whose key `PrepareKey` accepts (a list's
key and consistency accepted) and whose resource version parses. -/
theorem rexecL_notOther (x : Input) (m : RM) (hrv : (parseRVD x.MinRV').isSome)
    (hk : x.Kind' ≠ W64 4 → keyOkL (storeKeyL x.Key') = true)
    (hl : x.Kind' = W64 4 → (listConsL x).isSome ∧ (k8s.prepareKeyM [] x.ListKey' x.Recursive').isSome) :
    (rexecL x m).1.err ≠ .other := by
  unfold rexecL
  by_cases h4 : x.Kind' = W64 4
  · rw [if_pos h4]
    obtain ⟨hc, hp⟩ := hl h4
    obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hp
    obtain ⟨⟨c, rq⟩, hc⟩ := Option.isSome_iff_exists.1 hc
    show (rlistL x m).err ≠ .other
    unfold rlistL
    simp only [hp, hc]
    split
    · simp [tooLargeE]
    · split
      · rename_i hm
        simp only [encOkL_scopeR x m p hp hm, ↓reduceIte]
        simp
      · simp
  · rw [if_neg h4]
    have hk := hk h4
    have hk' : (!keyOkL (storeKeyL x.Key')) = false := by simp [hk]
    split
    · show (rcreateL x m).1.err ≠ .other
      unfold rcreateL
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      split
      · simp [failR, existsE]
      · simp
    split
    · show (rdeleteL x m).1.err ≠ .other
      unfold rdeleteL
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      split
      · simp [failR, notFoundE]
      · split
        · simp [failR, invalidE]
        · split
          · simp [failR, delRejE]
          · simp
    split
    · show (rupdateL x m).1.err ≠ .other
      unfold rupdateL
      simp only [hk', Bool.false_eq_true, ↓reduceIte]
      split
      · simp [failR, notFoundE]
      · split
        · simp [failR, invalidE]
        · split
          · simp [failR, updRejE]
          · unfold updWriteL
            split
            · split <;> simp
            · simp
    · show (rgetL x m).err ≠ .other
      obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.1 hrv
      unfold rgetL
      simp only [hk', Bool.false_eq_true, ↓reduceIte, hrv]
      split
      · simp [tooLargeE]
      · split
        · split <;> simp [notFoundE]
        · simp

/-- **`Model.Step`'s pure premises on an operation, at every state**: the operation's own (`opPre`), its
fields fit an object (`crFits`), and the facts that keep the model's own answer off `RErr.other`. -/
def stepIn (x : Input) (r : RResp) : Prop :=
  opPre x r ∧ crFits x ∧ (x.Kind' ≠ W64 4 → keyOkL (storeKeyL x.Key') = true) ∧
    (x.Kind' = W64 4 → (listConsL x).isSome ∧ (k8s.prepareKeyM [] x.ListKey' x.Recursive').isSome)

theorem stepIn_stepPre (x : Input) (r : RResp) (m : RM) (h : stepIn x r) (hm : itemsFitL m) :
    stepPre x m r :=
  ⟨hm, rexecL_notOther x m h.1.2.1 h.2.2.1 h.2.2.2, h.1⟩

/-- **A list `Gen` may return has options `listOptions` takes** (gap 2: `ListOptOk`). -/
theorem genIn_listConsL (x : Input) (hx : GenIn x) (h4 : x.Kind' = W64 4) : (listConsL x).isSome := by
  obtain ⟨hm0, hm2⟩ := hx.2.2.2.2 h4
  obtain ⟨n, hn, -⟩ := hx.1.2.2.2.2.1
  unfold listConsL
  by_cases he : x.MinRV' = []
  · rw [if_pos he, if_neg (by rw [hm0 he]; decide)]; rfl
  rw [if_neg he, hn]
  dsimp only
  by_cases h1 : x.Match' = W64 1
  · rw [if_pos h1]; rfl
  rw [if_neg h1]
  by_cases h2 : x.Match' = W64 2
  · have hn0 : n ≠ 0 := fun h => hm2 h2 (by rw [hn, h])
    rw [if_pos h2, if_neg hn0]; rfl
  rw [if_neg h2]
  split <;> rfl

/-- **`Model.Step`'s pure premises of an input `Gen` may return** (`stepIn`), given its response's own
facts (from `rawOk`). A list's minimum resource version is never the string `"0"` (which `parseRVD` refuses). -/
theorem genIn_stepIn (x : Input) (r : RResp) (hx : GenIn x) (hflat : flatE r.err)
    (hlist : x.Kind' = W64 4 → listOrNilD r.obj)
    (hobj : isWriteL x = false → x.Kind' ≠ W64 4 → objOrNilD r.obj) : stepIn x r := by
  obtain ⟨hk, hu, hn, ha, ⟨v, hv, -⟩, hl⟩ := hx.1
  have hkl : x.Key'.length ≤ 11 := by
    simp only [wkKeysL, List.mem_cons, List.not_mem_nil, _root_.or_false] at hk
    rcases hk with h | h | h | h <;> rw [h] <;> decide
  have hz : parseRVD go!"0" = none := by decide
  have h0 : x.MinRV' ≠ go!"0" := fun h => by rw [h, hz] at hv; cases hv
  refine ⟨⟨⟨by omega, hn, ha⟩, by rw [hv]; rfl, fun h4 => ⟨(hl h4).2.2.1, fun _ => h0⟩, hflat, hlist, hobj⟩,
    ⟨by omega, hu, hn, ha⟩, fun _ => ?_, fun h4 => ⟨genIn_listConsL x hx h4, by
      obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 (hl h4).2.2.2.1
      rw [prepareKeyM_nil hp]; rfl⟩⟩
  simp only [wkKeysL, List.mem_cons, List.not_mem_nil, _root_.or_false] at hk
  rcases hk with h | h | h | h <;> rw [h] <;> decide

/-- **`Step` keeps the items fitting.** -/
theorem itemsFitL_step (x : Input) (m : RM) (out : RResp) (hm : itemsFitL m) (hx : crFits x) :
    itemsFitL (rstepL x m out).2.1 := by
  unfold rstepL
  split
  · exact hm
  split
  · split
    · exact itemsFitL_exec x m hm hx
    · exact hm
  · exact hm

theorem replayStepL_foldl_none (l : List (Input × RResp)) : l.foldl replayStepL none = none := by
  induction l with
  | nil => rfl
  | cons op l ih => exact ih

/-- **The replay keeps the items fitting**, from a state whose items fit, on operations whose fields fit. -/
theorem replayFold_fit (l : List (Input × RResp)) (hl : ∀ op ∈ l, crFits op.1) :
    ∀ (a acc : RM × GMap w64 RM × List RChange), itemsFitL a.1 →
      l.foldl replayStepL (some a) = some acc → itemsFitL acc.1 := by
  induction l with
  | nil => intro a acc ha h; cases h; exact ha
  | cons op l ih =>
    intro a acc ha h
    rw [List.foldl_cons] at h
    obtain ⟨st, ss, cs⟩ := a
    by_cases hs : (rstepL op.1 st op.2).1 = true
    · have e : replayStepL (some (st, ss, cs)) op = some ((rstepL op.1 st op.2).2.1,
          <[(rstepL op.1 st op.2).2.1.rv := (rstepL op.1 st op.2).2.1]> ss,
          cs ++ (rstepL op.1 st op.2).2.2.toList) := by
        show (if _ then _ else _) = _; rw [if_pos hs]
      rw [e] at h
      exact ih (fun o ho => hl o (List.mem_cons_of_mem _ ho)) _ acc
        (itemsFitL_step op.1 st op.2 ha (hl op List.mem_cons_self)) h
    · have e : replayStepL (some (st, ss, cs)) op = none := by
        show (if _ then _ else _) = _; rw [if_neg hs]
      rw [e, replayStepL_foldl_none] at h; cases h

/-- **`NewReplay`'s premises** (`ReplayPre`, gap 3) on operations each with `Model.Step`'s pure premises
(`stepIn`), from a state whose items fit. -/
theorem replayPre_of (init : RM) (ops : List (Input × RResp)) (hinit : itemsFitL init)
    (hops : ∀ op ∈ ops, stepIn op.1 op.2) : ReplayPre init ops := by
  intro i acc op hacc hop
  have hfit := replayFold_fit (ops.take i) (fun o ho => (hops o (List.mem_of_mem_take ho)).2.1) _ acc
    hinit hacc
  exact stepIn_stepPre op.1 op.2 acc.1 (hops op (List.mem_of_getElem? hop)) hfit

/-- **`failureFree`'s test of one operation**: a watch that ran did not fail its `Watch` call, a unary output is
not `EOther`. -/
def okOut (x : Input) (y : Output) : Bool :=
  if x.Kind' = W64 5 then x.Skip' || !y.WFailed' else decide (y.Err' ≠ W64 4)

end pure

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [reg : EtcdGrove.k8s.CompactorRegistry]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A `Request`, boxed (`any(r)`). -/
abbrev boxReq (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request) : GoInterface :=
  interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Request.ty #r

/-- A `Response`, boxed (`any(r)`). -/
abbrev boxResp (r : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response) : GoInterface :=
  interface.mkOk github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.ty #r

/-- A `*Model`, boxed (`any(mp)`). -/
abbrev boxM (mp : Loc) : GoInterface :=
  interface.mkOk (go.GoType.PointerType github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Model.ty) #mp

/-- **`toPorcupineModel`'s model spec** (see the file header). -/
def realMS (L : List (github_com.anishathalye.porcupine.OpV × (Input × RResp))) (init : RM) :
    github_com.anishathalye.porcupine.ModelSpec GF RM where
  M := realM L init
  rep _ v m := iprop(∃ mp, ⌜v = boxM mp ∧ itemsFitL m⌝ ∗ modelAt mp m)
  ioOk i o := iprop(∃ rq ro x r, ⌜i = boxReq rq ∧ o = boxResp ro ∧ decR L (i, o) = some (x, r) ∧
    stepIn x r⌝ ∗ reqRep rq x ∗ respRep ro r)
  ioOk_pers _ _ := by infer_instance

instance realMS_rep_persistent (L : List (github_com.anishathalye.porcupine.OpV × (Input × RResp)))
    (init : RM) (k : Nat) (v : GoInterface) (m : RM) : Persistent ((realMS (GF := GF) L init).rep k v m) := by
  unfold realMS; infer_instance

end defs

end k8s_correctness
end EtcdGrove
end Perennial
