/-
Lean-first (no Rocq counterpart).

# `toPorcupineModel`'s model spec (k8s 7g step 5, decision 1)

The `ModelSpec` the spec of `toPorcupineModel` claims: `realM L init` (`RealModel`), a state value a frozen
`*correctness.Model` (`modelAt`) of a state whose items fit, at most `2^61 + k` of them at index `k` (porcupine
steps below index `2^60`, so `Step`'s model has fewer than `2^62`, `slices.Sorted`'s bound), and an operation's values boxed `Request`/`Response`
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

theorem stepIn_stepPre (x : Input) (r : RResp) (m : RM) (h : stepIn x r) (hm : itemsFitL m)
    (hs : GMap.size m.items < 2 ^ 62) : stepPre x m r :=
  ⟨hs, hm, rexecL_notOther x m h.1.2.1 h.2.2.1 h.2.2.2, h.1⟩

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

/-- **A step adds at most one item.** -/
theorem rexecL_size (x : Input) (m : RM) :
    GMap.size (rexecL x m).2.1.items ≤ GMap.size m.items + 1 := by
  have hi : ∀ k (o : Obj), GMap.size (<[k := o]> m.items) ≤ GMap.size m.items + 1 := by
    intro k o; have := GMap.map_size_insert m.items k o; split at this <;> omega
  have hd : ∀ k, GMap.size (GMap.delete k m.items) ≤ GMap.size m.items + 1 := by
    intro k; have := GMap.map_size_delete m.items k; split at this <;> omega
  have h0 : GMap.size m.items ≤ GMap.size m.items + 1 := Nat.le_succ _
  have hw : ∀ key st u, GMap.size (updWriteL m key st u).2.1.items ≤ GMap.size m.items + 1 := by
    intro key st u; unfold updWriteL; exact hi _ _
  unfold rexecL
  split
  · exact h0
  split
  · unfold rcreateL failR
    dsimp only
    split
    · exact h0
    split
    · exact h0
    · exact hi _ _
  split
  · unfold rdeleteL failR
    dsimp only
    split
    · exact h0
    split
    · exact h0
    split
    · exact h0
    split
    · exact h0
    · exact hd _
  split
  · unfold rupdateL failR
    dsimp only
    split
    · exact h0
    split
    · exact h0
    split
    · exact h0
    split
    · exact h0
    split
    · split
      · exact h0
      · exact hw _ _ _
    · exact hw _ _ _
  · exact h0

/-- **A model step adds at most one item.** -/
theorem rstepL_size (x : Input) (m : RM) (out : RResp) :
    GMap.size (rstepL x m out).2.1.items ≤ GMap.size m.items + 1 := by
  unfold rstepL
  split
  · exact Nat.le_succ _
  split
  · split
    · exact rexecL_size x m
    · exact Nat.le_succ _
  · exact Nat.le_succ _

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

/-- **The replay adds at most one item per operation.** -/
theorem replayFold_size (l : List (Input × RResp)) :
    ∀ (a acc : RM × GMap w64 RM × List RChange),
      l.foldl replayStepL (some a) = some acc → GMap.size acc.1.items ≤ GMap.size a.1.items + l.length := by
  induction l with
  | nil => intro a acc h; cases h; simp
  | cons op l ih =>
    intro a acc h
    rw [List.foldl_cons] at h
    obtain ⟨st, ss, cs⟩ := a
    by_cases hs : (rstepL op.1 st op.2).1 = true
    · have e : replayStepL (some (st, ss, cs)) op = some ((rstepL op.1 st op.2).2.1,
          <[(rstepL op.1 st op.2).2.1.rv := (rstepL op.1 st op.2).2.1]> ss,
          cs ++ (rstepL op.1 st op.2).2.2.toList) := by
        show (if _ then _ else _) = _; rw [if_pos hs]
      rw [e] at h
      have h1 := ih _ acc h
      have h2 := rstepL_size op.1 st op.2
      simp only [List.length_cons] at h1 ⊢
      omega
    · have e : replayStepL (some (st, ss, cs)) op = none := by
        show (if _ then _ else _) = _; rw [if_neg hs]
      rw [e, replayStepL_foldl_none] at h; cases h

/-- **`NewReplay`'s premises** (`ReplayPre`, gap 3) on operations each with `Model.Step`'s pure premises
(`stepIn`), from a state whose items fit, with room for one item per operation under `2^62`. -/
theorem replayPre_of (init : RM) (ops : List (Input × RResp)) (hinit : itemsFitL init)
    (hsz : GMap.size init.items + ops.length < 2 ^ 62)
    (hops : ∀ op ∈ ops, stepIn op.1 op.2) : ReplayPre init ops := by
  intro i acc op hacc hop
  have hfit := replayFold_fit (ops.take i) (fun o ho => (hops o (List.mem_of_mem_take ho)).2.1) _ acc
    hinit hacc
  have hs := replayFold_size (ops.take i) _ acc hacc
  have hi : i < ops.length := (List.getElem?_eq_some_iff.1 hop).1
  have ht : (ops.take i).length = i := by simp; omega
  exact stepIn_stepPre op.1 op.2 acc.1 (hops op (List.mem_of_getElem? hop)) hfit (by
    simp only at hs; omega)

/-- **`failureFree`'s test of one operation**: a watch that ran did not fail its `Watch` call, a unary output is
not `EOther`. -/
def okOut (x : Input) (y : Output) : Bool :=
  if x.Kind' = W64 5 then x.Skip' || !y.WFailed' else decide (y.Err' ≠ W64 4)

/-- A consistent list asks for revision `0`. -/
theorem listConsL_consistent (x : Input) (rq : w64) (h : listConsL x = some (.consistent, rq)) : rq = 0 := by
  unfold listConsL at h
  by_cases h0 : x.MinRV' = []
  · rw [if_pos h0] at h
    by_cases hm : x.Match' = W64 1 ∨ x.Match' = W64 2
    · rw [if_pos hm] at h; cases h
    · rw [if_neg hm] at h; simp only [Option.some.injEq, Prod.mk.injEq] at h; exact h.2.symm
  · rw [if_neg h0] at h
    cases hp : parseRVD x.MinRV' with
    | none => rw [hp] at h; cases h
    | some v =>
      rw [hp] at h
      simp only at h
      by_cases h1 : x.Match' = W64 1
      · rw [if_pos h1] at h; simp at h
      rw [if_neg h1] at h
      by_cases h2 : x.Match' = W64 2
      · rw [if_pos h2] at h
        by_cases hv : v = 0
        · rw [if_pos hv] at h; cases h
        · rw [if_neg hv] at h; simp at h
      rw [if_neg h2] at h
      split at h <;> simp at h

/-- A list answer of a unary operation carries no error (`RawRel`). -/
theorem rawRel_list_noerr (x : Input) (y : Output) (out : RResp) (hraw : RawRel x y out)
    (items : Option (List Obj)) (rv : w64) (c : GoString) (rr : Option w64)
    (hobj : out.obj = .list items rv c rr) : out.err = RErr.none := by
  unfold RawRel at hraw
  by_cases e0 : y.Err' = W64 0
  · rw [if_pos e0] at hraw
    by_cases e4 : x.Kind' = W64 4
    · rw [if_pos e4] at hraw; obtain ⟨_, _, _, rfl⟩ := hraw; rfl
    · rw [if_neg e4] at hraw; subst hraw; cases hobj
  rw [if_neg e0] at hraw
  by_cases e1 : y.Err' = W64 1
  · rw [if_pos e1] at hraw; subst hraw; cases hobj
  rw [if_neg e1] at hraw
  by_cases e2 : y.Err' = W64 2
  · rw [if_pos e2] at hraw; subst hraw; cases hobj
  rw [if_neg e2] at hraw
  by_cases e3 : y.Err' = W64 3
  · rw [if_pos e3] at hraw; subst hraw; cases hobj
  rw [if_neg e3] at hraw
  by_cases e5 : y.Err' = W64 5
  · rw [if_pos e5] at hraw; subst hraw; cases hobj
  rw [if_neg e5] at hraw
  by_cases e6 : y.Err' = W64 6
  · rw [if_pos e6] at hraw; subst hraw; cases hobj
  rw [if_neg e6] at hraw
  exact hraw.elim

/-- **`Replay.Validate`'s list premise** (`listExpOk`) for a unary list the replay validates. -/
theorem listExpOk_of (R : RReplay) (x : Input) (y : Output) (out : RResp) (hraw : RawRel x y out)
    (hst : stepIn x out) (h4 : x.Kind' = W64 4) (hv : rvalidateL R x out = true) : listExpOk R x out := by
  intro items rv c rr st hobj hst'
  have hne := rawRel_list_noerr x y out hraw items rv c rr hobj
  obtain ⟨hlc, hpk⟩ := hst.2.2.2 h4
  obtain ⟨⟨c0, rq⟩, hlc⟩ := Option.isSome_iff_exists.1 hlc
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.1 hpk
  unfold rvalidateL at hv
  rw [if_pos h4] at hv
  unfold rreplayListL at hv
  rw [hne, hlc] at hv
  simp only [errNonNil, Bool.false_eq_true, ↓reduceIte] at hv
  cases c0 with
  | consistent =>
    have hrq := listConsL_consistent x rq hlc
    subst hrq
    have hno := rexecL_notOther x st hst.1.2.1 (fun h => absurd h4 h)
      (fun _ => ⟨by rw [hlc]; rfl, by rw [hp]; rfl⟩)
    unfold rexecL at hno
    rw [if_pos h4] at hno
    unfold rlistL at hno ⊢
    rw [hp, hlc] at hno ⊢
    simp only at hno ⊢
    rw [if_neg (by simp)] at hno ⊢
    split <;> (try split) <;> simp_all [deepErrE]
  | exact =>
    simp only [hobj, hst'] at hv
    cases e : (rlistL x st).err <;> simp_all [equalListRespL, respEqL, errNonNil, deepErrE]
  | notOlderThan =>
    simp only [hobj, hst'] at hv
    cases e : (rlistL x st).err <;> simp_all [equalListRespL, respEqL, errNonNil, deepErrE]

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
  rep k v m := iprop(∃ mp, ⌜v = boxM mp ∧ itemsFitL m ∧ GMap.size m.items ≤ 2 ^ 61 + k⌝ ∗ modelAt mp m)
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
