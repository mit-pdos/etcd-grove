/-
Proof of `v3rpc.checkIntervals` (`key.go`) over the interval tree's contract (`NewIntervalTree`,
`Insert` of any interval, `Intersects`, `Union`, pending in the adt Link). Lean-first (no Rocq
counterpart).

The three loops of the code against `ivCheck = (ivNest ops).bind (ivFinish ops)`: the level's
deletes inserted into the tree (`levelDels`, up to order); the nested transactions, each checked
recursively (Löb induction on the spec) and its puts and deletes merged (`nestStep`, the two map
loops in any key order: their checks are membership tests); the level's puts (`putStep`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.checkIntervals
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewIntervalTree
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewStringAffineInterval
public import Spec.go_etcd_io.etcd.pkg.v3.adt.NewStringAffinePoint
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__InsertAny
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Intersects
public import Spec.go_etcd_io.etcd.pkg.v3.adt.intervalTree__Union

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove

namespace v3rpc

/-! ## The model, step by step -/

theorem ci_levelDels_append (a b : List ReqOp) :
    levelDels (a ++ b) = levelDels a ++ levelDels b := by
  induction a with
  | nil => rfl
  | cons u a ih => cases u <;> simp [levelDels, ih]

theorem ci_levelPuts_append (a b : List ReqOp) :
    levelPuts (a ++ b) = levelPuts a ++ levelPuts b := by
  induction a with
  | nil => rfl
  | cons u a ih => cases u <;> simp [levelPuts, ih]

theorem ci_ivNest_append (a b : List ReqOp) :
    ivNest (a ++ b) = (ivNest a).bind (fun x => (ivNest b).map (fun y => x ++ y)) := by
  induction a with
  | nil => cases h : ivNest b <;> simp [ivNest, h]
  | cons u a ih =>
    cases u with
    | txn cs ts es =>
      simp only [List.cons_append, ivNest, ih]
      cases (ivNest ts).bind (ivFinish ts) with
      | none => simp
      | some x =>
        cases (ivNest es).bind (ivFinish es) with
        | none => simp
        | some y =>
          cases ivNest a with
          | none => simp
          | some z => cases ivNest b <;> simp
    | _ => simp [ivNest, ih]

theorem ci_take_succ {us : List ReqOp} {k : Nat} {u : ReqOp} (h : us[k]? = some u) :
    us.take (k + 1) = us.take k ++ [u] := by
  rw [List.take_add_one, h]; rfl

theorem ci_foldl_nestStep_none (l : List NestRes) : l.foldl nestStep none = none := by
  induction l with
  | nil => rfl
  | cons r l ih => simpa [nestStep] using ih

theorem ci_foldl_putStep_none (l : List GoString) : l.foldl putStep none = none := by
  induction l with
  | nil => rfl
  | cons r l ih => simpa [putStep] using ih

theorem ci_ivNest_snoc_other {l : List ReqOp} {u : ReqOp}
    (h : ∀ cs ts es, u ≠ .txn cs ts es) : ivNest (l ++ [u]) = ivNest l := by
  rw [ci_ivNest_append]
  have : ivNest [u] = some [] := by
    cases u with
    | txn cs ts es => exact absurd rfl (h cs ts es)
    | _ => simp [ivNest]
  rw [this]; cases ivNest l <;> simp

theorem ci_ivNest_snoc_txn_some {l : List ReqOp} {x : List NestRes} {cs : List CmpModel}
    {ts es : List ReqOp} {pT pE : List GoString} {dT dE : List adt.IvlS}
    (hl : ivNest l = some x) (ht : ivCheck ts = some (pT, dT)) (he : ivCheck es = some (pE, dE)) :
    ivNest (l ++ [.txn cs ts es]) = some (x ++ [⟨pT, dT, pE, dE⟩]) := by
  rw [ci_ivNest_append, hl]
  unfold ivCheck at ht he
  simp [ivNest, ht, he]

theorem ci_ivNest_snoc_txn_none {l : List ReqOp} {cs : List CmpModel} {ts es : List ReqOp}
    (h : ivCheck ts = none ∨ ivCheck es = none) : ivNest (l ++ [.txn cs ts es]) = none := by
  rw [ci_ivNest_append]
  unfold ivCheck at h
  have : ivNest [.txn cs ts es] = none := by
    rcases h with h | h
    · simp [ivNest, h]
    · simp only [ivNest, h]
      cases (ivNest ts).bind (ivFinish ts) <;> rfl
  rw [this]; cases ivNest l <;> rfl

theorem ci_ivCheck_none_of_take {us : List ReqOp} {k : Nat} (h : ivNest (us.take k) = none) :
    ivCheck us = none := by
  unfold ivCheck
  rw [← List.take_append_drop k us, ci_ivNest_append, h]
  rfl

theorem ci_ivCheck_none_of_fold {us : List ReqOp} {k : Nat} {x : List NestRes}
    (h1 : ivNest (us.take k) = some x)
    (h2 : x.foldl nestStep (some ([], levelDels us)) = none) : ivCheck us = none := by
  unfold ivCheck
  have hus := List.take_append_drop k us
  rw [← hus, ci_ivNest_append, h1]
  cases hd : ivNest (us.drop k) with
  | none => rfl
  | some y =>
    simp only [Option.bind_some, Option.map_some]
    unfold ivFinish
    rw [hus, List.foldl_append, h2, ci_foldl_nestStep_none, ci_foldl_putStep_none]

theorem ci_foldl_putStep_dels (l : List GoString) (p : List GoString) (d : List adt.IvlS)
    (p' : List GoString) (d' : List adt.IvlS) (h : l.foldl putStep (some (p, d)) = some (p', d')) :
    d' = d := by
  induction l generalizing p with
  | nil => simp at h; exact h.2.symm
  | cons k l ih =>
    simp only [List.foldl_cons, putStep] at h
    split at h
    · rw [ci_foldl_putStep_none] at h; cases h
    · exact ih _ h

theorem ci_ivCheck_put_bad {us : List ReqOp} {nest : List NestRes} {pts pts' : List GoString}
    {ds : List adt.IvlS} {j : Nat} {o : OpFull}
    (hnest : ivNest us = some nest) (hf : nest.foldl nestStep (some ([], levelDels us)) = some (pts, ds))
    (hu : us[j]? = some (.put o))
    (hpre : (levelPuts (us.take j)).foldl putStep (some (pts, ds)) = some (pts', ds))
    (hbad : (decide (o.key ∈ pts') || hits ds o.key) = true) : ivCheck us = none := by
  unfold ivCheck ivFinish
  rw [hnest]
  simp only [Option.bind_some]
  rw [hf, ← List.take_append_drop (j + 1) us, ci_levelPuts_append, ci_take_succ hu,
    ci_levelPuts_append, List.foldl_append, List.foldl_append, hpre]
  simp only [levelPuts, List.foldl_cons, List.foldl_nil, putStep, hbad, ↓reduceIte]
  exact ci_foldl_putStep_none _

theorem ci_put_good {us : List ReqOp} {pts pts' : List GoString} {ds : List adt.IvlS} {j : Nat}
    {o : OpFull} (hu : us[j]? = some (.put o))
    (hpre : (levelPuts (us.take j)).foldl putStep (some (pts, ds)) = some (pts', ds))
    (hgood : (decide (o.key ∈ pts') || hits ds o.key) = false) :
    (levelPuts (us.take (j + 1))).foldl putStep (some (pts, ds)) = some (pts' ++ [o.key], ds) := by
  rw [ci_take_succ hu, ci_levelPuts_append, List.foldl_append, hpre]
  simp [levelPuts, putStep, hgood]

theorem ci_put_other {us : List ReqOp} {j : Nat} {u : ReqOp} (hu : us[j]? = some u)
    (h : ∀ o, u ≠ .put o) : levelPuts (us.take (j + 1)) = levelPuts (us.take j) := by
  rw [ci_take_succ hu, ci_levelPuts_append]
  cases u with
  | put o => exact absurd rfl (h o)
  | _ => simp [levelPuts]

theorem ci_insert_keys {M : GMap GoString Unit} {ks : List GoString}
    (h : ∀ x, (M !! x).isSome = true ↔ x ∈ ks) (k : GoString) :
    ∀ x, ((<[k := ()]> M) !! x).isSome = true ↔ x ∈ ks ++ [k] := by
  intro x
  rw [GMap.lookup_insert_is_Some]
  by_cases hx : k = x
  · subst hx; simp
  · have := h x
    constructor
    · rintro (h1 | ⟨-, h2⟩)
      · exact absurd h1 hx
      · exact List.mem_append_left _ (this.1 h2)
    · intro hm
      rcases List.mem_append.1 hm with h1 | h1
      · exact Or.inr ⟨hx, this.2 h1⟩
      · simp at h1; exact absurd h1.symm hx

theorem ci_not_mem_take {α : Type} {keys : List α} {j : Nat} {k : α} (hnd : keys.Nodup)
    (h : keys[j]? = some k) : k ∉ keys.take j := by
  intro hm
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.1 hm
  rw [List.getElem?_take] at hi
  split at hi
  · rename_i hij
    have hj : j < keys.length := (List.getElem?_eq_some_iff.1 h).1
    have := (List.Nodup.getElem?_inj (i := i) (j := j) (by omega) hnd).1 (by rw [hi, h])
    omega
  · cases hi

theorem ci_mem_take_succ {α : Type} {keys : List α} {j : Nat} {k x : α} (h : keys[j]? = some k) :
    x ∈ keys.take (j + 1) ↔ x ∈ keys.take j ∨ x = k := by
  rw [List.take_add_one, h]; simp

theorem ci_nestStep_then_fail {pts : List GoString} {ds : List adt.IvlS} {r : NestRes} {k : GoString}
    (hk : k ∈ r.putsThen) (hb : (decide (k ∈ pts) || hits ds k) = true) :
    nestStep (some (pts, ds)) r = none := by
  unfold nestStep
  have : r.putsThen.any (fun k => decide (k ∈ pts) || hits ds k) = true :=
    List.any_eq_true.2 ⟨k, hk, hb⟩
  simp [this]

theorem ci_nestStep_else_fail {pts : List GoString} {ds : List adt.IvlS} {r : NestRes} {k : GoString}
    (hk : k ∈ r.putsElse) (hb : (decide (k ∈ pts ++ r.putsThen ∧ k ∉ r.putsThen) || hits ds k) = true) :
    nestStep (some (pts, ds)) r = none := by
  unfold nestStep
  have : r.putsElse.any (fun k => decide (k ∈ pts ++ r.putsThen ∧ k ∉ r.putsThen) || hits ds k) = true :=
    List.any_eq_true.2 ⟨k, hk, hb⟩
  split <;> simp_all

theorem ci_nestStep_ok {pts : List GoString} {ds : List adt.IvlS} {r : NestRes}
    (ht : ∀ k ∈ r.putsThen, (decide (k ∈ pts) || hits ds k) = false)
    (he : ∀ k ∈ r.putsElse, (decide (k ∈ pts ++ r.putsThen ∧ k ∉ r.putsThen) || hits ds k) = false) :
    ∃ pts', nestStep (some (pts, ds)) r = some (pts', ds ++ unionSel r.delsThen ++ unionSel r.delsElse) ∧
      ∀ x, x ∈ pts' ↔ x ∈ pts ∨ x ∈ r.putsThen ∨ x ∈ r.putsElse := by
  have h1 : r.putsThen.any (fun k => decide (k ∈ pts) || hits ds k) = false := by
    rw [List.any_eq_false]; intro k hk; simp [ht k hk]
  have h2 : r.putsElse.any (fun k => decide (k ∈ pts ++ r.putsThen ∧ k ∉ r.putsThen) || hits ds k)
      = false := by
    rw [List.any_eq_false]; intro k hk; rw [he k hk]; simp
  refine ⟨pts ++ r.putsThen ++ r.putsElse.filter (fun k => decide (k ∉ pts ++ r.putsThen)), ?_, ?_⟩
  · simp only [nestStep, h1, h2]; rfl
  · intro x
    simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ((h | h) | ⟨h, -⟩) <;> simp_all
    · rintro (h | h | h)
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · by_cases hx : x ∈ pts ∨ x ∈ r.putsThen
        · exact Or.inl hx
        · exact Or.inr ⟨h, by simpa using hx⟩

theorem ci_txn_step_fail {us : List ReqOp} {n : Nat} {nest : List NestRes} {pts : List GoString}
    {ds : List adt.IvlS} {cs : List CmpModel} {ts es : List ReqOp} {pT pE : List GoString}
    {dT dE : List adt.IvlS}
    (hnest : ivNest (us.take n) = some nest)
    (hf : nest.foldl nestStep (some ([], levelDels us)) = some (pts, ds))
    (hu : us[n]? = some (.txn cs ts es)) (hT : ivCheck ts = some (pT, dT))
    (hE : ivCheck es = some (pE, dE))
    (hfail : nestStep (some (pts, ds)) (NestRes.mk pT dT pE dE) = none) : ivCheck us = none := by
  refine ci_ivCheck_none_of_fold (k := n + 1) (x := nest ++ [(NestRes.mk pT dT pE dE)]) ?_ ?_
  · rw [ci_take_succ hu]; exact ci_ivNest_snoc_txn_some hnest hT hE
  · rw [List.foldl_append, hf]; simpa using hfail

theorem ci_txn_step_ok {us : List ReqOp} {n : Nat} {nest : List NestRes} {pts pts' : List GoString}
    {ds ds' : List adt.IvlS} {cs : List CmpModel} {ts es : List ReqOp} {pT pE : List GoString}
    {dT dE : List adt.IvlS}
    (hnest : ivNest (us.take n) = some nest)
    (hf : nest.foldl nestStep (some ([], levelDels us)) = some (pts, ds))
    (hu : us[n]? = some (.txn cs ts es)) (hT : ivCheck ts = some (pT, dT))
    (hE : ivCheck es = some (pE, dE))
    (hok : nestStep (some (pts, ds)) (NestRes.mk pT dT pE dE) = some (pts', ds')) :
    ivNest (us.take (n + 1)) = some (nest ++ [(NestRes.mk pT dT pE dE)]) ∧
      (nest ++ [(NestRes.mk pT dT pE dE)]).foldl nestStep (some ([], levelDels us)) = some (pts', ds') := by
  refine ⟨?_, ?_⟩
  · rw [ci_take_succ hu]; exact ci_ivNest_snoc_txn_some hnest hT hE
  · rw [List.foldl_append, hf]; simpa using hok

section ffi
variable [FfiSyntax]

theorem ci_hits_perm (L : List adt.Entry) (ds : List adt.IvlS) (k : GoString)
    (h : (L.map Prod.fst).Perm ds) :
    decide (adt.stab (pointIvl k) L ≠ []) = hits ds k := by
  unfold adt.stab hits
  rw [Bool.eq_iff_iff, decide_eq_true_iff, List.any_eq_true, Ne, List.filter_eq_nil_iff]
  constructor
  · intro hn
    exact Classical.byContradiction fun hc =>
      hn fun z hz hcz => hc ⟨z.1, h.subset (List.mem_map_of_mem hz), hcz⟩
  · rintro ⟨d, hd, hc⟩ hall
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 (h.symm.subset hd)
    exact hall z hz hc

theorem ci_insert_perm (z : adt.Entry) (L : List adt.Entry) (ds : List adt.IvlS)
    (h : (L.map Prod.fst).Perm ds) : ((adt.ivtInsert z L).map Prod.fst).Perm (ds ++ [z.1]) := by
  refine ((adt.ivtInsert_perm z L).map Prod.fst).trans ?_
  rw [List.map_cons]
  exact (h.cons z.1).trans (List.perm_append_singleton _ _).symm

theorem ci_foldl_insert_perm (zs L : List adt.Entry) :
    (zs.foldl (fun acc z => adt.ivtInsert z acc) L).Perm (L ++ zs) := by
  induction zs generalizing L with
  | nil => simp
  | cons z zs ih =>
    simp only [List.foldl_cons]
    refine (ih _).trans ?_
    refine ((adt.ivtInsert_perm z L).append_right zs).trans ?_
    exact List.perm_middle.symm

theorem ci_union_perm (L L' zs : List adt.Entry) (ds d' : List adt.IvlS)
    (h : (L.map Prod.fst).Perm ds) (h' : (L'.map Prod.fst).Perm d')
    (hz : zs.Perm (adt.stab unionIvl L')) :
    ((zs.foldl (fun acc z => adt.ivtInsert z acc) L).map Prod.fst).Perm (ds ++ unionSel d') := by
  refine ((ci_foldl_insert_perm zs L).map Prod.fst).trans ?_
  rw [List.map_append]
  refine h.append ?_
  refine (hz.map Prod.fst).trans ?_
  unfold adt.stab unionSel
  rw [show L'.filter (fun z => decide (adt.ivlCmp unionIvl z.fst = 0)) =
    L'.filter ((fun d => decide (adt.ivlCmp unionIvl d = 0)) ∘ Prod.fst) from rfl,
    ← List.filter_map]
  exact h'.filter _

end ffi

end v3rpc

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver.api go_etcd_io.etcd.server.v3.etcdserver
  go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

theorem v3rpc.ci_reqOpsIs_len :
    ∀ (ps : List Loc) (us : List v3rpc.ReqOp),
      v3rpc.reqOpsIs (GF := GF) ps us ⊢ ⌜ps.length = us.length⌝
  | [], [] => by iintro -; ipureintro; rfl
  | [], _ :: _ => by unfold v3rpc.reqOpsIs; iintro H; iexfalso; iexact H
  | _ :: _, [] => by unfold v3rpc.reqOpsIs; iintro H; iexfalso; iexact H
  | p :: ps, u :: us => by
    unfold v3rpc.reqOpsIs
    iintro ⟨-, H⟩
    ihave %h := v3rpc.ci_reqOpsIs_len ps us $$ H
    ipureintro; simp [h]

theorem v3rpc.ci_reqOpsIs_get :
    ∀ (ps : List Loc) (us : List v3rpc.ReqOp) (i : Nat) (p : Loc) (u : v3rpc.ReqOp),
      ps[i]? = some p → us[i]? = some u →
      v3rpc.reqOpsIs (GF := GF) ps us ⊢ v3rpc.reqOpIs p u
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | q :: ps, w :: us, 0, p, u, h, h' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h h'
    subst h h'
    unfold v3rpc.reqOpsIs
    iintro ⟨H, -⟩; iexact H
  | q :: ps, w :: us, i + 1, p, u, h, h' => by
    simp only [List.getElem?_cons_succ] at h h'
    unfold v3rpc.reqOpsIs
    iintro ⟨-, H⟩
    iapply v3rpc.ci_reqOpsIs_get ps us i p u h h' $$ H

theorem v3rpc.ci_reqOpsWire_get :
    ∀ (ps : List Loc) (us : List v3rpc.ReqOp) (i : Nat) (p : Loc) (u : v3rpc.ReqOp),
      ps[i]? = some p → us[i]? = some u →
      v3rpc.reqOpsWire (GF := GF) ps us ⊢ v3rpc.reqOpWire p u
  | [], _, _, _, _, h, _ => by simp at h
  | _ :: _, [], _, _, _, _, h => by simp at h
  | q :: ps, w :: us, 0, p, u, h, h' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h h'
    subst h h'
    unfold v3rpc.reqOpsWire
    iintro ⟨H, -⟩; iexact H
  | q :: ps, w :: us, i + 1, p, u, h, h' => by
    simp only [List.getElem?_cons_succ] at h h'
    unfold v3rpc.reqOpsWire
    iintro ⟨-, H⟩
    iapply v3rpc.ci_reqOpsWire_get ps us i p u h h' $$ H

/-- The spec's postcondition, as the hypothesis `wp_start` names `HΦ` (the loops' invariants
carry it, for their early returns). -/
def v3rpc.ciPost (us : List v3rpc.ReqOp) (Φ : val → IProp GF) : IProp GF :=
  iprop(∀ (m : Loc) (t err : GoInterface), (match v3rpc.ivCheck us with
      | some (puts, ds) => ⌜err = GoInterface.nil⌝ ∗
          (∃ M : GMap GoString Unit, m ↦$ M ∗ ⌜∀ k, (M !! k).isSome = true ↔ k ∈ puts⌝) ∗
          (∃ (tl : Loc) (L : List adt.Entry),
            ⌜t = interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tl⌝ ∗
            adt.ownIvt tl L ∗ ⌜(L.map Prod.fst).Perm ds⌝)
      | none => txn.errVarIs v3rpc.CheckErr.duplicateKey.var err) -∗
    Φ (PairV (PairV #m #t) #err))

theorem v3rpc.checkIntervals.wp_proof
    (hNew : adt.NewIntervalTree.spec (GF := GF) (hG := hG))
    (hIvl : adt.NewStringAffineInterval.spec (GF := GF) (hG := hG))
    (hPt : adt.NewStringAffinePoint.spec (GF := GF) (hG := hG))
    (hIns : adt.intervalTree.InsertAny.spec (GF := GF) (hG := hG))
    (hInt : adt.intervalTree.Intersects.spec (GF := GF) (hG := hG))
    (hUnion : adt.intervalTree.Union.spec (GF := GF) (hG := hG)) :
    v3rpc.checkIntervals.spec (GF := GF) (hG := hG) := by
  intro sl ps us
  iloeb as IH generalizing %sl %ps %us
  wp_start as ⟨#Hsl, #Hps, #Hwire⟩
  ihave #Padt : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.pkg.v3.adt $$ []
  · iPkgInit
  wp_auto
  ihave Hinit : (go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.v3rpcInit : IProp GF) $$ []
  · iapply isPkgInit_access $$ Hpkg
  icases Hinit with ⟨-, ⟨-, -, -, -, -, #Hdup, -⟩, -, -⟩
  iunfold go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.errVarSet at Hdup
  icases Hdup with ⟨%edup, #Hdup⟩
  wp_apply hNew as %tl Htl
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  ihave %Hlen := v3rpc.ci_reqOpsIs_len ps us $$ Hps
  ihave HI : iprop(∃ (n : w64) (q : Loc) (L : List adt.Entry),
      "i" ∷ i_ptr ↦ n ∗ "req" ∷ req_ptr ↦ q ∗ "Htl" ∷ adt.ownIvt tl L ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝ ∗
      "%HL" ∷ ⌜(L.map Prod.fst).Perm (v3rpc.levelDels (us.take (sint.Z n).toNat))⌝) $$ [i req Htl]
  · iexists W64 0, _, []
    iframe i req Htl
    ipureintro
    refine ⟨⟨by decide, by have := Hsll.2; word⟩, ?_⟩
    simp [v3rpc.levelDels]
  wp_for HI
  wp_if_destruct
  · obtain ⟨p, hp⟩ : ∃ p, ps[(sint.Z n).toNat]? = some p :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
    obtain ⟨u, hu⟩ : ∃ u, us[(sint.Z n).toNat]? = some u :=
      ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; rw [← Hlen]; word)⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) ps DFrac.discard p Hn.1 $$ [] as -
    · iframe Hsl; ipureintro; exact hp
    ihave #Hp := v3rpc.ci_reqOpsIs_get ps us _ p u hp hu $$ Hps
    ihave #Hw := v3rpc.ci_reqOpsWire_get ps us _ p u hp hu $$ Hwire
    cases u with
    | delete o =>
      iunfold v3rpc.reqOpIs at Hp
      icases Hp with ⟨%Hpn, %w, %r, #HR, #Hw', #Hr⟩
      iunfold txn.deleteRangeRequestIs at Hr
      icases Hr with ⟨%Hrn, %ksl, %esl, %k, %e, %pk, #HK, #Hk, #HE, #He, #HPK, %Ho⟩
      iunfold v3rpc.reqOpWire at Hw
      ihave %Hwe := Hw $$ %w %r %esl HR Hw' HE
      ihave %Hel := ownSlice_len _ _ _ $$ He
      wp_auto
      simp only [Hrn, decide_false]
      wp_auto
      wp_if_destruct
      · wp_apply wp_bytes_to_string ksl k DFrac.discard $$ [$Hk] as -
        wp_apply hPt
        wp_apply hIns $$ [$Htl] as Htl
        have hesl : esl = slice.nil := Hwe.resolve_right (fun h => h Hif)
        have hdel : v3rpc.delIvl o = (k, k ++ [W8 0]) := by
          subst Ho; simp [v3rpc.delIvl, txn.rangeEndOf, hesl, v3rpc.pointIvl]
        wp_for_post
        iframe
        iexists n + W64 1, p, _
        iframe
        ipureintro
        refine ⟨by constructor <;> word, ?_⟩
        rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
          v3rpc.ci_levelDels_append]
        simp only [v3rpc.levelDels]
        rw [hdel]
        exact v3rpc.ci_insert_perm _ _ _ HL
      · have he : e ≠ [] := by
          intro h; subst h; apply Hif; simp at Hel; unfold sint.nat at Hel; word
        have hesl : esl ≠ slice.nil := by intro h; subst h; apply Hif; rfl
        have hdel : v3rpc.delIvl o = (k, e) := by
          subst Ho; simp [v3rpc.delIvl, txn.rangeEndOf, hesl, he]
        wp_apply wp_bytes_to_string ksl k DFrac.discard $$ [$Hk] as -
        wp_apply wp_bytes_to_string esl e DFrac.discard $$ [$He] as -
        wp_apply hIvl
        wp_apply hIns $$ [$Htl] as Htl
        wp_for_post
        iframe
        iexists n + W64 1, p, _
        iframe
        ipureintro
        refine ⟨by constructor <;> word, ?_⟩
        rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
          v3rpc.ci_levelDels_append]
        simp only [v3rpc.levelDels]
        rw [hdel]
        exact v3rpc.ci_insert_perm _ _ _ HL
    | txn cs ts es =>
      iunfold v3rpc.reqOpIs at Hp
      icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p, L
      iframe
      ipureintro
      refine ⟨by constructor <;> word, ?_⟩
      rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
        v3rpc.ci_levelDels_append]
      simpa [v3rpc.levelDels] using HL
    | empty =>
      iunfold v3rpc.reqOpIs at Hp
      icases Hp with ⟨%Hpn, #HR⟩
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p, L
      iframe
      ipureintro
      refine ⟨by constructor <;> word, ?_⟩
      rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
        v3rpc.ci_levelDels_append]
      simpa [v3rpc.levelDels] using HL
    | range o =>
      iunfold v3rpc.reqOpIs at Hp
      icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p, L
      iframe
      ipureintro
      refine ⟨by constructor <;> word, ?_⟩
      rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
        v3rpc.ci_levelDels_append]
      simpa [v3rpc.levelDels] using HL
    | put o =>
      iunfold v3rpc.reqOpIs at Hp
      icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p, L
      iframe
      ipureintro
      refine ⟨by constructor <;> word, ?_⟩
      rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
        v3rpc.ci_levelDels_append]
      simpa [v3rpc.levelDels] using HL
  · have hn : (sint.Z n).toNat = us.length := by
      rw [← Hlen, Hsll.1]; unfold sint.nat; word
    rw [hn, List.take_length] at HL
    try wp_auto
    wp_apply (wp_map_make1 (K := GoString) (V := Unit) go.string (go.StructType [])) as %mp Hmp
    ihave HI : iprop(∃ (n : w64) (q : Loc) (L : List adt.Entry) (M : GMap GoString Unit)
        (nest : List v3rpc.NestRes) (pts : List GoString) (ds : List adt.IvlS),
        "i" ∷ i_ptr ↦ n ∗ "req" ∷ req_ptr ↦ q ∗ "Htl" ∷ adt.ownIvt tl L ∗ "Hmp" ∷ mp ↦$ M ∗
        "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝ ∗
        "%Hnest" ∷ ⌜v3rpc.ivNest (us.take (sint.Z n).toNat) = some nest ∧
          nest.foldl v3rpc.nestStep (some ([], v3rpc.levelDels us)) = some (pts, ds)⌝ ∗
        "%HL" ∷ ⌜(L.map Prod.fst).Perm ds⌝ ∗
        "%HM" ∷ ⌜∀ x, (M !! x).isSome = true ↔ x ∈ pts⌝) $$ [i req Htl Hmp]
    · iexists W64 0, _, L, ∅, [], [], v3rpc.levelDels us
      iframe i req Htl Hmp
      ipureintro
      refine ⟨⟨by decide, by have := Hsll.2; word⟩, ⟨by simp [v3rpc.ivNest], rfl⟩, HL, ?_⟩
      intro x; simp
    wp_for HI
    wp_if_destruct
    · obtain ⟨p, hp⟩ : ∃ p, ps[(sint.Z n).toNat]? = some p :=
        ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
      obtain ⟨u, hu⟩ : ∃ u, us[(sint.Z n).toNat]? = some u :=
        ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; rw [← Hlen]; word)⟩
      have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
      simp only [Hbnd, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index sl (sint.Z n) ps DFrac.discard p Hn.1 $$ [] as -
      · iframe Hsl; ipureintro; exact hp
      ihave #Hp := v3rpc.ci_reqOpsIs_get ps us _ p u hp hu $$ Hps
      ihave #Hw := v3rpc.ci_reqOpsWire_get ps us _ p u hp hu $$ Hwire
      cases u with
      | txn cs ts es =>
        iunfold v3rpc.reqOpIs at Hp
        icases Hp with ⟨%Hpn, %w, %r, #HR, #Hw', %Hrn, %csl, %ssl, %fsl, %cps, %sps, %fps, #HC,
          #Hcsl, #Hcs, #HS, #Hssl, #Hss, #HF, #Hfsl, #Hfs⟩
        iunfold v3rpc.reqOpWire at Hw
        ihave ⟨#HwS, #HwF⟩ := Hw $$ %w %r %ssl %fsl %sps %fps HR Hw' HS Hssl HF Hfsl
        wp_auto
        wp_apply IH $$ %ssl %sps %ts [] as %mT %tT %errT HT
        · iframe #
        cases hT : v3rpc.ivCheck ts with
        | none =>
          dsimp only
          iunfold txn.errVarIs at HT
          icases HT with ⟨%e1, #He1, %Herr1⟩
          subst Herr1
          wp_auto
          wp_for_post
          iapply HΦ
          rw [v3rpc.ci_ivCheck_none_of_take (k := (sint.Z n).toNat + 1)
            (by rw [v3rpc.ci_take_succ hu]; exact v3rpc.ci_ivNest_snoc_txn_none (Or.inl hT))]
          iunfold txn.errVarIs
          iexists e1
          iframe He1
          ipureintro; rfl
        | some pdT =>
          obtain ⟨pT, dT⟩ := pdT
          icases HT with ⟨%HerrT, ⟨%MT, HmT, %HMT⟩, ⟨%tlT, %LT, %HtT, HtlT, %HLT⟩⟩
          subst HerrT HtT
          wp_auto
          wp_apply IH $$ %fsl %fps %es [] as %mE %tE %errE HE
          · iframe #
          cases hE : v3rpc.ivCheck es with
          | none =>
            dsimp only
            iunfold txn.errVarIs at HE
            icases HE with ⟨%e1, #He1, %Herr1⟩
            subst Herr1
            wp_auto
            wp_for_post
            iapply HΦ
            rw [v3rpc.ci_ivCheck_none_of_take (k := (sint.Z n).toNat + 1)
              (by rw [v3rpc.ci_take_succ hu]; exact v3rpc.ci_ivNest_snoc_txn_none (Or.inr hE))]
            iunfold txn.errVarIs
            iexists e1
            iframe He1
            ipureintro; rfl
          | some pdE =>
            obtain ⟨pE, dE⟩ := pdE
            icases HE with ⟨%HerrE, ⟨%ME, HmE, %HME⟩, ⟨%tlE, %LE, %HtE, HtlE, %HLE⟩⟩
            subst HerrE HtE
            wp_auto
            wp_func_lits
            wp_bind (App (App (Val (map.forRange _ _)) _) _)
            iapply wp_map_for_range (K := GoString) (V := Unit) (fun (keys : List GoString) (j : Int) =>
                iprop(∃ (M' : GMap GoString Unit) (kv : GoString),
                "HΦ" ∷ v3rpc.ciPost us Φ ∗ "k" ∷ k_ptr ↦ kv ∗ "Hmp" ∷ mp ↦$ M' ∗
                "Htl" ∷ adt.ownIvt tl L ∗ "dels" ∷ dels_ptr ↦
                  (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tl :
                    GoInterface) ∗
                "puts" ∷ puts_ptr ↦ mp ∗ "%Hj" ∷ ⌜0 ≤ j⌝ ∗
                "%HM'" ∷ ⌜∀ x, (M' !! x).isSome = true ↔ x ∈ pts ∨ x ∈ keys.take j.toNat⌝ ∗
                "%Hok" ∷ ⌜∀ x ∈ keys.take j.toNat, (decide (x ∈ pts) || v3rpc.hits ds x) = false⌝))
              $$ HmT
            iintro %keysT ⟨%HkT, %HklT, %HkndT⟩
            isplitl [HΦ k Hmp Htl dels puts]
            · iexists M, _
              simp only [named]
              iframe k Hmp Htl dels puts
              isplitl [HΦ]
              · iunfold v3rpc.ciPost; iexact HΦ
              ipureintro
              refine ⟨Int.le_refl _, ?_, ?_⟩
              · intro x; simp [HM x]
              · intro x hx; simp at hx
            isplitr
            · imodintro
              iintro %j %key %v ⟨%Hkey, %Hv⟩ HP
              iNamed HP
              wp_auto
              have hkeyT : key ∈ pT := (HMT key).1 (by rw [Hv]; rfl)
              have hkeyM : key ∈ keysT := List.mem_of_getElem? Hkey
              have hnt : key ∉ keysT.take j.toNat := v3rpc.ci_not_mem_take HkndT Hkey
              wp_apply (wp_map_lookup2 (K := GoString) (V := Unit) go.string (go.StructType []) mp M'
                key (DFrac.own 1)) $$ [$Hmp] as Hmp
              cases hk : (M' !! key).isSome
              · simp only [Bool.false_eq_true, decide_false]
                wp_auto
                wp_apply hPt
                wp_apply hInt $$ [$Htl] as Htl
                have hh0 : (!decide (adt.stab (key, key ++ [0#8]) L = [])) = v3rpc.hits ds key := by
                  rw [← v3rpc.ci_hits_perm L ds key HL]
                  by_cases h : adt.stab (key, key ++ [0#8]) L = [] <;> simp [v3rpc.pointIvl, h]
                rw [hh0]
                have hkp : key ∉ pts := fun h => by
                  rw [(HM' key).2 (Or.inl h)] at hk; cases hk
                cases hh : v3rpc.hits ds key
                · wp_auto
                  wp_apply (wp_mapInsert (K := GoString) (V := Unit) go.string mp M' key ()) $$ [$Hmp]
                    as Hmp
                  unfold forMapPostcondition
                  iright; ileft
                  isplitr
                  · ipureintro; rfl
                  iexists _, _
                  simp only [named]
                  iframe
                  ipureintro
                  have hj1 : (j + 1).toNat = j.toNat + 1 := by omega
                  refine ⟨by omega, ?_, ?_⟩
                  · intro x
                    rw [hj1, v3rpc.ci_mem_take_succ Hkey, GMap.lookup_insert_is_Some, HM' x]
                    by_cases hx : key = x
                    · subst hx; simp
                    · simp [hx, Ne.symm hx]
                  · intro x hx
                    rw [hj1, v3rpc.ci_mem_take_succ Hkey] at hx
                    rcases hx with hx | rfl
                    · exact Hok x hx
                    · simp [hkp, hh]
                · wp_auto
                  unfold forMapPostcondition
                  iright; iright; iright; ileft
                  iexists _
                  isplitr
                  · ipureintro; rfl
                  iintro -
                  wp_auto
                  wp_for_post
                  iunfold v3rpc.ciPost at HΦ
                  iapply HΦ
                  rw [v3rpc.ci_txn_step_fail Hnest.1 Hnest.2 hu hT hE
                    (v3rpc.ci_nestStep_then_fail (r := ⟨pT, dT, pE, dE⟩) hkeyT (by simp [hh]))]
                  iunfold txn.errVarIs
                  simp only [v3rpc.CheckErr.var]
                  iexists edup
                  iframe Hdup
                  ipureintro; rfl
              · simp only [_root_.decide_true]
                wp_auto
                unfold forMapPostcondition
                iright; iright; iright; ileft
                iexists _
                isplitr
                · ipureintro; rfl
                iintro -
                wp_auto
                wp_for_post
                iunfold v3rpc.ciPost at HΦ
                iapply HΦ
                rw [v3rpc.ci_txn_step_fail Hnest.1 Hnest.2 hu hT hE
                  (v3rpc.ci_nestStep_then_fail (r := ⟨pT, dT, pE, dE⟩) hkeyT (by have := (HM' key).1 hk; simp [this.resolve_right hnt]))]
                iunfold txn.errVarIs
                simp only [v3rpc.CheckErr.var]
                iexists edup
                iframe Hdup
                ipureintro; rfl
            iintro HP HmT
            iNamed HP
            irename k => kold
            rw [show (↑(GMap.size MT) : Int).toNat = keysT.length by omega, List.take_length] at HM' Hok
            have HM1' : ∀ x, (M' !! x).isSome = true ↔ x ∈ pts ∨ x ∈ pT := by
              intro x; rw [HM' x, HkT x, HMT x]
            have Hok1' : ∀ x ∈ pT, (decide (x ∈ pts) || v3rpc.hits ds x) = false := by
              intro x hx; exact Hok x ((HkT x).2 ((HMT x).2 hx))
            clear HM' Hok
            wp_auto
            wp_func_lits
            wp_bind (App (App (Val (map.forRange _ _)) _) _)
            iapply wp_map_for_range (K := GoString) (V := Unit) (fun (keys : List GoString) (j : Int) =>
                iprop(∃ (M' : GMap GoString Unit) (kv : GoString),
                "HΦ" ∷ v3rpc.ciPost us Φ ∗ "k" ∷ k_ptr ↦ kv ∗ "Hmp" ∷ mp ↦$ M' ∗
                "Htl" ∷ adt.ownIvt tl L ∗ "dels" ∷ dels_ptr ↦
                  (interface.mkOk (go.GoType.PointerType go_etcd_io.etcd.pkg.v3.adt.intervalTree.ty) #tl :
                    GoInterface) ∗
                "puts" ∷ puts_ptr ↦ mp ∗ "HmT" ∷ mT ↦$ MT ∗ "putsThen" ∷ putsThen_ptr ↦ mT ∗
                "%Hj" ∷ ⌜0 ≤ j⌝ ∗
                "%HM'" ∷ ⌜∀ x, (M' !! x).isSome = true ↔ x ∈ pts ∨ x ∈ pT ∨ x ∈ keys.take j.toNat⌝ ∗
                "%Hok" ∷ ⌜∀ x ∈ keys.take j.toNat,
                  (decide (x ∈ pts ++ pT ∧ x ∉ pT) || v3rpc.hits ds x) = false⌝))
              $$ HmE
            iintro %keysE ⟨%HkE, %HklE, %HkndE⟩
            isplitl [HΦ k Hmp Htl dels puts HmT putsThen]
            · iexists M', _
              simp only [named]
              iframe
              ipureintro
              refine ⟨Int.le_refl _, ?_, ?_⟩
              · intro x; simp [HM1' x]
              · intro x hx; simp at hx
            isplitr
            · imodintro
              iintro %j %key %v ⟨%Hkey, %Hv⟩ HP
              iNamed HP
              wp_auto
              have hkeyE : key ∈ pE := (HME key).1 (by rw [Hv]; rfl)
              have hnt : key ∉ keysE.take j.toNat := v3rpc.ci_not_mem_take HkndE Hkey
              wp_apply (wp_map_lookup2 (K := GoString) (V := Unit) go.string (go.StructType []) mp M'
                key (DFrac.own 1)) $$ [$Hmp] as Hmp
              cases hk : (M' !! key).isSome
              · simp only [Bool.false_eq_true, decide_false]
                wp_auto
                have hc0 : ¬ (key ∈ pts ++ pT ∧ key ∉ pT) := by
                  rintro ⟨h1, -⟩
                  have h1' : key ∈ pts ∨ key ∈ pT ∨ key ∈ keysE.take j.toNat := by
                    rcases List.mem_append.1 h1 with h | h
                    · exact Or.inl h
                    · exact Or.inr (Or.inl h)
                  rw [(HM' key).2 h1'] at hk; cases hk
                wp_apply hPt
                wp_apply hInt $$ [$Htl] as Htl
                have hh0 : (!decide (adt.stab (key, key ++ [0#8]) L = [])) = v3rpc.hits ds key := by
                  rw [← v3rpc.ci_hits_perm L ds key HL]
                  by_cases h : adt.stab (key, key ++ [0#8]) L = [] <;> simp [v3rpc.pointIvl, h]
                rw [hh0]
                cases hh : v3rpc.hits ds key
                · wp_auto
                  wp_apply (wp_mapInsert (K := GoString) (V := Unit) go.string mp M' key ()) $$ [$Hmp]
                    as Hmp
                  unfold forMapPostcondition
                  iright; ileft
                  isplitr
                  · ipureintro; rfl
                  iexists _, _
                  simp only [named]
                  iframe
                  ipureintro
                  have hj1 : (j + 1).toNat = j.toNat + 1 := by omega
                  refine ⟨by omega, ?_, ?_⟩
                  · intro x
                    rw [hj1, v3rpc.ci_mem_take_succ Hkey, GMap.lookup_insert_is_Some, HM' x]
                    by_cases hx : key = x
                    · subst hx; simp
                    · simp [hx, Ne.symm hx]
                  · intro x hx
                    rw [hj1, v3rpc.ci_mem_take_succ Hkey] at hx
                    rcases hx with hx | rfl
                    · exact Hok x hx
                    · rw [decide_eq_false hc0, hh]
                · wp_auto
                  unfold forMapPostcondition
                  iright; iright; iright; ileft
                  iexists _
                  isplitr
                  · ipureintro; rfl
                  iintro -
                  wp_auto
                  wp_for_post
                  iunfold v3rpc.ciPost at HΦ
                  iapply HΦ
                  rw [v3rpc.ci_txn_step_fail Hnest.1 Hnest.2 hu hT hE
                    (v3rpc.ci_nestStep_else_fail (r := ⟨pT, dT, pE, dE⟩) hkeyE (by simp [hh]))]
                  iunfold txn.errVarIs
                  simp only [v3rpc.CheckErr.var]
                  iexists edup
                  iframe Hdup
                  ipureintro; rfl
              · simp only [_root_.decide_true]
                wp_auto
                wp_apply (wp_map_lookup2 (K := GoString) (V := Unit) go.string (go.StructType []) mT MT
                  key (DFrac.own 1)) $$ [$HmT] as HmT
                cases hs : (MT !! key).isSome
                · simp only [Bool.false_eq_true, decide_false]
                  wp_auto
                  have h2 : key ∉ pT := fun h => by rw [(HMT key).2 h] at hs; cases hs
                  have hb : (decide (key ∈ pts ++ pT ∧ key ∉ pT) || v3rpc.hits ds key) = true := by
                    have h1 := (HM' key).1 hk
                    have h3 : key ∈ pts := by
                      rcases h1 with h | h | h
                      · exact h
                      · exact absurd h h2
                      · exact absurd h hnt
                    simp [h2, h3]
                  unfold forMapPostcondition
                  iright; iright; iright; ileft
                  iexists _
                  isplitr
                  · ipureintro; rfl
                  iintro -
                  wp_auto
                  wp_for_post
                  iunfold v3rpc.ciPost at HΦ
                  iapply HΦ
                  rw [v3rpc.ci_txn_step_fail Hnest.1 Hnest.2 hu hT hE
                    (v3rpc.ci_nestStep_else_fail (r := ⟨pT, dT, pE, dE⟩) hkeyE hb)]
                  iunfold txn.errVarIs
                  simp only [v3rpc.CheckErr.var]
                  iexists edup
                  iframe Hdup
                  ipureintro; rfl
                · simp only [_root_.decide_true]
                  wp_auto
                  have hc0 : ¬ (key ∈ pts ++ pT ∧ key ∉ pT) := fun h => h.2 ((HMT key).1 hs)
                  wp_apply hPt
                  wp_apply hInt $$ [$Htl] as Htl
                  have hh0 : (!decide (adt.stab (key, key ++ [0#8]) L = [])) = v3rpc.hits ds key := by
                    rw [← v3rpc.ci_hits_perm L ds key HL]
                    by_cases h : adt.stab (key, key ++ [0#8]) L = [] <;> simp [v3rpc.pointIvl, h]
                  rw [hh0]
                  cases hh : v3rpc.hits ds key
                  · wp_auto
                    wp_apply (wp_mapInsert (K := GoString) (V := Unit) go.string mp M' key ()) $$ [$Hmp]
                      as Hmp
                    unfold forMapPostcondition
                    iright; ileft
                    isplitr
                    · ipureintro; rfl
                    iexists _, _
                    simp only [named]
                    iframe
                    ipureintro
                    have hj1 : (j + 1).toNat = j.toNat + 1 := by omega
                    refine ⟨by omega, ?_, ?_⟩
                    · intro x
                      rw [hj1, v3rpc.ci_mem_take_succ Hkey, GMap.lookup_insert_is_Some, HM' x]
                      by_cases hx : key = x
                      · subst hx; simp
                      · simp [hx, Ne.symm hx]
                    · intro x hx
                      rw [hj1, v3rpc.ci_mem_take_succ Hkey] at hx
                      rcases hx with hx | rfl
                      · exact Hok x hx
                      · rw [decide_eq_false hc0, hh]
                  · wp_auto
                    unfold forMapPostcondition
                    iright; iright; iright; ileft
                    iexists _
                    isplitr
                    · ipureintro; rfl
                    iintro -
                    wp_auto
                    wp_for_post
                    iunfold v3rpc.ciPost at HΦ
                    iapply HΦ
                    rw [v3rpc.ci_txn_step_fail Hnest.1 Hnest.2 hu hT hE
                      (v3rpc.ci_nestStep_else_fail (r := ⟨pT, dT, pE, dE⟩) hkeyE (by simp [hh]))]
                    iunfold txn.errVarIs
                    simp only [v3rpc.CheckErr.var]
                    iexists edup
                    iframe Hdup
                    ipureintro; rfl
            iintro HP HmE
            iNamed HP
            rw [show (↑(GMap.size ME) : Int).toNat = keysE.length by omega, List.take_length] at HM' Hok
            have HM2 : ∀ x, (M' !! x).isSome = true ↔ x ∈ pts ∨ x ∈ pT ∨ x ∈ pE := by
              intro x; rw [HM' x, HkE x, HME x]
            have Hok2 : ∀ x ∈ pE, (decide (x ∈ pts ++ pT ∧ x ∉ pT) || v3rpc.hits ds x) = false := by
              intro x hx; exact Hok x ((HkE x).2 ((HME x).2 hx))
            obtain ⟨pts', hstep, hmem⟩ := v3rpc.ci_nestStep_ok (r := ⟨pT, dT, pE, dE⟩) Hok1' Hok2
            wp_auto
            wp_apply hIvl
            wp_apply hUnion $$ [$Htl $HtlT] as ⟨%zs1, %Hz1, Htl, HtlT⟩
            wp_apply hIvl
            wp_apply hUnion $$ [$Htl $HtlE] as ⟨%zs2, %Hz2, Htl, HtlE⟩
            have HL1 := v3rpc.ci_union_perm L LT zs1 ds dT HL HLT Hz1
            have HL2 := v3rpc.ci_union_perm _ LE zs2 _ dE HL1 HLE Hz2
            obtain ⟨Hn1, Hn2⟩ := v3rpc.ci_txn_step_ok Hnest.1 Hnest.2 hu hT hE hstep
            iunfold v3rpc.ciPost at HΦ
            wp_for_post
            iframe
            iexists n + W64 1, p, _, M', _, pts', _
            iframe
            ipureintro
            refine ⟨by constructor <;> word, ?_, HL2, ?_⟩
            · rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word]
              exact ⟨Hn1, Hn2⟩
            · intro x; rw [HM2 x, hmem x]
      | delete o =>
        iunfold v3rpc.reqOpIs at Hp
        icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p, L, M, nest, pts, ds
        iframe
        ipureintro
        refine ⟨by constructor <;> word, ?_, HL, HM⟩
        rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
          v3rpc.ci_ivNest_snoc_other (by intro _ _ _ h; cases h)]
        exact Hnest
      | empty =>
        iunfold v3rpc.reqOpIs at Hp
        icases Hp with ⟨%Hpn, #HR⟩
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p, L, M, nest, pts, ds
        iframe
        ipureintro
        refine ⟨by constructor <;> word, ?_, HL, HM⟩
        rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
          v3rpc.ci_ivNest_snoc_other (by intro _ _ _ h; cases h)]
        exact Hnest
      | range o =>
        iunfold v3rpc.reqOpIs at Hp
        icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p, L, M, nest, pts, ds
        iframe
        ipureintro
        refine ⟨by constructor <;> word, ?_, HL, HM⟩
        rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
          v3rpc.ci_ivNest_snoc_other (by intro _ _ _ h; cases h)]
        exact Hnest
      | put o =>
        iunfold v3rpc.reqOpIs at Hp
        icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
        wp_auto
        wp_for_post
        iframe
        iexists n + W64 1, p, L, M, nest, pts, ds
        iframe
        ipureintro
        refine ⟨by constructor <;> word, ?_, HL, HM⟩
        rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, v3rpc.ci_take_succ hu,
          v3rpc.ci_ivNest_snoc_other (by intro _ _ _ h; cases h)]
        exact Hnest
    · have hn : (sint.Z n).toNat = us.length := by
        rw [← Hlen, Hsll.1]; unfold sint.nat; word
      rw [hn, List.take_length] at Hnest
      obtain ⟨Hnest1, Hnest2⟩ := Hnest
      clear Hif Hn hn
      try wp_auto
      ihave HI : iprop(∃ (n : w64) (q : Loc) (M : GMap GoString Unit) (pts' : List GoString),
          "i" ∷ i_ptr ↦ n ∗ "req" ∷ req_ptr ↦ q ∗ "Htl" ∷ adt.ownIvt tl L ∗ "Hmp" ∷ mp ↦$ M ∗
          "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ sint.Z sl.len⌝ ∗
          "%Hpre" ∷ ⌜(v3rpc.levelPuts (us.take (sint.Z n).toNat)).foldl v3rpc.putStep
            (some (pts, ds)) = some (pts', ds)⌝ ∗
          "%HM" ∷ ⌜∀ x, (M !! x).isSome = true ↔ x ∈ pts'⌝) $$ [i req Htl Hmp]
      · iexists W64 0, _, M, pts
        iframe i req Htl Hmp
        ipureintro
        exact ⟨⟨by decide, by have := Hsll.2; word⟩, by simp [v3rpc.levelPuts], HM⟩
      clear HM
      wp_for HI
      by_cases Hif : sint.Z n < sint.Z sl.len
      · simp only [Hif, _root_.decide_true, ↓reduceIte]
        (try wp_auto)
        obtain ⟨p, hp⟩ : ∃ p, ps[(sint.Z n).toNat]? = some p :=
          ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; word)⟩
        obtain ⟨u, hu⟩ : ∃ u, us[(sint.Z n).toNat]? = some u :=
          ⟨_, List.getElem?_eq_getElem (by unfold sint.nat at Hsll; rw [← Hlen]; word)⟩
        have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, Hif⟩
        simp only [Hbnd, _root_.and_self, ↓reduceIte]
        wp_apply wp_load_slice_index sl (sint.Z n) ps DFrac.discard p Hn.1 $$ [] as -
        · iframe Hsl; ipureintro; exact hp
        ihave #Hp := v3rpc.ci_reqOpsIs_get ps us _ p u hp hu $$ Hps
        cases u with
        | put o =>
          iunfold v3rpc.reqOpIs at Hp
          icases Hp with ⟨%Hpn, %w, %r, #HR, #Hw', #Hr⟩
          iunfold txn.putRequestIs at Hr
          icases Hr with ⟨%Hrn, %ksl, %vsl, %k, %v, %lease, %pk, %iv, %il, #HK, #Hk, -, -, -, -, -, -, -, %Hpk⟩
          wp_auto
          simp only [Hrn, decide_false]
          wp_auto
          wp_apply wp_bytes_to_string ksl k DFrac.discard $$ [$Hk] as -
          wp_apply (wp_map_lookup2 (K := GoString) (V := Unit) go.string (go.StructType []) mp M k
            (DFrac.own 1)) $$ [$Hmp] as Hmp
          have hok : o.key = k := by subst Hpk; rfl
          cases hk : (M !! k).isSome
          · simp only [Bool.false_eq_true, decide_false]
            wp_auto
            wp_apply hPt
            wp_apply hInt $$ [$Htl] as Htl
            have hh0 : (!decide (adt.stab (k, k ++ [0#8]) L = [])) = v3rpc.hits ds k := by
              rw [← v3rpc.ci_hits_perm L ds k HL]
              by_cases h : adt.stab (k, k ++ [0#8]) L = [] <;> simp [v3rpc.pointIvl, h]
            rw [hh0]
            have hk' : k ∉ pts' := fun h => by rw [(HM k).2 h] at hk; cases hk
            cases hh : v3rpc.hits ds k
            · wp_auto
              wp_apply (wp_mapInsert (K := GoString) (V := Unit) go.string mp M k ()) $$ [$Hmp] as Hmp
              wp_for_post
              iframe
              iexists n + W64 1, p, _, pts' ++ [k]
              iframe
              ipureintro
              refine ⟨by constructor <;> word, ?_, v3rpc.ci_insert_keys HM k⟩
              rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word, ← hok]
              exact v3rpc.ci_put_good hu Hpre (by rw [hok]; simp [hk', hh])
            · wp_auto
              wp_for_post
              iapply HΦ
              rw [v3rpc.ci_ivCheck_put_bad Hnest1 Hnest2 hu Hpre (by rw [hok]; simp [hh])]
              iunfold txn.errVarIs
              simp only [v3rpc.CheckErr.var]
              iexists edup
              iframe Hdup
              ipureintro; rfl
          · simp only [_root_.decide_true]
            wp_auto
            wp_for_post
            iapply HΦ
            rw [v3rpc.ci_ivCheck_put_bad Hnest1 Hnest2 hu Hpre (by rw [hok]; simp [(HM k).1 hk])]
            iunfold txn.errVarIs
            simp only [v3rpc.CheckErr.var]
            iexists edup
            iframe Hdup
            ipureintro; rfl
        | delete o =>
          iunfold v3rpc.reqOpIs at Hp
          icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, p, M, pts'
          iframe
          ipureintro
          refine ⟨by constructor <;> word, ?_, HM⟩
          rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word,
            v3rpc.ci_put_other hu (by intro _ h; cases h)]
          exact Hpre
        | empty =>
          iunfold v3rpc.reqOpIs at Hp
          icases Hp with ⟨%Hpn, #HR⟩
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, p, M, pts'
          iframe
          ipureintro
          refine ⟨by constructor <;> word, ?_, HM⟩
          rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word,
            v3rpc.ci_put_other hu (by intro _ h; cases h)]
          exact Hpre
        | range o =>
          iunfold v3rpc.reqOpIs at Hp
          icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, p, M, pts'
          iframe
          ipureintro
          refine ⟨by constructor <;> word, ?_, HM⟩
          rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word,
            v3rpc.ci_put_other hu (by intro _ h; cases h)]
          exact Hpre
        | txn cs ts es =>
          iunfold v3rpc.reqOpIs at Hp
          icases Hp with ⟨%Hpn, %w, %r, #HR, -⟩
          wp_auto
          wp_for_post
          iframe
          iexists n + W64 1, p, M, pts'
          iframe
          ipureintro
          refine ⟨by constructor <;> word, ?_, HM⟩
          rw [show (sint.Z (n + W64 1)).toNat = (sint.Z n).toNat + 1 by word,
            v3rpc.ci_put_other hu (by intro _ h; cases h)]
          exact Hpre
      · simp only [Hif, _root_.decide_false, Bool.false_eq_true, ↓reduceIte]
        (try wp_auto)
        iapply HΦ
        have hn : (sint.Z n).toNat = us.length := by
          rw [← Hlen, Hsll.1]; unfold sint.nat; word
        rw [hn, List.take_length] at Hpre
        have hc : v3rpc.ivCheck us = some (pts', ds) := by
          unfold v3rpc.ivCheck v3rpc.ivFinish; rw [Hnest1]; simp only [Option.bind_some]
          rw [Hnest2]; exact Hpre
        rw [hc]
        dsimp only
        isplitr
        · ipureintro; rfl
        isplitl [Hmp]
        · iexists M; iframe Hmp; ipureintro; exact HM
        iexists tl, L
        iframe Htl
        ipureintro; exact ⟨rfl, HL⟩

end proof

end EtcdGrove
end Perennial
