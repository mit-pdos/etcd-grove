/-
**The facts of the events the informer's store writer produces** (the DaemonSet run's track A,
decision R4: handler events carry their API facts, `evFacts`). Lean-first.

While a popped delta (or batch) is not yet applied, the store's state `σ` as its writer knows it
(`γi.sw`) is the abstract store's (`storeRel`), the log's table at its version, and the popped
deltas are chained from it (`InfP.ok`): so every event that processing them at `σ` may produce is
about the log, read off `σ` and the deltas.

* `evOk l R e`: what an event's facts say purely, of the log `l` and the registry `R`;
  `evFacts_of_evOk`: they give `evFacts` (with a past state whose log is `l`, the registry's
  elements and objects).
* `change_evOk`: a watch change `c`, next after the store's version `u`: its `DELETED` event (the
  object's key absent from the table at `c`'s version, the object's version `c`'s), its `ADDED`/
  `MODIFIED` event as an add (the object at its key at `c`'s version) or an update of the store's
  object at the key (that object at its key at `u ≤ c`'s version, same key).
* `replaced_evOk`: a relist at version `v` (at least the store's): each tombstone's object was at
  its key at the store's version `u ≤ v`, its own version at most `u`, its key absent at `v`; each
  listed object is at its key at `v`, the store's object at the key (if any) at `u`.
* `single_evOk`, `batch_evOk`: every event of a lone popped delta (`stepEv`), of a popped batch
  (`batchEvs`, each delta's over the items after the ones before it).
* `infInv_singleEvs`, `infInv_batchEvs`: through the invariant, at the writer's state `σ` while
  the popped deltas are not applied (`procPopped`): their events' facts (`evsOk`, `batchEvsOk`),
  what `handleDeltas`/`handleBatchDeltas` take from their client once they hold the lock.
-/
module

public import Proof.k8s_io.client_go.tools.cache.InformerAlloc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace informer

open Iris Iris.BI Iris.ProofMode apimodel cache

section pure
variable [GooseExts] [GoGlobalContext]

/-- **What an event's facts say**, of the log `l` and the registry `R` (`evFacts`, purely). -/
def evOk (l : List Change) (R : Reg) : cache.Ev → Prop
  | .add x _ => ∃ (o : Obj) (v : Nat), R !! x = some o ∧ tableAt l v !! o.key = some o
  | .update old new => ∃ (oo on : Obj) (u v : Nat), R !! old = some oo ∧ R !! new = some on ∧
      oo.key = on.key ∧ u ≤ v ∧ tableAt l u !! oo.key = some oo ∧ tableAt l v !! on.key = some on
  | .delete x => ∃ (y : GoInterface) (o : Obj) (v : Nat) (n : w64),
      (x = y ∨ ∃ k, x = tombstone k y) ∧ R !! y = some o ∧ tableAt l v !! o.key = none ∧
      o.meta.ResourceVersion' = rvStr n ∧ n.toNat ≤ v

theorem lookup_objAt_of_mem (it : cache.Items) (k : GoString) (h : k ∈ it) :
    it !! k = some (cache.objAt it k) := by
  unfold cache.objAt
  rw [GMap.mem_iff] at h
  cases h' : it !! k with
  | none => rw [h'] at h; simp at h
  | some y => rfl

theorem lookup_objAt_of_ne_nil (it : cache.Items) (k : GoString) (h : cache.objAt it k ≠ interface.nil) :
    it !! k = some (cache.objAt it k) := by
  unfold cache.objAt at h ⊢
  cases h' : it !! k with
  | none => rw [h'] at h; exact absurd rfl h
  | some y => rfl

theorem fdTypeOf_deleted (τ : EvTy) : fdTypeOf τ = go!"Deleted" ↔ τ = .deleted := by
  cases τ <;> simp [fdTypeOf]

/-- The objects of the log's tables meet what the log's changes meet. -/
theorem replay_prop (P : Obj → Prop) : ∀ (l : List Change) (M : GMap Key Obj),
    (∀ key o, M !! key = some o → P o) → (∀ c ∈ l, P c.obj) →
    ∀ key o, (l.foldl applyChange M) !! key = some o → P o
  | [], M, h, _ => h
  | c :: l, M, h, hl => by
    simp only [List.foldl_cons]
    apply replay_prop P l
    · intro key o hk
      unfold applyChange at hk
      cases ht : c.typ with
      | deleted =>
        rw [ht, GMap.lookup_delete_iff] at hk
        split at hk
        · cases hk
        · exact h key o hk
      | added | modified =>
        rw [ht, GMap.lookup_insert_eq_iff] at hk
        split at hk
        · simp only [Option.some.injEq] at hk; subst hk; exact hl c List.mem_cons_self
        · exact h key o hk
    · exact fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')

/-- **An object of the table at version `v` has a version at most `v`.** -/
theorem tableAt_obj_rv (l : List Change)
    (hobj : ∀ c ∈ l, c.obj.meta.ResourceVersion' = rvStr c.rv) (v : Nat) (key : Key) (o : Obj)
    (h : tableAt l v !! key = some o) :
    ∃ n : w64, o.meta.ResourceVersion' = rvStr n ∧ n.toNat ≤ v := by
  refine replay_prop (fun o => ∃ n : w64, o.meta.ResourceVersion' = rvStr n ∧ n.toNat ≤ v)
    (l.filter (fun c => decide (c.rv.toNat ≤ v))) ∅ (by intro key o h; simp at h) ?_ key o h
  intro c hc
  obtain ⟨hcl, hcv⟩ := List.mem_filter.1 hc
  exact ⟨c.rv, hobj c hcl, by simpa using hcv⟩

theorem applyChange_del (M : GMap Key Obj) (c : Change) (h : c.typ = .deleted) :
    applyChange M c !! c.obj.key = none := by
  unfold applyChange; rw [h]; simp

theorem applyChange_put (M : GMap Key Obj) (c : Change) (h : c.typ ≠ .deleted) :
    applyChange M c !! c.obj.key = some c.obj := by
  unfold applyChange
  cases ht : c.typ with
  | deleted => exact absurd ht h
  | added | modified => simp

/-- **A watch change's events** (see the file header). -/
theorem change_evOk (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (hobj : ∀ c ∈ l, c.obj.meta.ResourceVersion' = rvStr c.rv)
    (hgood : ∀ c ∈ l, keyGood c.obj.key) (R : Reg) (σs : cache.St) (st : View) (u : Nat)
    (c : Change) (x : GoInterface) (hu : st.rv = some u) (hst : st.ok l)
    (hn : NextChange l u c) (hR : storeRel R σs st) (hx : R !! x = some c.obj) (b : Bool) :
    (c.typ = .deleted → evOk l R (.delete x)) ∧
    (c.typ ≠ .deleted → evOk l R (.add x b)) ∧
    (c.typ ≠ .deleted → ∀ y, σs.items !! keyStr c.obj.key = some y →
      evOk l R (.update y x)) := by
  have hc : c ∈ l := hn.1
  have htab : tableAt l c.rv.toNat = applyChange (tableAt l u) c := tableAt_next l hs u c hn
  have hstu : st.items = tableAt l u := by unfold View.ok at hst; rw [hu] at hst; exact hst
  obtain ⟨-, hg, -, hit⟩ := hR
  refine ⟨fun hd => ?_, fun hd => ?_, fun hd y hy => ?_⟩
  · refine ⟨x, c.obj, c.rv.toNat, c.rv, Or.inl rfl, hx, ?_, hobj c hc, Nat.le_refl _⟩
    rw [htab]; exact applyChange_del _ c hd
  · exact ⟨c.obj, c.rv.toNat, hx, by rw [htab]; exact applyChange_put _ c hd⟩
  · rcases hit (keyStr c.obj.key) with ⟨y', oy, hy', hoy, hk, hM⟩ | ⟨hnone, -⟩
    · obtain rfl : y = y' := Option.some.inj (hy.symm.trans hy')
      have hmem : oy.key ∈ st.items := by rw [GMap.mem_iff, hM]; rfl
      have hkeq : oy.key = c.obj.key := keyStr_inj _ _ (hg _ hmem) (hgood c hc) hk
      refine ⟨oy, c.obj, u, c.rv.toNat, hoy, hx, hkeq, Nat.le_of_lt hn.2.1, ?_, ?_⟩
      · rw [← hstu]; exact hM
      · rw [htab]; exact applyChange_put _ c hd
    · rw [hy] at hnone; cases hnone

/-- **A relist's events** (see the file header). -/
theorem replaced_evOk (l : List Change) (hobj : ∀ c ∈ l, c.obj.meta.ResourceVersion' = rvStr c.rv)
    (hgood : ∀ c ∈ l, keyGood c.obj.key) (R R0 : Reg) (hsub : regLe R0 R) (σs : cache.St)
    (st : View) (xs : List GoInterface) (rvs : GoString) (M : GMap Key Obj) (v : Nat)
    (hst : st.ok l) (hle : rvLe st.rv (some v)) (hM : M = tableAt l v) (hl : listRel R xs M)
    (hR : storeRel R σs st) (hreg : ∀ x ∈ xs, ∃ o, R0 !! x = some o) (b : Bool) :
    ∀ e, stepEv (regKF R0) b σs (.replaced xs rvs) e → evOk l R e := by
  intro e he
  obtain ⟨-, hg, -, hit⟩ := hR
  have hMg : ∀ key, key ∈ M → keyGood key := by rw [hM]; exact tableAt_good l v hgood
  have hMk : ∀ key o, M !! key = some o → o.key = key := by rw [hM]; exact tableAt_keyed l v
  have hKF : ∀ x ∈ xs, ∀ o, R !! x = some o → regKF R0 x = keyStr o.key := by
    intro x hx o hxo
    obtain ⟨o', ho'⟩ := hreg x hx
    have := hsub x o' ho'
    rw [hxo] at this
    cases this
    simp [regKF, ho']
  -- the store's version, when it has an object
  have hver : ∀ key o, st.items !! key = some o →
      ∃ u, u ≤ v ∧ st.items = tableAt l u := by
    intro key o h
    cases hu : st.rv with
    | none =>
      unfold View.ok at hst; rw [hu] at hst; rw [hst] at h; simp at h
    | some u =>
      refine ⟨u, ?_, ?_⟩
      · rw [hu] at hle; exact hle
      · unfold View.ok at hst; rw [hu] at hst; exact hst
  rcases he with ⟨k, hk, hkn, rfl⟩ | ⟨x, hx, rfl⟩
  · have hy := lookup_objAt_of_mem σs.items k hk
    rcases hit k with ⟨y, oy, hy', hoy, hkey, hMy⟩ | ⟨hnone, -⟩
    · obtain rfl : cache.objAt σs.items k = y := Option.some.inj (hy.symm.trans hy')
      obtain ⟨u, huv, hstu⟩ := hver _ _ hMy
      obtain ⟨n, hn, hnu⟩ := tableAt_obj_rv l hobj u oy.key oy (by rw [← hstu]; exact hMy)
      refine ⟨_, oy, v, n, Or.inr ⟨k, rfl⟩, hoy, ?_, hn, by omega⟩
      rw [← hM]
      cases hMo : M !! oy.key with
      | none => rfl
      | some o' =>
        exfalso
        obtain ⟨x, hxm, hxo⟩ := hl.2 oy.key o' hMo
        have : regKF R0 x = k := by rw [hKF x hxm o' hxo, hMk _ _ hMo, hkey]
        exact hkn (List.mem_map.2 ⟨x, hxm, this⟩)
    · rw [hy] at hnone; cases hnone
  · obtain ⟨ox, hxo, hMx⟩ := hl.1 x hx
    have hkx := hKF x hx ox hxo
    unfold putEvR
    split
    · rename_i hne
      have hy := lookup_objAt_of_ne_nil _ _ hne
      rcases hit (regKF R0 x) with ⟨y, oy, hy', hoy, hkey, hMy⟩ | ⟨hnone, -⟩
      · obtain rfl : cache.objAt σs.items (regKF R0 x) = y := Option.some.inj (hy.symm.trans hy')
        obtain ⟨u, huv, hstu⟩ := hver _ _ hMy
        have hmy : oy.key ∈ st.items := by rw [GMap.mem_iff, hMy]; rfl
        have hmx : ox.key ∈ M := by rw [GMap.mem_iff, hMx]; rfl
        have hkeq : oy.key = ox.key :=
          keyStr_inj _ _ (hg _ hmy) (hMg _ hmx) (by rw [hkey, hkx])
        exact ⟨oy, ox, u, v, hoy, hxo, hkeq, huv, by rw [← hstu]; exact hMy,
          by rw [← hM]; exact hMx⟩
      · rw [hy] at hnone; cases hnone
    · exact ⟨ox, v, hxo, by rw [← hM]; exact hMx⟩

theorem regKF_of_sub (R R0 : Reg) (hsub : regLe R0 R) (x : GoInterface) (o : Obj)
    (hx : R !! x = some o) (hreg : ∃ o, R0 !! x = some o) : regKF R0 x = keyStr o.key := by
  obtain ⟨o', ho'⟩ := hreg
  have := hsub x o' ho'
  rw [hx] at this
  cases this
  simp [regKF, ho']

/-- **A lone popped delta's events** (`stepEv`). -/
theorem single_evOk (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (hobj : ∀ c ∈ l, c.obj.meta.ResourceVersion' = rvStr c.rv)
    (hgood : ∀ c ∈ l, keyGood c.obj.key) (R R0 : Reg) (hsub : regLe R0 R) (σs : cache.St)
    (st : View) (d : cache.FD) (a : informer.Delta) (rest : List informer.Delta)
    (w : Option Nat) (hok : Inf.ok l ⟨st, a :: rest, w⟩) (hR : storeRel R σs st)
    (hfd : fdRel R d a) (hreg : ∀ x ∈ d.objs, ∃ o, R0 !! x = some o) (b : Bool) :
    ∀ e, stepEv (regKF R0) b σs d e → evOk l R e := by
  obtain ⟨hst, hch⟩ := hok
  cases d with
  | obj t x =>
    cases a with
    | change c =>
      obtain ⟨rfl, hx, -⟩ := hfd
      obtain ⟨⟨u, hu, hn⟩, -⟩ := hch
      have hkx : regKF R0 x = keyStr c.obj.key :=
        regKF_of_sub R R0 hsub x c.obj hx (hreg x (by simp [cache.FD.objs]))
      obtain ⟨hD, hA, hU⟩ := change_evOk l hs hobj hgood R σs st u c x hu hst hn hR hx b
      intro e he
      simp only [stepEv] at he
      subst he
      by_cases hd : c.typ = .deleted
      · rw [ite_cond_eq_true _ _ (eq_true ((fdTypeOf_deleted _).2 hd))]; exact hD hd
      · rw [ite_cond_eq_false _ _ (eq_false (fun h => hd ((fdTypeOf_deleted _).1 h)))]
        unfold putEv
        split
        · rename_i hin
          exact hU hd _ (by rw [← hkx]; exact lookup_objAt_of_mem _ _ hin)
        · exact hA hd
    | replaced _ _ => exact absurd hfd id
    | bookmark _ => exact absurd hfd id
  | replaced xs rvs =>
    cases a with
    | replaced M v =>
      obtain ⟨-, hl⟩ := hfd
      obtain ⟨hle, hM, -⟩ := hch
      exact replaced_evOk l hobj hgood R R0 hsub σs st xs rvs M v hst hle hM hl hR
        (fun x hx => hreg x (by simpa [cache.FD.objs] using hx)) b
    | change _ => exact absurd hfd id
    | bookmark _ => exact absurd hfd id
  | bookmark rvs =>
    intro e he
    exact absurd he id

theorem storeStepFD_obj_items (KF : GoInterface → GoString) (rvOf : GoInterface → Option GoString)
    (σ : cache.St) (t : GoString) (x : GoInterface) :
    (cache.storeStepFD KF rvOf σ (.obj t x)).items = fdItems KF σ.items (.obj t x) := by
  unfold cache.storeStepFD
  simp only [fdItems]
  split <;> rfl

/-- **A popped batch's events** (`batchEvs`, each delta's over the items after the ones before
it). -/
theorem batch_evOk (l : List Change) (hs : l.Pairwise (fun a b => a.rv.toNat < b.rv.toNat))
    (hobj : ∀ c ∈ l, c.obj.meta.ResourceVersion' = rvStr c.rv)
    (hgood : ∀ c ∈ l, keyGood c.obj.key) (R R0 : Reg) (hsub : regLe R0 R) (b : Bool) :
    ∀ (ds : List cache.FD) (abs : List informer.Delta) (σs : cache.St) (st : View)
      (rest : List informer.Delta) (w : Option Nat),
      Inf.ok l ⟨st, abs ++ rest, w⟩ → storeRel R σs st → List.Forall₂ (fdRel R) ds abs →
      (∀ d ∈ ds, ∃ t x, d = .obj t x) → (∀ x ∈ fdObjs ds, ∃ o, R0 !! x = some o) →
      ∀ e ∈ batchEvs (regKF R0) b σs.items ds, evOk l R e := by
  intro ds
  induction ds with
  | nil =>
    intro abs σs st rest w _ _ _ _ _ e he
    simp [batchEvs] at he
  | cons d ds ih =>
    intro abs σs st rest w hok hR hfd hob hreg
    obtain ⟨a, abs', rfl⟩ : ∃ a abs', abs = a :: abs' := by
      cases hfd; exact ⟨_, _, rfl⟩
    obtain ⟨hda, hfds⟩ := List.forall₂_cons.1 hfd
    obtain ⟨t, x, rfl⟩ := hob d List.mem_cons_self
    cases a with
    | replaced _ _ => exact absurd hda id
    | bookmark _ => exact absurd hda id
    | change c =>
    obtain ⟨rfl, hx, hnil⟩ := hda
    have hok' : Inf.ok l ⟨st, informer.Delta.change c :: (abs' ++ rest), w⟩ := by
      simpa using hok
    obtain ⟨hst, ⟨u, hu, hn⟩, -⟩ := hok'
    have hc : c ∈ l := hn.1
    have hregx : ∃ o, R0 !! x = some o := hreg x (by simp [fdObjs, cache.FD.obj?])
    have hkx : regKF R0 x = keyStr c.obj.key := regKF_of_sub R R0 hsub x c.obj hx hregx
    obtain ⟨hD, hA, hU⟩ := change_evOk l hs hobj hgood R σs st u c x hu hst hn hR hx b
    intro e he
    simp only [batchEvs, List.mem_cons] at he
    rcases he with rfl | he
    · unfold fdEv
      by_cases hd : c.typ = .deleted
      · rw [ite_cond_eq_true _ _ (eq_true ((fdTypeOf_deleted _).2 hd))]; exact hD hd
      · rw [ite_cond_eq_false _ _ (eq_false (fun h => hd ((fdTypeOf_deleted _).1 h)))]
        unfold putEvR
        split
        · rename_i hne
          exact hU hd _ (by rw [← hkx]; exact lookup_objAt_of_ne_nil _ _ hne)
        · exact hA hd
    · have hR' := storeRel_single R R0 hsub σs st (.obj (fdTypeOf c.typ) x) (.change c) hR
        ⟨rfl, hx, hnil⟩ (fun y hy => by
          simp only [cache.FD.objs, List.mem_singleton] at hy; subst hy; exact hregx)
        (fun c' hc' => by cases hc'; exact ⟨hgood c hc, hobj c hc⟩)
        (fun M n h => by cases h)
      have hok2 := ok_pop l hs st (.change c) (abs' ++ rest) w (by simpa using hok)
      rw [← storeStepFD_obj_items (regKF R0) (regRv R0)] at he
      exact ih abs' _ _ rest w hok2 hR' hfds
        (fun d hd => hob d (List.mem_cons_of_mem _ hd))
        (fun y hy => hreg y (by
          simp only [fdObjs, List.map_cons, List.mem_cons] at hy ⊢; exact Or.inr hy))
        e he

end pure

section iris
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : k8s_io.client_go.tools.cache.Assumptions]

/-- The registry's elements and objects, persistent. -/
def regFacts (γi : InfNames) (R : Reg) : IProp GF :=
  iprop(([∗map] x ↦ o ∈ R, x ↪[γi.reg]□ o) ∗ ([∗map] x ↦ o ∈ R, □ apimodel.objAt x DFrac.discard o))

instance regFacts_persistent (γi : InfNames) (R : Reg) : Persistent (regFacts (GF := GF) γi R) := by
  unfold regFacts; infer_instance

theorem infObjIs_of_reg (γi : InfNames) (r : Res) (R : Reg)
    (hres : ∀ x o, R !! x = some o → o.res = r) (x : GoInterface) (o : Obj)
    (h : R !! x = some o) : regFacts (GF := GF) γi R ⊢ infObjIs γi r x o := by
  unfold regFacts infObjIs
  iintro ⟨#Hreg, #Hobjs⟩
  isplitr
  · iapply (BigSepM.bigSepM_lookup (Φ := fun x o => iprop(x ↪[γi.reg]□ o)) h) $$ Hreg
  isplitr
  · iapply (BigSepM.bigSepM_lookup (Φ := fun x o => iprop(□ apimodel.objAt x DFrac.discard o)) h)
      $$ Hobjs
  · ipureintro; exact hres x o h

/-- **The pure facts of an event are its `evFacts`.** -/
theorem evFacts_of_evOk (γa : ApiNames) (r : Res) (γi : InfNames) (σp : apimodel.St) (R : Reg)
    (hres : ∀ x o, R !! x = some o → o.res = r) (e : cache.Ev)
    (h : evOk (σp.tbl r).log R e) :
    pastSt (GF := GF) γa σp ∗ regFacts γi R ⊢ evFacts γa r γi e := by
  iintro ⟨#Hp, #HR⟩
  cases e with
  | add x b =>
    obtain ⟨o, v, hxo, hv⟩ := h
    unfold evFacts
    iexists o
    isplitr
    · iapply (infObjIs_of_reg γi r R hres x o hxo) $$ HR
    · unfold inLog; iexists σp, v; iframe #; ipureintro; exact hv
  | update old new =>
    obtain ⟨oo, on, u, v, hoo, hon, hk, huv, hu, hv⟩ := h
    unfold evFacts
    iexists oo, on
    isplitr
    · iapply (infObjIs_of_reg γi r R hres old oo hoo) $$ HR
    isplitr
    · iapply (infObjIs_of_reg γi r R hres new on hon) $$ HR
    · iexists σp, u, v; iframe #; ipureintro; exact ⟨hk, huv, hu, hv⟩
  | delete x =>
    obtain ⟨y, o, v, n, hxy, hyo, hv, hn, hnv⟩ := h
    unfold evFacts
    iexists y, o
    isplitr
    · ipureintro; exact hxy
    isplitr
    · iapply (infObjIs_of_reg γi r R hres y o hyo) $$ HR
    · unfold goneAfter; iexists σp, v, n; iframe #; ipureintro; exact ⟨hv, hn, hnv⟩

/-- **The facts of a list of events**, each with its pure facts. -/
theorem evFacts_list (γa : ApiNames) (r : Res) (γi : InfNames) (σp : apimodel.St) (R : Reg)
    (hres : ∀ x o, R !! x = some o → o.res = r) (L : List cache.Ev)
    (h : ∀ e ∈ L, evOk (σp.tbl r).log R e) :
    □ (pastSt (GF := GF) γa σp ∗ regFacts γi R) ⊢ [∗list] e ∈ L, evFacts γa r γi e :=
  BigSepL.bigSepL_intro (fun _ e he => intuitionistically_elim.trans
    (evFacts_of_evOk γa r γi σp R hres e (h e (List.mem_of_getElem? he))))

/-- **A lone popped delta's events' facts, through the invariant**: see the file header. -/
theorem infInv_singleEvs (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (R0 : Reg) (d : cache.FD) (b : Bool) (σ : cache.St)
    (hreg : ∀ x ∈ d.objs, ∃ o, R0 !! x = some o) :
    ⊢ infInv γa r γf γt γi -∗ ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) -∗
      ghostVar γi.sw (1 : Qp).half σ -∗ procPopped γi [d] b ={⊤}=∗
      ghostVar γi.sw (1 : Qp).half σ ∗ procPopped γi [d] b ∗
      evsOk (evFacts γa r γi) (regKF R0) b σ d := by
  iintro #Hinv #Hsnap Hsw' Hpop'
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw,
    Hlast, Hpop, Hlb, Hfst, Hix, %Hok⟩
  iunfold procPopped at Hpop'
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  ihave #Hp2 := Hp
  iunfold pastSt at Hp2
  icases Hp2 with ⟨%Hh, -, %hH⟩
  have hwf := hH.2.1
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  have hpop' := hpop
  unfold poppedRel at hpop'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpop'
  obtain ⟨a, ha, hfd⟩ := forall₂_singleton hpop'
  have hok' : Inf.ok (σp.tbl r).log ⟨s.store, a :: s.fifo, s.last⟩ := by
    have := hok; unfold InfP.ok at this; rw [ha] at this; simpa using this
  have hevs := single_evOk _ (hwf.log_sorted r) (fun c hc => (hwf.log_obj r c hc).2) hgood R R0
    hsub σs s.store d a s.fifo s.last hok' hst hfd hreg b
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst Hix] with -
  · inext
    unfold infRes
    iexists σp, s, q, σs, R, [d], false, f
    iframe
    iframe #
    ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩
  imodintro
  iunfold procPopped
  iframe
  unfold evsOk
  imodintro
  iintro %e %he
  iapply (evFacts_of_evOk γa r γi σp R hres e (hevs e he))
  unfold regFacts
  iframe #

/-- **A popped batch's events' facts, through the invariant**: see the file header. -/
theorem infInv_batchEvs (γa : ApiNames) (r : Res) (γf : FifoNames) (γt : TsNames)
    (γi : InfNames) (R0 : Reg) (ds : List cache.FD) (b : Bool) (σ : cache.St)
    (hobj : ∀ d ∈ ds, ∃ t x, d = .obj t x) (hreg : ∀ x ∈ fdObjs ds, ∃ o, R0 !! x = some o) :
    ⊢ infInv γa r γf γt γi -∗ ([∗map] x ↦ o ∈ R0, x ↪[γi.reg]□ o) -∗
      ghostVar γi.sw (1 : Qp).half σ -∗ procPopped γi ds b ={⊤}=∗
      ghostVar γi.sw (1 : Qp).half σ ∗ procPopped γi ds b ∗
      batchEvsOk (evFacts γa r γi) (regKF R0) b σ ds := by
  iintro #Hinv #Hsnap Hsw' Hpop'
  iunfold infInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold infRes at Hi
  icases Hi with ⟨%σp, %s, %q, %σs, %R, %pd, %ap, %f, #Hp, Hreg, #Hsnap', #Hobjs, Hq, Hst, Hsw,
    Hlast, Hpop, Hlb, Hfst, Hix, %Hok⟩
  iunfold procPopped at Hpop'
  icombine Hsw Hsw' gives % ⟨_, hσ⟩
  subst hσ
  icombine Hpop Hpop' gives % ⟨_, hpd⟩
  simp only [Prod.mk.injEq] at hpd
  obtain ⟨rfl, rfl⟩ := hpd
  ihave ⟨%hsub, Hreg, -⟩ := reg_sub γi.reg R R0 $$ [$Hreg $Hsnap]
  ihave #Hp2 := Hp
  iunfold pastSt at Hp2
  icases Hp2 with ⟨%Hh, -, %hH⟩
  have hwf := hH.2.1
  obtain ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩ := Hok
  have hpop' := hpop
  unfold poppedRel at hpop'
  simp only [Bool.false_eq_true, ↓reduceIte] at hpop'
  have hevs := batch_evOk _ (hwf.log_sorted r) (fun c hc => (hwf.log_obj r c hc).2) hgood R R0
    hsub b pd s.popped σs s.store s.fifo s.last hok hst hpop' hobj hreg
  imod Hclose $$ [Hreg Hq Hst Hsw Hlast Hpop Hlb Hfst Hix] with -
  · inext
    unfold infRes
    iexists σp, s, q, σs, R, pd, false, f
    iframe
    iframe #
    ipureintro; exact ⟨hok, hlast, hfifo, hpop, hst, hres, hgood, hfq, hpr, hsy⟩
  imodintro
  iunfold procPopped
  iframe
  unfold batchEvsOk
  imodintro
  iapply (evFacts_list γa r γi σp R hres _ hevs)
  imodintro
  unfold regFacts
  iframe #

end iris

end informer
end EtcdGrove
end Perennial
