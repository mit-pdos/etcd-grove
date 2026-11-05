/-
Lean-first (no Rocq counterpart).

# k8setcd3: the driver's updates (stage 6f)

The updates `Apply` hands the store (`Proof/k8s_io/apiserver/pkg/storage/etcd3/Updates.lean`), at
the instance's invariant (`Inv.lean`), and the commits it makes itself, as linkvtxn's:

- `create_au`: a `Create` whose prophecy says the call answers (not `EOther`): the store's
  one-shot update (`k8sAu1`) commits `lintest`'s update at its firing with the store's model's
  output there (`kStep`);
- `rw_au`: a `Delete` or `GuaranteedUpdate` so prophesied: the store's persistent update
  (`k8sAuRW`) whose token is `rwCall`'s; where the store hands it (its linearization point: the
  write, or a read where the model's step is the identity), `lintest`'s update commits with the
  model's output there; a plain read changes nothing;
- `write_err_commit`, `pend_au1`, `pend_rw`: a write whose prophecy says `EOther` commits at once
  as pending, its token the store's (`k8sAu1`'s frame, `k8sAuRW`'s `W`); where the store's update
  fires as the write, the pending write takes effect (`kOk_pend`);
- `read_err_commit`, `plain_read_au`: a `Get` so prophesied commits at once; its reads only see
  the store's states;
- `get_read_au`, `getCall_take`: a `Get` whose prophecy says it answers: the read update for the
  revision `R` the client prophesies commits at its first firing at a state of revision `R`
  (`getCall`), every later one at `R` seeing the same state (the revisions' map); `Apply` takes
  the continuation after the reply.

At a write's firing the invariant's state moves along `KvNext` (`Updates.lean`): the revisions'
map and the store's history follow (`revOwn_next`, `histAuth_next`). That etcd's revision still
has room for two more after a write (`revRoom`) is a marked `sorry` (D30n): the driver cannot
count the writes to come.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Inv

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **etcd's revisions do not run out** (D30n; see the file header): a marked `sorry` until the
driver bounds its writes. -/
theorem revRoom (σ σ' : KVState) (_h : σ'.rev = σ.rev + 1) : σ'.rev + 2 < 2 ^ 63 := by
  sorry

/-- The model's step of a boxed input and output is the pending model's of the input and the
output's answer. -/
theorem step_box (g0 : GSt) (S : linkv.PSet GSt Input) (x : Input) (y : Output) :
    (k8setcd3S (GF := GF) g0).M.step S (boxIn x, boxOut y) =
      (linkv.pSeq (kSpec g0)).step S (x, ansOf y) :=
  linkv.pM_step _ _ _ _ _ _ (decOp_box (sem := sem) (package_sem := package_sem) x y)

theorem run_snoc (g0 : GSt) (h : List OpV) (S S' : linkv.PSet GSt Input) (a : OpV)
    (h1 : run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) h = some S)
    (h2 : (k8setcd3S (GF := GF) g0).M.step S a = some S') :
    run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) (h ++ [a]) = some S' := by
  suffices H : ∀ (s0 : linkv.PSet GSt Input) (l : List OpV),
      run (k8setcd3S (GF := GF) g0).M s0 (l ++ [a]) =
        (run (k8setcd3S (GF := GF) g0).M s0 l).bind ((k8setcd3S (GF := GF) g0).M.step · a) by
    rw [H, h1]; exact h2
  intro s0 l
  induction l generalizing s0 with
  | nil =>
    simp only [List.nil_append, run, Option.bind_some]
    cases (k8setcd3S (GF := GF) g0).M.step s0 a <;> rfl
  | cons b l ih =>
    simp only [List.cons_append, run]
    cases (k8setcd3S (GF := GF) g0).M.step s0 b with
    | none => rfl
    | some s1 => exact ih s1

/-- The store's model's answer on an input, at the instance's state: an answer (never
`EOther`). -/
theorem kStep_ans {c : StoreCfg GF DObj} {g0 : GSt} {S : linkv.PSet GSt Input} {σ : KVState}
    {M : GMap Nat Input} {nx : Nat} (H : KOk c g0 S σ M nx) (eD eU : GoInterface) (x : Input)
    (hx : InOk x)
    (hk : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2 ∨ uint.nat (minOf x) ≤ σ.rev) :
    ansOf (kStep eD eU x (c.abs σ)).2 = .ok (kStep eD eU x (c.abs σ)).2 := by
  obtain ⟨cf, -, hrel, -⟩ := H.cfg
  have hrv : (c.abs σ).rv + 1 < 2 ^ 64 := by rw [abs_rv]; have := H.room; omega
  rw [(refine_step eD eU _ _ hrel x hx hrv).2]
  rcases hk with h | h | h | hmin
  · exact ansOf_mstepL x cf.st (Or.inl h)
  · exact ansOf_mstepL x cf.st (Or.inr (Or.inl h))
  · exact ansOf_mstepL x cf.st (Or.inr (Or.inr h))
  -- a `Get` whose minimum resource version the state has reached: not the too-large `EOther`
  by_cases hk3 : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2
  · exact ansOf_mstepL x cf.st hk3
  rw [← (refine_step eD eU _ _ hrel x hx hrv).2]
  have h0 : ¬ x.Kind' = W64 0 := fun h => hk3 (Or.inl h)
  have h1 : ¬ x.Kind' = W64 1 := fun h => hk3 (Or.inr (Or.inl h))
  have h2 : ¬ x.Kind' = W64 2 := fun h => hk3 (Or.inr (Or.inr h))
  unfold ansOf
  rw [if_neg]
  simp only [kStep, h0, h1, h2, ↓reduceIte, KSt.get]
  rw [if_neg (by rw [abs_rv]; omega)]
  repeat' split
  all_goals simp [outOf, objOutL, zeroOutL]

/-- The revisions' map, after a step: the next revision's state added, if it moved. -/
theorem revOwn_next (γ : KNames) (σ σ' : KVState) (hn : σ' = σ ∨ σ'.rev = σ.rev + 1) :
    revOwn (GF := GF) γ σ ⊢ |==> revOwn γ σ' := by
  iintro H
  rcases hn with he | hr
  · rw [he]; imodintro; iexact H
  iunfold revOwn at H
  icases H with ⟨%Mr, HA, -, %Hok⟩
  have hfresh : Mr !! (σ.rev + 1) = none := Hok.2 _ (by omega)
  imod ghost_map_insert_persist (σ.rev + 1) σ' hfresh $$ HA with ⟨HA, #He⟩
  imodintro
  iunfold revOwn
  iexists _
  rw [hr]
  iframe He HA
  ipureintro
  refine ⟨?_, fun n hn => ?_⟩
  · rw [hr]; exact GMap.lookup_insert _ _ _
  · rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact Hok.2 n (by omega)

/-- The current revision's state, read-only. -/
theorem revOwn_elem (γ : KNames) (σ : KVState) :
    revOwn (GF := GF) γ σ ⊢ revOwn γ σ ∗ ghostMapElem γ.r σ.rev DFrac.discard σ := by
  iintro H
  iunfold revOwn at H
  icases H with ⟨%Mr, HA, #He, %Hok⟩
  iframe He
  iunfold revOwn
  iexists Mr
  iframe He HA
  ipureintro; exact Hok

/-- The state, seen in the history. -/
theorem histOwn_seen (c : StoreCfg GF DObj) (σ : KVState) :
    histOwn (GF := GF) c σ ⊢ histOwn c σ ∗ kvSeen c.γh σ := by
  iintro H
  iunfold histOwn at H
  icases H with ⟨Hh, #Ho⟩
  ihave ⟨Hh, #Hs⟩ := histAuth_seen c.γh σ $$ Hh
  iframe Hs
  iunfold histOwn
  iframe Hh Ho

/-- **The history follows a step of etcd's state**, a step that changes the store's items at one
key at most: the revisions so far still change one key under the prefix each; the step's entry
comes back (`revSeen`). -/
theorem histOwn_next (c : StoreCfg GF DObj) (σ σ' : KVState) (hn : KvNext σ σ')
    (hw : kvWf c σ) (hw' : kvWf c σ') (hr' : σ'.rev + 2 < 2 ^ 63)
    (hK : ∃ K, ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k) :
    histOwn (GF := GF) c σ ⊢ |==> (histOwn c σ' ∗ revSeen c.γh σ σ') := by
  iintro H
  iunfold histOwn at H
  icases H with ⟨Hh, #Ho⟩
  imod (histAuth_next c.γh σ σ' hn (by omega) hw.1 hw'.1) $$ Hh with ⟨Hh, #Hs⟩
  imodintro
  iframe Hs
  iunfold histOwn
  iframe Hh
  rcases hn with he | ⟨hrv, hnew⟩
  · subst he
    iexact Ho
  obtain ⟨K, hK⟩ := hK
  have h1 := chgOf_pfx_one σ σ' (Or.inr ⟨hrv, hnew⟩) hrv hw hw' K hK
  iunfold oneKeyRevs
  imodintro
  iintro %r %hr
  by_cases hlast : r = σ'.rev
  · subst hlast
    iunfold revSeen at Hs
    ihave He := Hs $$ %hrv
    iexists (chgOf σ σ')
    isplit
    · iexact He
    · ipureintro; exact h1
  · iunfold oneKeyRevs at Ho
    iapply Ho
    ipureintro; omega

/-- **The invariant's ghost state follows a step of etcd's state** (see the file header): the
revisions' map, the store's history (at a step that changes the store's items at one key at
most), and the room for revisions (`revRoom`); the step's entry comes back. -/
theorem inv_next (γ : KNames) (c : StoreCfg GF DObj) (σ σ' : KVState) (hn : KvNext σ σ')
    (hw : kvWf c σ) (hw' : kvWf c σ') (hr : σ.rev + 2 < 2 ^ 63)
    (hK : ∃ K, ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k) :
    revOwn (GF := GF) γ σ ∗ histOwn c σ ⊢
      |==> (revOwn γ σ' ∗ histOwn c σ' ∗ ⌜σ'.rev + 2 < 2 ^ 63⌝ ∗ revSeen c.γh σ σ') := by
  have hr' : σ'.rev + 2 < 2 ^ 63 := by
    rcases hn with he | ⟨hrv, -⟩
    · rw [he]; exact hr
    · exact revRoom σ σ' hrv
  have hn' : σ' = σ ∨ σ'.rev = σ.rev + 1 := by
    rcases hn with he | ⟨hrv, -⟩
    · exact Or.inl he
    · exact Or.inr hrv
  iintro ⟨Hrv, Hhist⟩
  ihave Hrv := (revOwn_next γ σ σ' hn') $$ Hrv
  ihave Hhist := (histOwn_next c σ σ' hn hw hw' hr' hK) $$ Hhist
  imod Hrv with Hrv
  imod Hhist with ⟨Hhist, #Hs⟩
  imodintro
  iframe Hrv Hhist Hs
  ipureintro; exact hr'

/-- The model's step on `x` changes the items at its key at most. -/
theorem kStep_oneKey (c : StoreCfg GF DObj) (eD eU : GoInterface) (x : Input) (σ σ' : KVState)
    (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1) :
    ∃ K, ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k :=
  ⟨mkeyL x.Key', fun k hk => by rw [habs]; exact kStep_items eD eU x _ k hk⟩

/-- **`lintest`'s update, committed** at the output `y` (see the file header): the history
grows by the operation, the continuation is left. -/
theorem linU_commit (γ : KNames) (g0 : GSt) (x : Input) (y : Output) (Φ : val → IProp GF)
    (h : List OpV) (S S' : linkv.PSet GSt Input)
    (hr : run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) h = some S)
    (hst : (k8setcd3S (GF := GF) g0).M.step S (boxIn x, boxOut y) = some S') :
    ghostVar γ.h (1 : Qp).half h ∗ linU γ g0 (boxIn x) Φ ⊢
      |={⊤ \ drvE}=> (ghostVar γ.h (1 : Qp).half (h ++ [(boxIn x, boxOut y)]) ∗
        contAt g0 x y Φ) := by
  iintro ⟨Hh, HU⟩
  iunfold linU at HU
  imod HU with ⟨%S0, HS, HU⟩
  iunfold kState at HS
  icases HS with ⟨%h0, Hh0, %Hr0⟩
  ihave %Heq := ghostVar_agree γ.h h (1 : Qp).half h0 (1 : Qp).half $$ Hh Hh0
  subst Heq
  have HS0 : S0 = S := Option.some.inj (Hr0.symm.trans hr)
  subst HS0
  have Hr' := run_snoc g0 h S0 S' _ hr hst
  imod ghostVar_update_halves (h ++ [(boxIn x, boxOut y)]) γ.h h h $$ Hh Hh0 with ⟨Hh, Hh0⟩
  imod HU $$ %S' %(boxOut y) [Hh0] with HΦ
  · isplitl [Hh0]
    · iunfold kState
      iexists _
      iframe Hh0
      ipureintro; exact Hr'
    · ipureintro; exact hst
  imodintro
  iframe Hh HΦ

/-- Two copies of a call's token: impossible. -/
theorem tok_excl (γt : GName) :
    dghostVar (GF := GF) γt (DFrac.own 1) () ∗ dghostVar γt (DFrac.own 1) () ⊢ False := by
  iintro ⟨Htok, Htok'⟩
  ihave %Hbad := dghostVar_valid_2 γt _ _ _ _ $$ Htok Htok'
  exfalso
  have h := DFrac.valid_own_op Hbad.1
  exact absurd h (by decide)

theorem drvE_au : ⊤ \ drvE ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN := fun p hp => by
  have := drvE_mask' p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this
  exact this.1

/-! ### An answer's cached object (`ansOk`) -/

/-- A list of at most one element has one. -/
theorem eq_of_len_le_one {α : Type} {l : List α} (h : l.length ≤ 1) {a b : α} (ha : a ∈ l)
    (hb : b ∈ l) : a = b := by
  match l, h, ha, hb with
  | [x], _, ha, hb =>
    rw [List.mem_singleton] at ha hb
    rw [ha, hb]
  | _ :: _ :: _, h, _, _ => simp at h

/-- **An item of the abstraction** is a key-value's, under the prefix. -/
theorem abs_inv (c : StoreCfg GF DObj) (τ : KVState) (K : GoString) (it : KItem DObj)
    (h : (c.abs τ).items K = some it) :
    c.pfx <+: K ∧ ∃ v, mvcc.findKey K τ.kvs = some v ∧ c.S.dec v.value = some (it.obj, it.canon) ∧
      uint.nat v.modRev = it.rv := by
  unfold StoreCfg.abs absK at h
  simp only at h
  by_cases hp : c.pfx <+: K
  · rw [if_pos hp] at h
    refine ⟨hp, ?_⟩
    cases hf : mvcc.findKey K τ.kvs with
    | none => simp [linkv.absSt, linkv.absM, hf] at h
    | some v =>
      refine ⟨v, rfl, ?_⟩
      simp only [linkv.absSt, linkv.absM, hf, Option.map_some, Option.bind_some, itemOf,
        linkv.absVR] at h
      cases hd : c.S.dec v.value with
      | none => simp [hd] at h
      | some ob =>
        simp only [hd, Option.map_some, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl⟩
  · rw [if_neg hp] at h; cases h

/-- **A revision changing `K`, at most one key under the prefix**: every key under the prefix held
`o` at that revision, if it is `K`'s value there (`hx`), else none did. -/
theorem versionAt_of_chg (c : StoreCfg GF DObj) (r : w64) (hr0 : r ≠ W64 0) (ch : Changes)
    (K : GoString) (xv : Option GoString) (hin : (K, xv) ∈ ch)
    (hone : ((ch.map Prod.fst).filter (fun k => decide (c.pfx <+: k))).length ≤ 1)
    (hpK : c.pfx <+: K) (o : DObj) (hx : ∀ val, xv = some val → ∃ b, c.S.dec val = some (o, b)) :
    ghostMapElem (GF := GF) c.γh r DFrac.discard ch ⊢
      □ ∀ k : GoString, ⌜c.pfx <+: k⌝ → versionAt c k r o := by
  iintro #He
  imodintro
  iintro %k %hk
  iunfold versionAt
  imodintro
  iintro %σ #Hs
  cases hf : mvcc.findKey k σ.kvs with
  | none =>
    ipureintro
    intro hm
    simp [kubernetes.modAt, hf] at hm
    exact absurd hm.symm hr0
  | some v =>
    by_cases hm : v.modRev = r
    · subst hm
      have hvk : v.key = k := by
        have := List.find?_some hf
        simpa using this
      have hmem : v ∈ σ.kvs := List.mem_of_find?_eq_some hf
      iunfold kvSeen at Hs
      icases Hs $$ %v %hmem with ⟨%ch', #E', %hc'⟩
      ihave %he := ghostMapElem_agree $$ E' He
      subst he
      ipureintro
      intro _
      rw [hvk] at hc'
      by_cases hkK : k = K
      · subst hkK
        have hxv := Changes.eq_of_key hc'.2 hin hc'.1
        obtain ⟨b, hb⟩ := hx v.value hxv
        exact ⟨b, c.abs_some σ k hk v hf o b hb⟩
      · exfalso
        apply hkK
        refine eq_of_len_le_one hone ?_ ?_
        · simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
          exact ⟨⟨_, hc'.1, rfl⟩, hk⟩
        · simp only [List.mem_filter, List.mem_map, decide_eq_true_eq]
          exact ⟨⟨_, hin, rfl⟩, hpK⟩
    · ipureintro
      intro h
      simp [kubernetes.modAt, hf] at h
      exact absurd h hm

/-- The history's facts at the state `σ`: seen, its revisions changing one key each. -/
theorem histOwn_one (c : StoreCfg GF DObj) (σ : KVState) :
    histOwn (GF := GF) c σ ⊢ histOwn c σ ∗ oneKeyRevs c σ.rev := by
  iintro H
  iunfold histOwn at H
  icases H with ⟨Hh, #Ho⟩
  iframe Ho
  iunfold histOwn
  iframe Hh Ho

/-- **An item of a state seen is a cached object**: its key-value's revision changed its key only,
under the prefix. -/
theorem cachedObj_of_item (c : StoreCfg GF DObj) (τ : KVState) (hw : kvWf c τ) (K : GoString)
    (o : DObj) (rv : Nat) (b : Bool) (h : (c.abs τ).items K = some ⟨o, rv, b⟩) :
    kvSeen (GF := GF) c.γh τ ∗ oneKeyRevs c τ.rev ⊢
      cachedObjOk c ⟨o.name, o.uid, o.val, W64 (rv : Int)⟩ := by
  obtain ⟨hpK, v, hf, hd, hrv⟩ := abs_inv c τ K _ h
  simp only at hd hrv
  have hmem : v ∈ τ.kvs := List.mem_of_find?_eq_some hf
  have hvk : v.key = K := by
    have := List.find?_some hf
    simpa using this
  have hb := hw.2.2.1 K (linkv.absVR v) (by simp [linkv.absSt, linkv.absM, hf])
  simp only [linkv.absVR, linkv.absSt] at hb
  have hW : W64 ((rv : Nat) : Int) = v.modRev := by rw [← hrv]; exact W64_uint_nat _
  have hr0 : v.modRev ≠ W64 0 := by
    intro e; rw [e] at hb; simp at hb
  iintro ⟨#Hs, #Ho⟩
  iunfold kvSeen at Hs
  icases Hs $$ %v %hmem with ⟨%ch, #E, %hc⟩
  iunfold oneKeyRevs at Ho
  icases Ho $$ %(uint.nat v.modRev) %(by omega) with ⟨%ch2, #E2, %hl⟩
  rw [W64_uint_nat] at *
  ihave %he := ghostMapElem_agree $$ E E2
  subst he
  rw [hvk] at hc
  ihave #Hv := versionAt_of_chg c v.modRev hr0 ch K (some v.value) hc.1 hl hpK o
    (fun val e => ⟨b, by cases e; exact hd⟩) $$ E
  unfold cachedObjOk
  rw [hW]
  isplitr
  · ipureintro
    refine ⟨o.2.1, o.2.2, hr0⟩
  rw [dobjOf_mk]
  iexact Hv

/-- **A deleted key's answer is a cached object**, vacuously: its revision wrote nothing under
the prefix (it deleted the key). -/
theorem cachedObj_of_del (c : StoreCfg GF DObj) (σ σ' : KVState) (hw' : kvWf c σ')
    (hrv : σ'.rev = σ.rev + 1) (K : GoString) (hpK : c.pfx <+: K)
    (hin : (K, (none : Option GoString)) ∈ chgOf σ σ') (o : DObj) :
    revSeen (GF := GF) c.γh σ σ' ∗ oneKeyRevs c σ'.rev ⊢
      cachedObjOk c ⟨o.name, o.uid, o.val, W64 ((σ'.rev : Nat) : Int)⟩ := by
  have hR : uint.nat (W64 ((σ'.rev : Nat) : Int)) = σ'.rev := by
    have := hw'.2.2.2
    simp only [linkv.absSt] at this
    simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
  have hr0 : W64 ((σ'.rev : Nat) : Int) ≠ W64 0 := by
    intro e; rw [e] at hR; simp at hR; omega
  iintro ⟨#Hs, #Ho⟩
  iunfold revSeen at Hs
  ihave #E := Hs $$ %hrv
  iunfold oneKeyRevs at Ho
  icases Ho $$ %σ'.rev %(by omega) with ⟨%ch2, #E2, %hl⟩
  ihave %he := ghostMapElem_agree $$ E E2
  subst he
  ihave #Hv := versionAt_of_chg c _ hr0 _ K none hin hl hpK o (fun val e => by cases e) $$ E
  unfold cachedObjOk
  isplitr
  · ipureintro
    exact ⟨o.2.1, o.2.2, hr0⟩
  rw [dobjOf_mk]
  iexact Hv

/-- **An answer at a step's firing is a cached object** (`ansOk`): its item is in the state
before or after the step (`cachedObj_of_item`), or it is a deleted key's (`cachedObj_of_del`). -/
theorem ansOk_step (c : StoreCfg GF DObj) (σ σ' : KVState) (hw : kvWf c σ) (hw' : kvWf c σ')
    (K : GoString) (y : Output) (ha : AnsFrom (c.abs σ) (c.abs σ') K y) :
    kvSeen (GF := GF) c.γh σ ∗ oneKeyRevs c σ.rev ∗ kvSeen c.γh σ' ∗ oneKeyRevs c σ'.rev ∗
      revSeen c.γh σ σ' ⊢ ansOk c y := by
  iintro ⟨#Hs, #Ho, #Hs', #Ho', #Hr⟩
  unfold ansOk
  by_cases he : y.Err' = W64 0 ∧ y.Name' ≠ []
  · rw [if_pos he]
    obtain ⟨o, rv, rfl, hr⟩ := ha he.1 he.2
    have hco : cachedOf (objOutL ⟨o.name, o.uid, o.val, W64 (rv : Int)⟩) =
        ⟨o.name, o.uid, o.val, W64 (rv : Int)⟩ := rfl
    rw [hco]
    rcases hr with ⟨b, hb | hb⟩ | ⟨it, hrv, hit, hnone, hrr⟩
    · iapply cachedObj_of_item c σ hw K o rv b hb
      iframe Hs Ho
    · iapply cachedObj_of_item c σ' hw' K o rv b hb
      iframe Hs' Ho'
    · obtain ⟨hpK, v, hf, -, -⟩ := abs_inv c σ K it hit
      have hrv' : σ'.rev = σ.rev + 1 := hrr
      have hf' : mvcc.findKey K σ'.kvs = none := by
        cases h' : mvcc.findKey K σ'.kvs with
        | none => rfl
        | some v' =>
          obtain ⟨o', b', hd'⟩ := c.dec_of_wf σ' hw' K hpK v' h'
          rw [c.abs_some σ' K hpK v' h' o' b' hd'] at hnone
          cases hnone
      have hdel : (K, (none : Option GoString)) ∈ chgOf σ σ' := by
        refine chgOf_del σ σ' K ⟨v, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩ ?_
        intro w hw hk
        have := List.find?_eq_none.1 hf' w hw
        simp [hk] at this
      have hrv2 : rv = σ'.rev := by rw [hrv, hrv']; rfl
      subst hrv2
      iapply cachedObj_of_del c σ σ' hw' hrv' K hpK hdel o
      iframe Hr Ho'
  · rw [if_neg he]
    itrivial

/-- **A read's answer is a cached object** (`ansOk`), its item in the state read. -/
theorem ansOk_read (c : StoreCfg GF DObj) (σ : KVState) (hw : kvWf c σ) (K : GoString)
    (y : Output) (ha : AnsFrom (c.abs σ) (c.abs σ) K y) :
    kvSeen (GF := GF) c.γh σ ∗ oneKeyRevs c σ.rev ⊢ ansOk c y := by
  iintro ⟨#Hs, #Ho⟩
  ihave #Hr : revSeen (GF := GF) c.γh σ σ $$ []
  · iunfold revSeen
    imodintro
    iintro %h
    exfalso; omega
  iapply ansOk_step c σ σ hw hw K y ha
  iframe Hs Ho Hr

/-- **A `Create` whose prophecy says it answers** (see the file header). -/
theorem create_au (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames)
    (eD eU : GoInterface) (x : Input) (hx : InOk x) (hk : x.Kind' = W64 0)
    (Φ : val → IProp GF) :
    kInv γ c g0 γk ∗ linU γ g0 (boxIn x) Φ ⊢
      k8sAu1 γk c (fun s => (s.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).1)
        (fun σ => iprop(contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∗
          ansOk c (kStep eD eU x (c.abs σ)).2)) := by
  have Hm := drvInvN_mask'
  have HE := drvE_au
  iintro ⟨#Hinv, HU⟩
  unfold k8sAu1
  iunfold kInv at Hinv
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hhist, #Hseen⟩ := histOwn_seen c σ $$ Hhist
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  isplitl [Hσ]
  · iframe Hσ Hseen
    ipureintro; exact ⟨Hok.wf, Hok.room⟩
  isplit
  · -- abort: nothing moved
    iintro ⟨Hσ, -, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact HU
  · -- the write's firing: `lintest`'s update commits with the model's output
    iintro %σ' ⟨Hσ, %Hpost⟩
    obtain ⟨hw', habs, hn⟩ := Hpost
    imod Hclose2 with -
    have habs' : c.abs σ' = (kStep eD eU x (c.abs σ)).1 := by rw [habs]; simp [kStep, hk]
    ihave ⟨Hhist, #Hone⟩ := histOwn_one c σ $$ Hhist
    imod (inv_next γ c σ σ' hn Hok.wf hw' Hok.room (kStep_oneKey c eD eU x σ σ' habs')) $$ [Hrv Hhist]
      with ⟨Hrv, Hhist, %hr', #Hrs⟩
    · iframe
    obtain ⟨S', HS', Hok'⟩ := kOk_ok Hok eD eU x hx habs' hw' hr'
    ihave ⟨Hhist, #Hseen'⟩ := histOwn_seen c σ' $$ Hhist
    ihave ⟨Hhist, #Hone'⟩ := histOwn_one c σ' $$ Hhist
    ihave #Hans := ansOk_step c σ σ' Hok.wf hw' (mkeyL x.Key') (kStep eD eU x (c.abs σ)).2
      (by rw [habs']; exact kStep_ansFrom eD eU x (c.abs σ)) $$ []
    · iframe Hseen Hone Hseen' Hone' Hrs
    have Hst : (k8setcd3S (GF := GF) g0).M.step S (boxIn x, boxOut (kStep eD eU x (c.abs σ)).2) =
        some S' := by
      rw [step_box, kStep_ans Hok eD eU x hx (Or.inl hk)]; exact HS'
    imod (fupd_mask_subseteq HE) with Hclose3
    imod (linU_commit γ g0 x _ Φ h S S' Hr Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
    · iframe
    imod Hclose3 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists _, S', σ', M, nx
      iframe
      ipureintro; exact ⟨run_snoc g0 h S S' _ Hr Hst, Hok'⟩
    imodintro
    iframe HΦ Hans

/-- **A `Delete` or `GuaranteedUpdate` whose prophecy says it answers** (see the file header):
the store's step is the model's on the input (`hstep`). -/
theorem rw_au (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames)
    (eD eU : GoInterface) (x : Input) (hx : InOk x) (hk : x.Kind' = W64 1 ∨ x.Kind' = W64 2)
    (step : KSt DObj → KSt DObj)
    (hstep : ∀ ks, step ks = (kStep eD eU x ks).1) (γt : GName) (Φ : val → IProp GF) :
    kInv γ c g0 γk ∗ rwCall γ g0 γt x Φ ⊢
      k8sAuRW γk c step (dghostVar γt (DFrac.own 1) ())
        (fun σ => iprop(contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∗
          ansOk c (kStep eD eU x (c.abs σ)).2)) := by
  have Hm := drvInvN_mask
  have Hcm := callN_mask
  have HE := drvE_mask
  iintro ⟨#Hinv, #Hc⟩
  unfold k8sAuRW
  iunfold kInv at Hinv
  imodintro
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hhist, #Hseen⟩ := histOwn_seen c σ $$ Hhist
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ rwMask \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  isplitl [Hσ]
  · iframe Hσ Hseen
    ipureintro; exact ⟨Hok.wf, Hok.room⟩
  isplit
  · -- abort: nothing moved
    iintro ⟨Hσ, -, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iempintro
  · iintro %b %σ' ⟨Hσ, Hb⟩
    cases b
    · -- a plain read: nothing moved
      isimp only [Bool.false_eq_true, ↓reduceIte] at Hb
      icases Hb with %Hb
      subst Hb
      imod Hclose2 with -
      imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
      · inext
        iunfold kInvBody
        iexists h, S, σ', M, nx
        iframe
        ipureintro; exact ⟨Hr, Hok⟩
      imodintro
      simp only [Bool.false_eq_true, ↓reduceIte]
      iempintro
    · -- the linearization point: `lintest`'s update commits with the model's output
      isimp only [↓reduceIte] at Hb
      icases Hb with ⟨Htok, %Hpost⟩
      obtain ⟨hw', habs, hn⟩ := Hpost
      imod Hclose2 with -
      have habs' : c.abs σ' = (kStep eD eU x (c.abs σ)).1 := by rw [habs, hstep]
      ihave ⟨Hhist, #Hone⟩ := histOwn_one c σ $$ Hhist
      imod (inv_next γ c σ σ' hn Hok.wf hw' Hok.room (kStep_oneKey c eD eU x σ σ' habs')) $$ [Hrv Hhist]
        with ⟨Hrv, Hhist, %hr', #Hrs⟩
      · iframe
      obtain ⟨S', HS', Hok'⟩ := kOk_ok Hok eD eU x hx habs' hw' hr'
      ihave ⟨Hhist, #Hseen'⟩ := histOwn_seen c σ' $$ Hhist
      ihave ⟨Hhist, #Hone'⟩ := histOwn_one c σ' $$ Hhist
      ihave #Hans := ansOk_step c σ σ' Hok.wf hw' (mkeyL x.Key') (kStep eD eU x (c.abs σ)).2
        (by rw [habs']; exact kStep_ansFrom eD eU x (c.abs σ)) $$ []
      · iframe Hseen Hone Hseen' Hone' Hrs
      have Hst : (k8setcd3S (GF := GF) g0).M.step S
          (boxIn x, boxOut (kStep eD eU x (c.abs σ)).2) = some S' := by
        rw [step_box, kStep_ans Hok eD eU x hx (hk.elim (fun h => Or.inr (Or.inl h))
          (fun h => Or.inr (Or.inr (Or.inl h))))]; exact HS'
      unfold rwCall
      iinv Hc with Hci Hclosec
      icases Hci with (⟨HU, >Hlc⟩ | >Htok')
      · imod lc_fupd_elim_later $$ Hlc HU with HU
        imod (fupd_mask_subseteq HE) with Hclose3
        imod (linU_commit γ g0 x _ Φ h S S' Hr Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
        · iframe
        imod Hclose3 with -
        imod Hclosec $$ [Htok] with -
        · inext
          iright
          iexact Htok
        imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
        · inext
          iunfold kInvBody
          iexists _, S', σ', M, nx
          iframe
          ipureintro; exact ⟨run_snoc g0 h S S' _ Hr Hst, Hok'⟩
        imodintro
        simp only [↓reduceIte]
        iframe HΦ Hans
      · iexfalso
        iapply tok_excl γt
        iframe Htok Htok'

/-- **A write whose prophecy says `EOther`, its pending effect** (`Create`; see the file header):
at the store's firing the pending write `n ↦ x` takes effect, its token consumed. -/
theorem pend_au1 (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames)
    (eD eU : GoInterface) (n : Nat) (x : Input) (hk : x.Kind' = W64 0) :
    kInv γ c g0 γk ∗ pendTok γ n x ⊢
      k8sAu1 γk c (fun s => (s.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).1)
        (fun _ => iprop(True)) := by
  have Hm := drvInvN_mask'
  iintro ⟨#Hinv, Htok⟩
  unfold k8sAu1
  iunfold kInv at Hinv
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hhist, #Hseen⟩ := histOwn_seen c σ $$ Hhist
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  isplitl [Hσ]
  · iframe Hσ Hseen
    ipureintro; exact ⟨Hok.wf, Hok.room⟩
  isplit
  · iintro ⟨Hσ, -, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact Htok
  · iintro %σ' ⟨Hσ, %Hpost⟩
    obtain ⟨hw', habs, hn⟩ := Hpost
    imod Hclose2 with -
    have habs' : c.abs σ' = (kStep eD eU x (c.abs σ)).1 := by rw [habs]; simp [kStep, hk]
    imod (inv_next γ c σ σ' hn Hok.wf hw' Hok.room (kStep_oneKey c eD eU x σ σ' habs')) $$ [Hrv Hhist]
      with ⟨Hrv, Hhist, %hr', #Hrs⟩
    · iframe
    iunfold pendTok at Htok
    ihave %Hn := ghost_map_lookup $$ HM Htok
    imod ghost_map_delete $$ HM Htok with HM
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ', _, nx
      iframe
      ipureintro; exact ⟨Hr, kOk_pend Hok eD eU n x Hn habs' hw' hr'⟩
    imodintro
    itrivial

/-- **A write whose prophecy says `EOther`, its pending effect** (`Delete`, `GuaranteedUpdate`):
where the store hands the token, the pending write `n ↦ x` takes effect. -/
theorem pend_rw (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames)
    (eD eU : GoInterface) (n : Nat) (x : Input) (step : KSt DObj → KSt DObj)
    (hstep : ∀ ks, step ks = (kStep eD eU x ks).1) :
    kInv γ c g0 γk ⊢ k8sAuRW γk c step (pendTok γ n x) (fun _ => iprop(True)) := by
  have Hm := drvInvN_mask
  iintro #Hinv
  unfold k8sAuRW
  iunfold kInv at Hinv
  imodintro
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hhist, #Hseen⟩ := histOwn_seen c σ $$ Hhist
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ rwMask \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  isplitl [Hσ]
  · iframe Hσ Hseen
    ipureintro; exact ⟨Hok.wf, Hok.room⟩
  isplit
  · iintro ⟨Hσ, -, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iempintro
  · iintro %b %σ' ⟨Hσ, Hb⟩
    cases b
    · isimp only [Bool.false_eq_true, ↓reduceIte] at Hb
      icases Hb with %Hb
      subst Hb
      imod Hclose2 with -
      imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
      · inext
        iunfold kInvBody
        iexists h, S, σ', M, nx
        iframe
        ipureintro; exact ⟨Hr, Hok⟩
      imodintro
      simp only [Bool.false_eq_true, ↓reduceIte]
      iempintro
    · isimp only [↓reduceIte] at Hb
      icases Hb with ⟨Htok, %Hpost⟩
      obtain ⟨hw', habs, hn⟩ := Hpost
      imod Hclose2 with -
      have habs' : c.abs σ' = (kStep eD eU x (c.abs σ)).1 := by rw [habs, hstep]
      imod (inv_next γ c σ σ' hn Hok.wf hw' Hok.room (kStep_oneKey c eD eU x σ σ' habs')) $$ [Hrv Hhist]
        with ⟨Hrv, Hhist, %hr', #Hrs⟩
      · iframe
      iunfold pendTok at Htok
      ihave %Hn := ghost_map_lookup $$ HM Htok
      imod ghost_map_delete $$ HM Htok with HM
      imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
      · inext
        iunfold kInvBody
        iexists h, S, σ', _, nx
        iframe
        ipureintro; exact ⟨Hr, kOk_pend Hok eD eU n x Hn habs' hw' hr'⟩
      imodintro
      simp only [↓reduceIte]
      itrivial

/-- `call`'s output of an error it cannot place (`Output{Err: EOther}`). -/
def errOutL : Output := ⟨W64 4, [], 0, [], [], [], 0⟩

theorem ansOf_errOutL : ansOf errOutL = .err := by
  simp [ansOf, errOutL]

/-- **A `Get`'s `EOther`** is the model's "too large" answer, `errOutL`. -/
theorem kStep_err4 (eD eU : GoInterface) (x : Input) (ks : KSt DObj) (hk : x.Kind' = W64 3)
    (h : (kStep eD eU x ks).2.Err' = W64 4) : (kStep eD eU x ks).2 = errOutL := by
  have h0 : ¬ x.Kind' = W64 0 := by rw [hk]; decide
  have h1 : ¬ x.Kind' = W64 1 := by rw [hk]; decide
  have h2 : ¬ x.Kind' = W64 2 := by rw [hk]; decide
  simp only [kStep, h0, h1, h2, ↓reduceIte, KSt.get] at h ⊢
  revert h
  repeat' split
  all_goals simp [outOf, objOutL, zeroOutL, otherL, errOutL]

/-- **A write whose prophecy says `EOther`** (see the file header): `lintest`'s update commits
at once, the write pending (`kOk_errW`), with the pending write's token. -/
theorem write_err_commit (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames)
    (x : Input) (hx : InOk x) (hw : isWriteL x = true) (Φ : val → IProp GF) :
    kInv γ c g0 γk ∗ linU γ g0 (boxIn x) Φ ⊢
      |={⊤}=> ∃ n : Nat, contAt g0 x errOutL Φ ∗ pendTok γ n x := by
  have HE := drvE_mask_top
  iintro ⟨#Hinv, HU⟩
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  obtain ⟨S', HS', Hok'⟩ := kOk_errW Hok x hw hx
  have Hst : (k8setcd3S (GF := GF) g0).M.step S (boxIn x, boxOut errOutL) = some S' := by
    rw [step_box, ansOf_errOutL]; exact HS'
  imod (fupd_mask_subseteq HE) with Hclose3
  imod (linU_commit γ g0 x _ Φ h S S' Hr Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
  · iframe
  imod Hclose3 with -
  imod ghost_map_insert nx x (Hok.fresh nx (Nat.le_refl _)) $$ HM with ⟨HM, Htok⟩
  imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
  · inext
    iunfold kInvBody
    iexists _, S', σ, _, nx + 1
    iframe
    ipureintro; exact ⟨run_snoc g0 h S S' _ Hr Hst, Hok'⟩
  imodintro
  iexists nx
  iframe HΦ
  iunfold pendTok
  iexact Htok

/-- **A `Get` whose prophecy says `EOther`**: `lintest`'s update commits at once (`kOk_errR`). -/
theorem read_err_commit (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames)
    (x : Input) (hw : isWriteL x = false) (Φ : val → IProp GF) :
    kInv γ c g0 γk ∗ linU γ g0 (boxIn x) Φ ⊢ |={⊤}=> contAt g0 x errOutL Φ := by
  have HE := drvE_mask_top
  iintro ⟨#Hinv, HU⟩
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  obtain ⟨S', HS', Hok'⟩ := kOk_errR Hok x hw
  have Hst : (k8setcd3S (GF := GF) g0).M.step S (boxIn x, boxOut errOutL) = some S' := by
    rw [step_box, ansOf_errOutL]; exact HS'
  imod (fupd_mask_subseteq HE) with Hclose3
  imod (linU_commit γ g0 x _ Φ h S S' Hr Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
  · iframe
  imod Hclose3 with -
  imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
  · inext
    iunfold kInvBody
    iexists _, S', σ, M, nx
    iframe
    ipureintro; exact ⟨run_snoc g0 h S S' _ Hr Hst, Hok'⟩
  imodintro
  iexact HΦ

/-- A `Get` leaves the store's model as it is. -/
theorem kStep_get (eD eU : GoInterface) (x : Input) (hk : x.Kind' = W64 3) (ks : KSt DObj) :
    (kStep eD eU x ks).1 = ks := by
  simp [kStep, hk]

/-- What a plain read learns: the state is the store's, with room. -/
abbrev plainQ (c : StoreCfg GF DObj) : KVState → IProp GF :=
  fun σ => iprop(⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝)

/-- **A read of the store's states** (a `Get` whose prophecy says `EOther`). -/
theorem plain_read_au (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames) :
    kInv γ c g0 γk ⊢ kvReadAu γk (plainQ c) := by
  have Hm := drvInvN_mask'
  iintro #Hinv
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    imodintro
    ipureintro; exact ⟨Hok.wf, Hok.room⟩

/-- **A `Get`'s read update for the prophesied revision `R`** (see the file header): at its
first firing at a state of revision `R`, `lintest`'s update commits with the model's output
there and the commit bit records the state; a later firing at revision `R` sees the same state
(the revisions' map). -/
theorem get_read_au (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames)
    (eD eU : GoInterface) (γc γt γp : GName) (x : Input) (hx : InOk x) (hk : x.Kind' = W64 3)
    (R : w64) (Φ : val → IProp GF) :
    kInv γ c g0 γk ∗ getCall γ c g0 eD eU γc γt γp x Φ ∗ dghostVar γp DFrac.discard (some R) ⊢
      kvReadAu γk (readQ c γc (uint.nat (minOf x)) R) := by
  have Hm := drvInvN_mask'
  have Hcm := callN_mask'
  have HE := drvE_mask'
  iintro ⟨#Hinv, #Hc, #Hp⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold kInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold kInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, Hhist, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hrv, #Hel⟩ := revOwn_elem γ σ $$ Hrv
  ihave ⟨Hhist, #Hseen⟩ := histOwn_seen c σ $$ Hhist
  ihave ⟨Hhist, #Hone⟩ := histOwn_one c σ $$ Hhist
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
    · inext
      iunfold kInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    by_cases Hrev2 : σ.rev = uint.nat R ∧ uint.nat (minOf x) ≤ σ.rev
    · have Hrev := Hrev2.1
      unfold getCall
      iinv Hc with Hci Hclosec
      icases Hci with (⟨HU, >Hlc, >Hγc⟩ | ⟨%σ0, %R0, >#Hv, >#Hp0, >%Hrev0, >#HL, Hrest⟩)
      · -- the first firing at revision `R`: commit
        imod lc_fupd_elim_later $$ Hlc HU with HU
        have habs' : c.abs σ = (kStep eD eU x (c.abs σ)).1 := (kStep_get eD eU x hk _).symm
        obtain ⟨S', HS', Hok'⟩ := kOk_ok Hok eD eU x hx habs' Hok.wf Hok.room
        have Hst : (k8setcd3S (GF := GF) g0).M.step S
            (boxIn x, boxOut (kStep eD eU x (c.abs σ)).2) = some S' := by
          rw [step_box, kStep_ans Hok eD eU x hx (Or.inr (Or.inr (Or.inr Hrev2.2)))]; exact HS'
        imod (fupd_mask_subseteq HE) with Hclose3
        imod (linU_commit γ g0 x _ Φ h S S' Hr Hst) $$ [Hh HU] with ⟨Hh, HΦ⟩
        · iframe
        imod Hclose3 with -
        imod dghostVar_update (some σ) γc none $$ Hγc with Hγc
        imod dghostVar_persist γc 1 _ $$ Hγc with #Hγc
        imod Hclosec $$ [HΦ] with -
        · inext
          iright
          iexists σ, R
          iframe Hγc Hp Hel
          isplitr
          · ipureintro; exact Hrev
          ileft
          iframe HΦ
          iapply ansOk_read c σ Hok.wf (mkeyL x.Key') _
            (by have := kStep_ansFrom eD eU x (c.abs σ); rwa [kStep_get eD eU x hk] at this)
          iframe Hseen Hone
        imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
        · inext
          iunfold kInvBody
          iexists _, S', σ, M, nx
          iframe
          ipureintro; exact ⟨run_snoc g0 h S S' _ Hr Hst, Hok'⟩
        imodintro
        imodintro
        unfold readQ
        isplitr
        · ipureintro; exact ⟨Hok.wf, Hok.room⟩
        iintro %_
        iexact Hγc
      · -- a later firing at revision `R`: the same state, nothing to do
        ihave %HpR := dghostVar_agree γp _ _ _ _ $$ Hp Hp0
        simp only [Option.some.injEq] at HpR
        subst HpR
        ihave %HLe := ghostMapElem_agree σ.rev γ.r _ _ _ _ $$ [HL] Hel
        · rw [Hrev, ← Hrev0]; iexact HL
        subst HLe
        imod Hclosec $$ [Hrest] with -
        · inext
          iright
          iexists σ0, R
          iframe Hv Hp0 HL Hrest
          ipureintro; exact Hrev0
        imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
        · inext
          iunfold kInvBody
          iexists h, S, _, M, nx
          iframe
          ipureintro; exact ⟨Hr, Hok⟩
        imodintro
        imodintro
        unfold readQ
        isplitr
        · ipureintro; exact ⟨Hok.wf, Hok.room⟩
        iintro %_
        iexact Hv
    · imod Hclose $$ [Hh Hσ HM Hrv Hhist] with -
      · inext
        iunfold kInvBody
        iexists h, S, σ, M, nx
        iframe
        ipureintro; exact ⟨Hr, Hok⟩
      imodintro
      imodintro
      unfold readQ
      isplitr
      · ipureintro; exact ⟨Hok.wf, Hok.room⟩
      iintro %H
      exact absurd H Hrev2

/-- **The maker `Get` takes** (a `Get` whose prophecy says it answers): for the pair the client
prophesies, the revision recorded (`γp`) and each member's read update for it. -/
theorem get_maker (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (ms : List (client.SrvAt GF))
    (eD eU : GoInterface) (γc γt γp : GName) (x : Input) (hx : InOk x) (hk : x.Kind' = W64 3)
    (Φ : val → IProp GF) :
    □ ([∗list] sv ∈ ms, kInv γ c g0 sv.γr.kv) ∗ getCall γ c g0 eD eU γc γt γp x Φ ∗
      dghostVar γp (DFrac.own 1) (none : Option w64) ⊢
      (iprop(∀ (R m : w64), |==> □ [∧list] sv ∈ ms,
        ⌜(fun σ => readQ c γc (uint.nat (minOf x)) R σ) = fun _ => iprop(True)⌝ ∨
          kvReadAu sv.γr.kv (fun σ => readQ c γc (uint.nat (minOf x)) R σ)) : IProp GF) := by
  iintro ⟨#Hinvs, #Hc, Hp⟩ %R %m
  imod dghostVar_update (some R) γp none $$ Hp with Hp
  imod dghostVar_persist γp 1 _ $$ Hp with #Hp
  imodintro
  imodintro
  refine BigAndL.bigAndL_intro (PROP := IProp GF) fun j sv hj => ?_
  have hsv : sv ∈ ms := List.mem_of_getElem? hj
  iintro ⟨⟨#Hinvs, #Hc⟩, #Hp⟩
  iright
  iapply get_read_au γ c g0 sv.γr.kv eD eU γc γt γp x hx hk R Φ
  iframe Hc Hp
  iapply (BigSepL.bigSepL_mem (Φ := fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv)
    hsv) $$ Hinvs

/-- **The maker of plain reads** (a `Get` whose prophecy says `EOther`). -/
theorem plain_maker (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt)
    (ms : List (client.SrvAt GF)) :
    □ ([∗list] sv ∈ ms, kInv γ c g0 sv.γr.kv) ⊢
      (iprop(∀ (R m : w64), |==> □ [∧list] sv ∈ ms,
        ⌜plainQ c = fun _ => iprop(True)⌝ ∨ kvReadAu sv.γr.kv (plainQ c)) :
        IProp GF) := by
  iintro #Hinvs %R %m
  imodintro
  imodintro
  refine BigAndL.bigAndL_intro (PROP := IProp GF) fun j sv hj => ?_
  have hsv : sv ∈ ms := List.mem_of_getElem? hj
  iintro #Hinvs
  iright
  iapply plain_read_au γ c g0 sv.γr.kv
  iapply (BigSepL.bigSepL_mem (Φ := fun sv : client.SrvAt GF => kInv γ c g0 sv.γr.kv)
    hsv) $$ Hinvs

/-- **`Apply` takes the continuation** after the reply: the commit bit holds `σ`, so the call
invariant is on its committed side, its continuation still there (`Apply` holds the token). -/
theorem getCall_take (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (eD eU : GoInterface)
    (γc γt γp : GName) (x : Input) (Φ : val → IProp GF) (σ : KVState) :
    getCall γ c g0 eD eU γc γt γp x Φ ∗ dghostVar γc DFrac.discard (some σ) ∗
      dghostVar γt (DFrac.own 1) () ∗ £ 1 ⊢
      |={⊤}=> (contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∗ ansOk c (kStep eD eU x (c.abs σ)).2) := by
  iintro ⟨#Hc, #Hv, Htok, Hlc⟩
  unfold getCall
  iinv Hc with Hci Hclosec
  icases Hci with (⟨-, -, >Hγc⟩ | ⟨%σ', %R', >#Hv', >#Hp', >%Hrev', >#HL, Hrest⟩)
  · ihave %Hbad := dghostVar_valid_2 γc _ _ _ _ $$ Hv Hγc
    exfalso
    cases Hbad.2
  · ihave %Hvv := dghostVar_agree γc _ _ _ _ $$ Hv Hv'
    simp only [Option.some.injEq] at Hvv
    subst Hvv
    imod lc_fupd_elim_later $$ Hlc Hrest with Hrest
    icases Hrest with (HΦ | Htok')
    · imod Hclosec $$ [Htok] with -
      · inext
        iright
        iexists σ, R'
        iframe Hv Hp' HL
        isplitr
        · ipureintro; exact Hrev'
        iright
        iexact Htok
      imodintro
      iexact HΦ
    · iexfalso
      iapply tok_excl γt
      iframe Htok Htok'

end proofs

end k8s_etcd3
end EtcdGrove
end Perennial
