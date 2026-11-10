/-
Lean-first (no Rocq counterpart).

# k8setcd3: the library's abstract state over etcd, through the store (stage 6f)

As linkvtxn's `Inv.lean`, for the driver's model `k8setcd3S g0` (`pM (kSpec g0) decOp`) and the
store's specs (`Proof/k8s_io/apiserver/pkg/storage/etcd3/`).

## The pure part

- `kStep eD eU x ks`: the store's model (`KSt`) on the input `x` (its kind: `create` of the
  object `mkObj x`, `delete` with the input's preconditions `preD x` and `validateFor`'s function
  `rejD`, `update` with `ignoreNotFound`, `preD x` and `tryUpdateFor`'s `updD`, or `get` at the
  minimum `minOf x`), its next state and the driver's output of its answer (`outOf`). On related
  states (`KRel`) it is the driver's model's step (`refine_step`, from 6b's `refine_*`).
- `KOk c g0 S σ M nx`: the instance's relation, as linkvtxn's `LinkvOk`: `S` closed under late
  effects, etcd's state the store's (`kvWf`), the pending writes `M`
  (inputs `Gen` may return, `InOk`) keyed below `nx`, and some configuration of `S` whose store
  the store's model of `σ` refines (`KRel (c.abs σ)`) with exactly `M`'s writes pending. (Until
  2026-11-05 also etcd's revision's room, kept across a write by the `sorry` `revRoom`, D30n; since
  H-rr1 the room of a state comes with each firing at it, from the server: `kvRoom`.)
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Refine
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Callbacks
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.History
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps

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

/-! ## The inputs are countable (the pending writes' ghost map) -/

section enc
variable [GooseExts]

/-- An object, injectively. -/
def encObj (o : Obj) :=
  (o.Namespace', o.Name', o.UID', o.Value', o.Node', o.App', o.ResourceVersion', o.Annotated')

/-- An input, injectively (its 32 fields). -/
def encIn (x : Input) :=
  ((x.Kind', x.Key', x.Val', x.Node', x.App', x.HasReject', x.Reject', x.NoOp'),
    (x.IgnoreNotFound', x.UID', x.HasPreUID', x.PreUID', x.HasPreRV', x.PreRV', x.UseCached',
      encObj x.Cached'),
    (x.MinRV', x.ListKey', x.Recursive', x.Match', x.Field', x.SelNS', x.SelName', x.SelNode'),
    (x.SelApp', x.Limit', x.Client', x.WKey', x.SendInit', x.Bookmarks', x.Behavior', x.Skip'))

theorem encObj_inj : Function.Injective encObj := by
  intro a b h
  cases a; cases b
  simp only [encObj, Prod.mk.injEq] at h
  simp only [h]

theorem encIn_inj : Function.Injective encIn := by
  intro a b h
  cases a; cases b
  simp only [encIn, Prod.mk.injEq, encObj_inj.eq_iff] at h
  simp only [h]

instance Input.countable : Pos.Countable Input :=
  .ofInjective (fun i => Pos.Countable.encode (encIn i))
    (fun _ _ h => encIn_inj (Pos.encode_inj h))

end enc

instance KVState.inhabited : Inhabited KVState := ⟨{ compacted := 0, base := ∅, changes := [] }⟩

/-! ## Pure part -/

section pure
variable [GooseExts]

/-- The workload's keys (`workloadKeys`, 7e-0's: two levels, prefix boundaries). -/
abbrev wkKeysL : List GoString :=
  [go!"ns-1/pod-1", go!"ns-1/pod-11", go!"ns-2/pod-2", go!"ns-11/pod-1"]

/-- **An input `Gen` may return**, as far as the model needs: its key one of the workload's, its
UID, node and app fit an object's, its minimum resource version parses (stage 7b), below `2^63`;
a list's match one of the three, its key under the resource prefix, its limit not negative (stage
7e-4: `refine_list`'s and `GetList`'s premises), a key `PrepareKey` takes. -/
def InOk (x : Input) : Prop :=
  x.Key' ∈ wkKeysL ∧ x.UID'.length < 256 ∧ x.Node'.length < 256 ∧ x.App'.length < 256 ∧
    (∃ n, parseRVD x.MinRV' = some n ∧ uint.Z n < 2 ^ 63) ∧
    (x.Kind' = W64 4 → (x.Match' = W64 0 ∨ x.Match' = W64 1 ∨ x.Match' = W64 2) ∧
      go!"/objs/" <+: x.ListKey' ∧ 0 ≤ sint.Z x.Limit' ∧
      (k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive').isSome)

theorem wkKeysL_len (k : GoString) (h : k ∈ wkKeysL) : k.length ≤ 11 := by
  simp only [wkKeysL, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl <;> decide

theorem inOk_crFits (x : Input) (h : InOk x) : crFits x :=
  ⟨by have := wkKeysL_len _ h.1; omega, h.2.1, h.2.2.1, h.2.2.2.1⟩

theorem inOk_inFits (x : Input) (h : InOk x) : inFits x :=
  ⟨by have := wkKeysL_len _ h.1; omega, h.2.2.1, h.2.2.2.1⟩

/-- A `Get`'s minimum resource version (`0` if it does not parse: never, `InOk`). -/
def minOf (x : Input) : w64 := (parseRVD x.MinRV').getD 0

/-- A Go `Obj`'s store object (the zero object if it does not fit: never for a cached object,
`cachedObjOk`). -/
def dobjOf (ob : Obj) : DObj := if h : fitsD ob then DObj.ofObj ob h else dzero

theorem dobjOf_toObj (o : DObj) (r : w64) : dobjOf (o.toObj r) = o := by
  unfold dobjOf; rw [dif_pos (DObj.toObj_fits o r)]; rfl

/-- The object `Apply` caches for an answer (`objOf(out)`). -/
abbrev cachedOf (y : Output) : Obj := objOfL y

/-- The store's preconditions of an input, as the store's model takes them. -/
abbrev preD (x : Input) : DObj → Nat → Bool := driverCodec.preOk (kpreOf x)

/-- **The store's model on the input `x`** (see the file header; not a list): its next state and
the driver's output of its answer. -/
def kStep (eD eU : GoInterface) (x : Input) (ks : KSt DObj) : KSt DObj × Output :=
  if x.Kind' = W64 0 then
    ((ks.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).1,
      outOf (ks.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).2)
  else if x.Kind' = W64 1 then
    ((ks.delete (mkeyL x.Key') (preD x) (rejD eD x.HasReject' x.Reject')).1,
      outOf (ks.delete (mkeyL x.Key') (preD x) (rejD eD x.HasReject' x.Reject')).2)
  else if x.Kind' = W64 2 then
    ((ks.update (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD eU x)).1,
      outOf (ks.update (mkeyL x.Key') x.IgnoreNotFound' dzero (preD x) (updD eU x)).2)
  else (ks, outOf (ks.get (E := Empty) (mkeyL x.Key') (uint.nat (minOf x)) x.IgnoreNotFound'))

/-- **The store's model refines the driver's on an input** (6b's `refine_*`; not a list). -/
theorem refine_step (eD eU : GoInterface) (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input)
    (hx : InOk x) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (kStep eD eU x ks).1 (mstepL x g).1 ∧ (kStep eD eU x ks).2 = (mstepL x g).2 := by
  unfold kStep mstepL
  by_cases h0 : x.Kind' = W64 0
  · simp only [h0, ↓reduceIte]
    exact refine_create ks g h x (inOk_crFits x hx) hrv
  by_cases h1 : x.Kind' = W64 1
  · simp only [h0, h1, ↓reduceIte]
    exact refine_delete ks g h x eD hrv
  by_cases h2 : x.Kind' = W64 2
  · simp only [h0, h1, h2, ↓reduceIte]
    exact refine_update ks g h x eU (inOk_inFits x hx) hrv
  simp only [h0, h1, h2, ↓reduceIte]
  obtain ⟨n, hn, -⟩ := hx.2.2.2.2.1
  have hm : minOf x = n := by unfold minOf; rw [hn]; rfl
  rw [hm]
  exact ⟨h, refine_get ks g h x n hn⟩

/-- **A list's answer at etcd's state `σ`** (stage 7e-4): what `call`'s `listOut` makes of
`GetList`'s answer there (`refine_list`'s left side): `ETooLarge` above `σ`'s revision, else the
store's list at the read revision. -/
def lOut (x : Input) (σ : KVState) : Output :=
  match parseRVD x.MinRV', k8s.prepareKeyM go!"/objs" x.ListKey' x.Recursive' with
  | some n, some k =>
    let R := listRevL (matchOptL x) x.Recursive' x.Limit' n
    let s := if uint.Z R = 0 then σ.store else σ.at (uint.nat R)
    if σ.rev < uint.nat n then tooLargeL
    else listOutDriver x (if uint.Z R = 0 then W64 (σ.rev : Int) else R)
      (kListL driverCodec.dec (selD x) (limN x.Limit') (go!"/registry" ++ k) x.Recursive' s)
  | _, _ => otherL

/-- **On related states a list answers the driver's model** (7e-3c's `refine_list`). -/
theorem refine_lOut (x : Input) (h : HSt) (σ : KVState) (hrel : KRelH h σ) (hx : InOk x)
    (hk4 : x.Kind' = W64 4) : lOut x σ = mlistL x h := by
  obtain ⟨hm, hlk, -, hks⟩ := hx.2.2.2.2.2 hk4
  obtain ⟨n, hn, -⟩ := hx.2.2.2.2.1
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.1 hks
  have := refine_list x h σ k n hrel hm hlk hk hn
  unfold lOut
  rw [hn, hk]
  simp only at this ⊢
  by_cases hlt : σ.rev < uint.nat n <;> simp only [hlt, ↓reduceIte] at this ⊢ <;> exact this

/-- **The model's step changes only the input's key.** -/
theorem kStep_items (eD eU : GoInterface) (x : Input) (ks : KSt DObj) (k : GoString)
    (hk : k ≠ mkeyL x.Key') : (kStep eD eU x ks).1.items k = ks.items k := by
  unfold kStep
  by_cases h0 : x.Kind' = W64 0
  · simp only [h0, ↓reduceIte, KSt.create]
    repeat' split
    all_goals simp_all [KSt.setItem]
  by_cases h1 : x.Kind' = W64 1
  · simp only [h0, h1, ↓reduceIte, KSt.delete]
    repeat' split
    all_goals simp_all [KSt.delItem]
  by_cases h2 : x.Kind' = W64 2
  · simp only [h0, h1, h2, ↓reduceIte, KSt.update]
    repeat' split
    all_goals simp_all [KSt.setItem]
  simp only [h0, h1, h2, ↓reduceIte]

/-- **Where an object answer's item is** (from `ks` to `ks'` at the key `K`): the item of `ks` or
of `ks'` at `K`, or (a delete) the item `ks` had at `K`, gone at the next resource version. -/
def RespFrom {E : Type} (ks ks' : KSt DObj) (K : GoString) : KResp DObj E → Prop
  | .obj o rv => (∃ b, ks.items K = some ⟨o, rv, b⟩ ∨ ks'.items K = some ⟨o, rv, b⟩) ∨
      (∃ it, rv = ks.rv + 1 ∧ ks.items K = some it ∧ ks'.items K = none ∧ ks'.rv = ks.rv + 1)
  | _ => True

theorem KItem.eq_cases (it : KItem DObj) :
    it = ⟨it.obj, it.rv, false⟩ ∨ it = ⟨it.obj, it.rv, true⟩ := by
  cases it with
  | mk o r b => cases b <;> simp

theorem respFrom_create {E : Type} (ks : KSt DObj) (k : GoString) (o : DObj) :
    RespFrom ks (ks.create (E := E) k o 0).1 k (ks.create (E := E) k o 0).2 := by
  unfold KSt.create
  repeat' split
  all_goals simp_all [RespFrom, KSt.setItem]

theorem respFrom_delete {E : Type} (ks : KSt DObj) (k : GoString) (pre : DObj → Nat → Bool)
    (v : DObj → Nat → Option E) :
    RespFrom ks (ks.delete k pre v).1 k (ks.delete k pre v).2 := by
  unfold KSt.delete
  repeat' split
  all_goals simp_all [RespFrom, KSt.delItem]

theorem respFrom_update {E : Type} (ks : KSt DObj) (k : GoString) (ig : Bool) (z : DObj)
    (pre : DObj → Nat → Bool) (f : DObj → Nat → Except E DObj) :
    RespFrom ks (ks.update k ig z pre f).1 k (ks.update k ig z pre f).2 := by
  unfold KSt.update
  repeat' split
  all_goals simp_all [RespFrom, KSt.setItem]
  all_goals exact KItem.eq_cases _

theorem respFrom_get {E : Type} (ks : KSt DObj) (k : GoString) (req : Nat) (ig : Bool) :
    RespFrom ks ks k (ks.get (E := E) k req ig) := by
  unfold KSt.get
  repeat' split
  all_goals simp_all [RespFrom]
  all_goals exact KItem.eq_cases _

/-- **What an answer with a name is** (`Apply` caches it): an object answer, its item where
`RespFrom` says. -/
def AnsFrom (ks ks' : KSt DObj) (K : GoString) (y : Output) : Prop :=
  y.Err' = W64 0 → y.Name' ≠ [] → ∃ (o : DObj) (rv : Nat),
    y = objOutL (o.toObj (W64 (rv : Int))) ∧ RespFrom (E := Empty) ks ks' K (.obj o rv)

theorem ansFrom_outOf {E : Type} (ks ks' : KSt DObj) (K : GoString) (r : KResp DObj E)
    (h : RespFrom ks ks' K r) : AnsFrom ks ks' K (outOf r) := by
  intro he hn
  cases r with
  | obj o rv => exact ⟨o, rv, rfl, h⟩
  | zero => exact absurd rfl hn
  | err e =>
    cases e <;> simp [outOf, rejectedL, otherL, tooLargeL, errOutL] at he hn

/-- **The model's answer, with a name, is an item's** (`AnsFrom`). -/
theorem kStep_ansFrom (eD eU : GoInterface) (x : Input) (ks : KSt DObj) :
    AnsFrom ks (kStep eD eU x ks).1 (mkeyL x.Key') (kStep eD eU x ks).2 := by
  unfold kStep
  by_cases h0 : x.Kind' = W64 0
  · simp only [h0, ↓reduceIte]
    exact ansFrom_outOf _ _ _ _ (respFrom_create _ _ _)
  by_cases h1 : x.Kind' = W64 1
  · simp only [h0, h1, ↓reduceIte]
    exact ansFrom_outOf _ _ _ _ (respFrom_delete _ _ _ _)
  by_cases h2 : x.Kind' = W64 2
  · simp only [h0, h1, h2, ↓reduceIte]
    exact ansFrom_outOf _ _ _ _ (respFrom_update _ _ _ _ _ _)
  simp only [h0, h1, h2, ↓reduceIte]
  exact ansFrom_outOf _ _ _ _ (respFrom_get _ _ _ _)

/-- A list's answer has no name (`Apply` caches none). -/
theorem lOut_name (x : Input) (σ : KVState) : (lOut x σ).Name' = [] := by
  unfold lOut listOutDriver
  split
  · dsimp only
    split
    · rfl
    · split <;> (try split) <;> rfl
  · rfl

/-- **A `Get` answers other than `EOther`/`ETooLarge` only at its minimum resource version** (D5):
below it, the model answers `ETooLarge` (stage 7e). -/
theorem kStep_min (eD eU : GoInterface) (x : Input) (ks : KSt DObj) (hk : x.Kind' = W64 3)
    (h : (kStep eD eU x ks).2.Err' ≠ W64 6) : uint.nat (minOf x) ≤ ks.rv := by
  have h0 : ¬ x.Kind' = W64 0 := by rw [hk]; decide
  have h1 : ¬ x.Kind' = W64 1 := by rw [hk]; decide
  have h2 : ¬ x.Kind' = W64 2 := by rw [hk]; decide
  by_cases hm : uint.nat (minOf x) ≤ ks.rv
  · exact hm
  exfalso
  apply h
  simp only [kStep, h0, h1, h2, ↓reduceIte, KSt.get]
  rw [if_pos (by omega)]
  rfl

/-- **The driver's model answers `EOther` to no write** (stage 7b): a write's outputs are objects,
"not found", "key exists", "invalid object" or a rejection. -/
theorem mstepL_err (x : Input) (g : GSt)
    (hk : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) : (mstepL x g).2.Err' ≠ W64 4 := by
  unfold mstepL mcreateL mdeleteL mupdateL
  rcases hk with h | h | h <;>
    simp only [h, objOutL, existsL, notFoundL, rejectedL, invalidObjL, errOutL]
  all_goals (repeat' split) <;> simp_all

/-- A write's model answer, as porcupine's model decodes its output. -/
theorem ansOf_mstepL (x : Input) (g : GSt)
    (hk : x.Kind' = W64 0 ∨ x.Kind' = W64 1 ∨ x.Kind' = W64 2) :
    ansOf (mstepL x g).2 = .ok (mstepL x g).2 := by
  unfold ansOf
  rw [if_neg (mstepL_err x g hk)]

/-- The pending writes (in some order). -/
def pendIns (M : GMap Nat Input) : List Input := M.toList.map Prod.snd

theorem pendIns_insert (M : GMap Nat Input) (n : Nat) (i : Input) (h : M !! n = none) :
    (pendIns (GMap.insert n i M)).Perm (i :: pendIns M) := by
  unfold pendIns
  have hp := Iris.Std.LawfulFiniteMap.toList_insert (M := GMap Nat) (m := M) (k := n) (v := i) h
  exact hp.map Prod.snd

theorem pendIns_delete (M : GMap Nat Input) (n : Nat) (i : Input) (h : M !! n = some i) :
    (pendIns M).Perm (i :: pendIns (GMap.delete n M)) := by
  unfold pendIns
  have hp := Iris.Std.LawfulFiniteMap.toList_delete (M := GMap Nat) (m := M) (k := n) (v := i) h
  exact hp.map Prod.snd

/-! ### The history (stage 7e-4) -/

/-- **Every revision's keys are the workload's** (etcd keys `mkeyL` of `wkKeysL`). -/
def keysOk (σ : KVState) : Prop :=
  ∀ r ≤ σ.rev, ∀ v ∈ (σ.at r).kvs, v.key ∈ wkKeysL.map mkeyL

/-- A step extends the history: the states agree at every revision of the first. -/
theorem kvNext_at {σ σ' : KVState} (hn : k8s.KvNext σ σ') (r : Nat) (hr : r ≤ σ.rev) :
    σ'.at r = σ.at r := by
  rcases hn with rfl | ⟨hrv, -, hext⟩
  · rfl
  · obtain ⟨hc, hb, hp⟩ := hext
    exact (k8s.kvSameHist_at σ σ' r ⟨hc, hb, Or.inl hp⟩ hr (by omega)).symm

theorem kvNext_rev {σ σ' : KVState} (hn : k8s.KvNext σ σ') :
    σ'.rev = σ.rev ∨ σ'.rev = σ.rev + 1 := by
  rcases hn with rfl | ⟨hrv, -⟩
  · exact Or.inl rfl
  · exact Or.inr hrv

theorem w64_nat_inj (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64)
    (h : W64 (a : Int) = W64 (b : Int)) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [W64, BitVec.toNat_ofInt] at this
  omega

/-- **The driver's history follows a step of etcd's state** (`advance`): related at `σ` with the
history as long as `σ`'s revision, and the next store related to `σ'`'s, the advanced
configuration is related at `σ'`. -/
theorem krelH_step (h : HSt) (σ σ' : KVState) (st' : GSt) (hrel : KRelH h σ)
    (hlen : h.hist.length = σ.rev) (hn : k8s.KvNext σ σ') (hr' : σ'.rev < 2 ^ 63)
    (hS : KRelS σ'.store σ'.rev st')
    (hmod : ∀ r ≤ σ'.rev, ∀ v ∈ (σ'.at r).kvs, uint.Z v.modRev < 2 ^ 63) :
    KRelH (advanceL h st') σ' ∧ (advanceL h st').hist.length = σ'.rev := by
  obtain ⟨hlt, hcur, hhist, -⟩ := hrel
  have hrv0 : W64 (σ.rev : Int) = h.st.rv := hcur.2.1
  have hrv1 : W64 (σ'.rev : Int) = st'.rv := hS.2.1
  rcases kvNext_rev hn with he | he
  · -- the revision kept: the history kept
    have hst : st'.rv = h.st.rv := by rw [← hrv1, ← hrv0, he]
    have hadv : advanceL h st' = ⟨st', h.hist⟩ := by
      unfold advanceL; rw [if_neg (by rw [hst]; exact fun h => h rfl)]
    rw [hadv]
    refine ⟨⟨hr', hS, fun r h1 h2 => ?_, hmod⟩, by rw [he]; exact hlen⟩
    rw [kvNext_at hn r (by omega)]
    exact hhist r h1 (by omega)
  · have hst : st'.rv ≠ h.st.rv := by
      rw [← hrv1, ← hrv0]
      intro e
      have := w64_nat_inj _ _ (by omega) (by omega) e
      omega
    have hadv : advanceL h st' = ⟨st', h.hist ++ [st']⟩ := by
      unfold advanceL; rw [if_pos hst]
    rw [hadv]
    refine ⟨⟨hr', hS, fun r h1 h2 => ?_, hmod⟩, by simp [hlen, he]⟩
    have hrw : uint.nat (W64 (r : Int)) = r := by
      simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
    by_cases hle : r ≤ σ.rev
    · rw [kvNext_at hn r hle, histAtL_snoc_le _ _ _ (by rw [hrw, hlen]; exact hle)]
      exact hhist r h1 hle
    · have hr : r = σ'.rev := by omega
      rw [histAtL_snoc_gt _ _ _ (by rw [hrw, hlen]; omega), hr]
      exact hS

/-- Keys of the workload are few and short (`kvKeysShort`). -/
theorem keysOk_short (σ : KVState) (h : keysOk σ) : k8s.kvKeysShort σ := by
  intro R hR
  have hs := KVStore.kvs_sorted (σ.at R)
  have hnd : ((σ.at R).kvs.map EtcdKv.key).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact hs.imp fun hab e => by
      unfold etcdKvLess at hab; rw [e] at hab; exact go.goStringLt_irrefl _ hab
  have hsub : (σ.at R).kvs.map EtcdKv.key ⊆ wkKeysL.map mkeyL := by
    intro k hk
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hk
    exact h R hR v hv
  have hl := List.Nodup.length_le_of_subset hnd hsub
  simp only [List.length_map] at hl
  refine ⟨by simp at hl; omega, fun kv hkv => ?_⟩
  have := h R hR kv hkv
  simp only [wkKeysL, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil,
    or_false] at this
  rcases this with e | e | e | e <;> rw [e] <;> decide

end pure

section rel
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The store is the driver's** (its decoding the driver's codec's, its prefix `/registry/objs`):
its model of etcd's state is 7e-3c's (`KRelS`'s `absK`). -/
def CfgD (c : StoreCfg GF DObj) : Prop := c.S.dec = driverCodec.dec ∧ c.pfx = kpfxD

theorem krel_abs (c : StoreCfg GF DObj) (hc : CfgD c) (σ : KVState) (g : GSt)
    (hr : σ.rev < 2 ^ 64) : KRel (c.abs σ) g ↔ KRelS σ.store σ.rev g := by
  have e : c.abs σ = absK driverCodec.dec kpfxD ⟨linkv.absM σ.store.kvs, σ.rev⟩ := by
    unfold StoreCfg.abs; rw [hc.1, hc.2]; rfl
  rw [e, krelS_iff _ _ _ hr]

/-- **The instance's relation** (see the file header; stage 7e-4: the configuration's history, the
store's history fit for lists, the workload's keys). -/
structure KOk (c : StoreCfg GF DObj) (g0 : HSt) (S : linkv.PSet HSt Input) (σ : KVState)
    (M : GMap Nat Input) (nx : Nat) : Prop where
  closed : linkv.PSet.Closed (kSpec g0) S
  wf : kvWf c σ
  hwf : kvWfHist c σ
  keys : keysOk σ
  fresh : ∀ n, nx ≤ n → M !! n = none
  ins : ∀ n i, M !! n = some i → InOk i ∧ isWriteL i = true
  cfg : ∃ cf, S cf ∧ KRelH cf.st σ ∧ cf.st.hist.length = σ.rev ∧ (pendIns M).Perm cf.pend

/-- **Every revision's key-values decode and have their mod revision there** (`kvWfHist`), after a
step of etcd's state to a state of the store. -/
theorem kvWfHist_step (c : StoreCfg GF DObj) (σ σ' : KVState)
    (h : kvWfHist c σ) (hw' : kvWf c σ') (hn : k8s.KvNext σ σ') : kvWfHist c σ' := by
  intro r hr v hv
  by_cases hle : r ≤ σ.rev
  · rw [kvNext_at hn r hle] at hv
    exact h r hle v hv
  have hr' : r = σ'.rev := by rcases kvNext_rev hn with e | e <;> omega
  subst hr'
  have hv' : v ∈ σ'.kvs := hv
  have hf := txn.findKey_of_mem_sorted hw'.1 hv'
  have hm := hw'.2.2.1 v.key (linkv.absVR v) (by simp [linkv.absSt, linkv.absM, hf])
  refine ⟨fun hp => ?_, hm⟩
  have := hw'.2.1 v.key (linkv.absVR v) hp (by simp [linkv.absSt, linkv.absM, hf])
  simp only [linkv.absVR] at this
  intro e; rw [e] at this; cases this

open Classical in
/-- **A step whose model changes the store's items at `K` only adds keys under the prefix at `K`**:
a new key under the prefix has an item after the step (it decodes) and none before. -/
theorem newKey_eq (c : StoreCfg GF DObj) (σ σ' : KVState)
    (hw' : kvWf c σ') (K : GoString)
    (hK : ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k)
    (v : EtcdKv) (hv : v ∈ σ'.kvs) (hp : c.pfx <+: v.key) (hnew : ∀ w ∈ σ.kvs, w.key ≠ v.key) :
    v.key = K := by
  by_cases hne : v.key = K
  · exact hne
  exfalso
  have he := hK v.key hne
  have hf' := txn.findKey_of_mem_sorted hw'.1 hv
  obtain ⟨o, b, hob⟩ := c.dec_of_wf σ' hw' v.key hp v hf'
  rw [c.abs_some σ' v.key hp v hf' o b hob] at he
  have hf : mvcc.findKey v.key σ.kvs = none := by
    cases hf : mvcc.findKey v.key σ.kvs with
    | none => rfl
    | some w => exact absurd (mvcc.findKey_key hf) (hnew w (mvcc.findKey_mem hf))
  rw [c.abs_none σ _ hf] at he
  cases he

/-- **The keys stay the workload's** across a step of etcd's state whose new keys are under the
prefix (`KeysIn`, the store's) and whose model changes the items at a workload key only. -/
theorem keysOk_step (c : StoreCfg GF DObj) (σ σ' : KVState)
    (h : keysOk σ) (hw' : kvWf c σ') (hn : k8s.KvNext σ σ') (hki : k8s.KeysIn c.pfx σ σ')
    (K : GoString) (hKw : K ∈ wkKeysL.map mkeyL)
    (hK : ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k) : keysOk σ' := by
  intro r hr v hv
  by_cases hle : r ≤ σ.rev
  · rw [kvNext_at hn r hle] at hv
    exact h r hle v hv
  have hr' : r = σ'.rev := by rcases kvNext_rev hn with e | e <;> omega
  subst hr'
  have hv' : v ∈ σ'.kvs := hv
  have hold : ∀ w ∈ σ.kvs, w.key = v.key → v.key ∈ wkKeysL.map mkeyL := fun w hw e =>
    e ▸ h σ.rev (Nat.le_refl _) w hw
  rcases hki v hv' with ⟨w, hw, e⟩ | hp
  · exact hold w hw e
  · by_cases hex : ∃ w ∈ σ.kvs, w.key = v.key
    · obtain ⟨w, hw, e⟩ := hex; exact hold w hw e
    · have := newKey_eq c σ σ' hw' K hK v hv' hp (fun w hw e => hex ⟨w, hw, e⟩)
      rw [this]; exact hKw

variable {c : StoreCfg GF DObj} {g0 : HSt}

/-- The relation at the start: the model's initial state, nothing pending. -/
theorem kOk_init (σ : KVState) (hw : kvWf c σ) (hwh : kvWfHist c σ) (hk : keysOk σ)
    (he : KRelH g0 σ) (hl : g0.hist.length = σ.rev) :
    KOk c g0 (linkv.pInit (kSpec g0)) σ (∅ : GMap Nat Input) 0 := by
  refine ⟨linkv.pInit_closed, hw, hwh, hk, fun _ _ => rfl, (fun _ _ h => by cases h),
    ⟨⟨g0, []⟩, rfl, he, hl, ?_⟩⟩
  simp [pendIns]

/-- **A configuration follows an operation** (not a list) answered at etcd's state `σ`, stepping
to `σ'`: the store's model's step is the driver's, and the advanced configuration is related. -/
theorem cfg_step (hc : CfgD c) (eD eU : GoInterface) (x : Input) (hx : InOk x)
    (hk4 : x.Kind' ≠ W64 4) (h : HSt) (σ σ' : KVState) (hrel : KRelH h σ)
    (hlen : h.hist.length = σ.rev) (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1)
    (hn : k8s.KvNext σ σ') (hwh' : kvWfHist c σ') (hr : σ.rev + 2 < 2 ^ 63) :
    KRelH (kstepL x h).1 σ' ∧ (kstepL x h).1.hist.length = σ'.rev ∧
      (kStep eD eU x (c.abs σ)).2 = (kstepL x h).2 := by
  have hr' : σ'.rev < 2 ^ 63 := by rcases kvNext_rev hn with e | e <;> omega
  have hK := (krel_abs c hc σ h.st (by omega)).2 hrel.2.1
  have hrv : (c.abs σ).rv + 1 < 2 ^ 64 := by rw [abs_rv]; omega
  obtain ⟨hK', hout⟩ := refine_step eD eU _ _ hK x hx hrv
  rw [← habs] at hK'
  have hS := (krel_abs c hc σ' _ (by omega)).1 hK'
  have hmod : ∀ r ≤ σ'.rev, ∀ v ∈ (σ'.at r).kvs, uint.Z v.modRev < 2 ^ 63 := by
    intro r hr0 v hv
    have := (hwh' r hr0 v hv).2.2
    simp only [uint.nat] at this; simp only [uint.Z]; omega
  have hst : kstepL x h = (advanceL h (mstepL x h.st).1, (mstepL x h.st).2) := by
    unfold kstepL; rw [if_neg hk4]
  rw [hst]
  obtain ⟨h1, h2⟩ := krelH_step h σ σ' _ hrel hlen hn hr' hS hmod
  exact ⟨h1, h2, hout⟩

/-- **An operation answered at the real configuration** (not a list): the store's model of `σ`,
which has room (`hr`, the firing's), stepped by the input to the store's model of `σ'`. -/
theorem kOk_ok (hc : CfgD c) {S : linkv.PSet HSt Input} {σ σ' : KVState} {M : GMap Nat Input}
    {nx : Nat} (H : KOk c g0 S σ M nx) (eD eU : GoInterface) (x : Input) (hx : InOk x)
    (hk4 : x.Kind' ≠ W64 4)
    (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1) (hw' : kvWf c σ') (hn : k8s.KvNext σ σ')
    (hki : k8s.KeysIn c.pfx σ σ') (hr : σ.rev + 2 < 2 ^ 63) :
    ∃ S', (linkv.pSeq (kSpec g0)).step S (x, .ok (kStep eD eU x (c.abs σ)).2) = some S' ∧
      KOk c g0 S' σ' M nx := by
  obtain ⟨cf, hcf, hrel, hlen, hp⟩ := H.cfg
  have hwh' := kvWfHist_step c σ σ' H.hwf hw' hn
  obtain ⟨hrel', hlen', hout⟩ := cfg_step hc eD eU x hx hk4 cf.st σ σ' hrel hlen habs hn hwh' hr
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_ok (P := kSpec g0) hcf x
  have hKw : mkeyL x.Key' ∈ wkKeysL.map mkeyL := List.mem_map_of_mem hx.1
  have hkeys := keysOk_step c σ σ' H.keys hw' hn hki _ hKw
    (fun k hk => by rw [habs]; exact kStep_items eD eU x _ k hk)
  refine ⟨S', ?_, linkv.pSeq_step_closed hS', hw', hwh', hkeys, H.fresh, H.ins,
    ⟨_, hc', hrel', hlen', hp⟩⟩
  rw [hout]; exact hS'

/-- **A list answered at the real configuration** (stage 7e-4): `lOut` at etcd's state `σ`, the
configuration and etcd's state unchanged. -/
theorem kOk_list {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) (x : Input) (hx : InOk x) (hk4 : x.Kind' = W64 4) :
    ∃ S', (linkv.pSeq (kSpec g0)).step S (x, .ok (lOut x σ)) = some S' ∧ KOk c g0 S' σ M nx := by
  obtain ⟨cf, hcf, hrel, hlen, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_ok (P := kSpec g0) hcf x
  have hst : kstepL x cf.st = (cf.st, mlistL x cf.st) := by unfold kstepL; rw [if_pos hk4]
  rw [show (kSpec g0).step x cf.st = (cf.st, mlistL x cf.st) from hst] at hS' hc'
  refine ⟨S', ?_, linkv.pSeq_step_closed hS', H.wf, H.hwf, H.keys, H.fresh, H.ins,
    ⟨_, hc', hrel, hlen, hp⟩⟩
  rw [refine_lOut x cf.st σ hrel hx hk4]; exact hS'

/-- A write committed as pending, its token minted at `nx`. -/
theorem kOk_errW {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) (x : Input) (hw : isWriteL x = true) (hx : InOk x) :
    ∃ S', (linkv.pSeq (kSpec g0)).step S (x, .err) = some S' ∧
      KOk c g0 S' σ (GMap.insert nx x M) (nx + 1) := by
  obtain ⟨cf, hc, hst, hlen, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errW_pending (P := kSpec g0) hc x hw
  refine ⟨S', hS', linkv.pSeq_step_closed hS', H.wf, H.hwf, H.keys, ?_, ?_, ⟨_, hc', hst, hlen, ?_⟩⟩
  · intro n hn
    show (GMap.insert nx x M) !! n = none
    rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact H.fresh n (by omega)
  · intro n j hn
    by_cases e : nx = n
    · subst e
      have : (GMap.insert nx x M) !! nx = some x := GMap.lookup_insert _ _ _
      rw [this] at hn
      cases hn
      exact ⟨hx, hw⟩
    · have : (GMap.insert nx x M) !! n = M !! n := GMap.lookup_insert_ne _ _ e
      rw [this] at hn
      exact H.ins n j hn
  · exact (pendIns_insert M nx x (H.fresh nx (Nat.le_refl _))).trans (hp.cons _)

/-- A read that failed. -/
theorem kOk_errR {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) (x : Input) (hw : isWriteL x = false) :
    ∃ S', (linkv.pSeq (kSpec g0)).step S (x, .err) = some S' ∧ KOk c g0 S' σ M nx := by
  obtain ⟨cf, hc, hst, hlen, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errR (P := kSpec g0) hc x hw
  exact ⟨S', hS', linkv.pSeq_step_closed hS', H.wf, H.hwf, H.keys, H.fresh, H.ins,
    ⟨cf, hc', hst, hlen, hp⟩⟩

theorem isWriteL_ne4 (x : Input) (hw : isWriteL x = true) : x.Kind' ≠ W64 4 := by
  intro e; simp [isWriteL, e] at hw

/-- **A late effect**: the pending write `n ↦ x` takes effect, the model state unchanged. -/
theorem kOk_pend (hc : CfgD c) {S : linkv.PSet HSt Input} {σ σ' : KVState} {M : GMap Nat Input}
    {nx : Nat} (H : KOk c g0 S σ M nx) (eD eU : GoInterface) (n : Nat) (x : Input)
    (hn : M !! n = some x)
    (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1) (hw' : kvWf c σ') (hnx : k8s.KvNext σ σ')
    (hki : k8s.KeysIn c.pfx σ σ') (hr : σ.rev + 2 < 2 ^ 63) :
    KOk c g0 S σ' (GMap.delete n M) nx := by
  obtain ⟨cf, hcf, hst, hlen, hp⟩ := H.cfg
  obtain ⟨hx, hwx⟩ := H.ins n x hn
  have hd := pendIns_delete M n x hn
  have hmem : x ∈ cf.pend := hp.subset (hd.symm.subset List.mem_cons_self)
  have hwh' := kvWfHist_step c σ σ' H.hwf hw' hnx
  obtain ⟨hrel', hlen', -⟩ :=
    cfg_step hc eD eU x hx (isWriteL_ne4 x hwx) cf.st σ σ' hst hlen habs hnx hwh' hr
  have hKw : mkeyL x.Key' ∈ wkKeysL.map mkeyL := List.mem_map_of_mem hx.1
  have hkeys := keysOk_step c σ σ' H.keys hw' hnx hki _ hKw
    (fun k hk => by rw [habs]; exact kStep_items eD eU x _ k hk)
  refine ⟨H.closed, hw', hwh', hkeys, ?_, ?_, ⟨_, H.closed.apply hcf hmem, hrel', hlen', ?_⟩⟩
  · intro m hm
    show (GMap.delete n M) !! m = none
    by_cases e : n = m
    · subst e; exact GMap.lookup_delete _ _
    · rw [GMap.lookup_delete_ne _ e]; exact H.fresh m hm
  · intro m j hm
    by_cases e : n = m
    · subst e
      have : (GMap.delete n M) !! n = none := GMap.lookup_delete _ _
      rw [this] at hm; cases hm
    · have : (GMap.delete n M) !! m = M !! m := GMap.lookup_delete_ne _ e
      rw [this] at hm
      exact H.ins m j hm
  · refine List.Perm.cons_inv ((hd.symm.trans hp).trans ?_)
    exact List.perm_cons_erase hmem

/-- A firing that leaves etcd's state as it was. -/
theorem kOk_same {S : linkv.PSet HSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) : KOk c g0 S σ M nx := H

open Classical in
/-- **A step of etcd's state that changes the store's items at one key `K` at most changes one key
under the prefix** (at the next revision): a new key-value is at the new revision, which no item
of `σ` has, and a deleted key under the prefix had an item. -/
theorem chgOf_pfx_one (σ σ' : KVState) (hn : KvNext σ σ') (hrv : σ'.rev = σ.rev + 1)
    (hw : kvWf c σ) (hw' : kvWf c σ') (K : GoString)
    (hK : ∀ k, k ≠ K → (c.abs σ').items k = (c.abs σ).items k) :
    (((chgOf σ σ').map Prod.fst).filter (fun k => decide (c.pfx <+: k))).length ≤ 1 := by
  have hnew : ∀ v ∈ σ'.kvs, v ∈ σ.kvs ∨ v.modRev = W64 ((σ'.rev : Nat) : Int) := by
    rcases hn with he | ⟨-, h, -⟩
    · intro v hv; left; rw [← he]; exact hv
    · exact h
  have hR : uint.nat (W64 ((σ'.rev : Nat) : Int)) = σ'.rev := by
    have := hw'.2.2.2
    simp only [linkv.absSt] at this
    simp only [W64, uint.nat, BitVec.toNat_ofInt]; omega
  have hall : ∀ a ∈ ((chgOf σ σ').map Prod.fst).filter (fun k => decide (c.pfx <+: k)), a = K := by
    intro a ha
    simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at ha
    obtain ⟨⟨⟨a', x⟩, hax, rfl⟩, hpa⟩ := ha
    simp only at hpa ⊢
    by_cases hne : a' = K
    · exact hne
    exfalso
    have he := hK a' hne
    rcases chgOf_keys σ σ' a' x hax with ⟨v, hv, hv0, rfl⟩ | ⟨⟨v, hv, rfl⟩, hd⟩
    · have hf' := txn.findKey_of_mem_sorted hw'.1 hv
      obtain ⟨o, b, hob⟩ := c.dec_of_wf σ' hw' v.key hpa v hf'
      rw [c.abs_some σ' v.key hpa v hf' o b hob] at he
      have hm : v.modRev = W64 ((σ'.rev : Nat) : Int) := (hnew v hv).resolve_left hv0
      cases hf : mvcc.findKey v.key σ.kvs with
      | none => rw [c.abs_none σ _ hf] at he; cases he
      | some w =>
        obtain ⟨o', b', hob'⟩ := c.dec_of_wf σ hw v.key hpa w hf
        rw [c.abs_some σ v.key hpa w hf o' b' hob'] at he
        have hrw : uint.nat v.modRev = uint.nat w.modRev := by
          have := congrArg KItem.rv (Option.some.inj he)
          simpa using this
        have hle := (hw.2.2.1 v.key (linkv.absVR w)
          (by simp [linkv.absSt, linkv.absM, hf])).2
        simp only [linkv.absVR, linkv.absSt] at hle
        rw [hm, hR] at hrw
        omega
    · have hf' : mvcc.findKey v.key σ'.kvs = none := by
        unfold mvcc.findKey
        exact List.find?_eq_none.2 (fun w hw => by simpa using hd w hw)
      rw [c.abs_none σ' _ hf'] at he
      have hf := txn.findKey_of_mem_sorted hw.1 hv
      obtain ⟨o, b, hob⟩ := c.dec_of_wf σ hw v.key hpa v hf
      rw [c.abs_some σ v.key hpa v hf o b hob] at he
      cases he
  have hnd : (((chgOf σ σ').map Prod.fst).filter (fun k => decide (c.pfx <+: k))).Nodup :=
    (chgOf_nodup σ σ' hw.1 hw'.1).sublist List.filter_sublist
  generalize ((chgOf σ σ').map Prod.fst).filter (fun k => decide (c.pfx <+: k)) = L at hall hnd ⊢
  match L, hall, hnd with
  | [], _, _ => simp
  | [_], _, _ => simp
  | a :: b :: _, hall, hnd =>
    have ha := hall a (by simp)
    have hb := hall b (by simp)
    exact absurd (ha.trans hb.symm) ((List.pairwise_cons.1 hnd).1 b (by simp))

end rel

/-! ## The ghost state and the invariant -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The instance's ghost names: the history's variable, the pending writes' map, the revisions'
states' map. -/
structure KNames where
  h : GName
  p : GName
  r : GName

/-- The instance's namespace: its invariant's (`drvInvN`) and a call's (`callN`). -/
def drvN : Namespace := nroot .@ "k8setcd3"

def drvInvN : Namespace := drvN .@ "inv"

def callN : Namespace := drvN .@ "call"

/-- **`Apply`'s mask** (`applySpec`'s `Eapp`): the server's invariants, the store's, the
instance's. -/
def drvE : CoPset := ↑srvRaftN ∪ ↑kvN ∪ ↑k8sN ∪ ↑drvN

theorem drvN_out (p : Pos) (hp : p ∈ (↑drvN : CoPset)) :
    p ∉ (↑srvRaftN : CoPset) ∧ p ∉ (↑kvN : CoPset) ∧ p ∉ (↑k8sN : CoPset) :=
  ⟨fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

theorem drvN_rw (p : Pos) (hp : p ∈ (↑drvN : CoPset)) : p ∈ rwMask := by
  obtain ⟨h1, h2, h3⟩ := drvN_out p hp
  rw [rwMask, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff,
    Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, h1⟩, h2⟩, h3⟩

theorem drvInvN_mask : (↑drvInvN : CoPset) ⊆ rwMask :=
  fun p hp => drvN_rw p (nclose_subseteq _ _ p hp)

theorem drvInvN_mask' : (↑drvInvN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN :=
  fun p hp => rwMask_sub p (drvInvN_mask p hp)

theorem callN_mask : (↑callN : CoPset) ⊆ rwMask \ ↑drvInvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨drvN_rw p (nclose_subseteq _ _ p hp),
    fun h' => ndot_ne_disjoint drvN (by decide : "call" ≠ "inv") p ⟨hp, h'⟩⟩

theorem callN_mask' : (↑callN : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN := by
  intro p hp
  have := callN_mask p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this ⊢
  exact ⟨rwMask_sub p this.1, this.2⟩

theorem drvE_out (p : Pos) (hp : p ∉ drvE) :
    p ∉ (↑srvRaftN : CoPset) ∧ p ∉ (↑kvN : CoPset) ∧ p ∉ (↑k8sN : CoPset) ∧
      p ∉ (↑drvN : CoPset) := by
  unfold drvE at hp
  simp only [Iris.Std.LawfulSet.mem_union, not_or] at hp
  exact ⟨hp.1.1.1, hp.1.1.2, hp.1.2, hp.2⟩

/-- Where `lintest`'s update fires, the instance's invariant and a call's open: inside the
store's updates. -/
theorem drvE_mask : ⊤ \ drvE ⊆ (rwMask \ ↑drvInvN) \ ↑callN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff] at hp
  obtain ⟨h1, h2, h3, h4⟩ := drvE_out p hp.2
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, rwMask,
    Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨⟨⟨CoPset.mem_full, h1⟩, h2⟩, h3⟩, fun h => h4 (nclose_subseteq _ _ p h)⟩,
    fun h => h4 (nclose_subseteq _ _ p h)⟩

/-- The same, inside the server's updates (`k8sAu1`'s, the reads'). -/
theorem drvE_mask' : ⊤ \ drvE ⊆ (((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑drvInvN) \ ↑callN := by
  intro p hp
  have := drvE_mask p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff] at this ⊢
  exact ⟨⟨rwMask_sub p this.1.1, this.1.2⟩, this.2⟩

/-- At the top, with the instance's invariant open. -/
theorem drvE_mask_top : ⊤ \ drvE ⊆ ⊤ \ ↑drvInvN := by
  intro p hp
  have := drvE_mask p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff] at this
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨CoPset.mem_full, this.1.2⟩

/-- **The library's abstract state** (`lintest`'s `libState`). -/
def kState (γ : KNames) (g0 : HSt) (S : linkv.PSet HSt Input) : IProp GF :=
  iprop(∃ h : List OpV, ghostVar γ.h (1 : Qp).half h ∗
    ⌜run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) h = some S⌝)

/-- **A pending write's token** (exclusive): the write `x` committed as pending under `n`. -/
def pendTok (γ : KNames) (n : Nat) (x : Input) : IProp GF :=
  ghostMapElem γ.p n (DFrac.own 1) x

instance pendTok_timeless (γ : KNames) (n : Nat) (x : Input) :
    Timeless (pendTok (GF := GF) γ n x) := by
  unfold pendTok; infer_instance

/-- The revisions' map at the state `σ`: its revision holds it, no later one is there, every state
in it is of `σ`'s history (stage 7e-4: a list's later pages read after its first). -/
def RevOk (Mr : GMap Nat KVState) (σ : KVState) : Prop :=
  Mr !! σ.rev = some σ ∧ (∀ n, σ.rev < n → Mr !! n = none) ∧
    ∀ n s, Mr !! n = some s → k8s.KvExt s σ

/-- **The revisions' states**, with the current one's element, read-only: a revision determines
the state. -/
def revOwn (γ : KNames) (σ : KVState) : IProp GF :=
  iprop(∃ Mr : GMap Nat KVState, ghostMapAuth γ.r 1 Mr ∗
    ghostMapElem γ.r σ.rev DFrac.discard σ ∗ ⌜RevOk Mr σ⌝)

instance revOwn_timeless (γ : KNames) (σ : KVState) : Timeless (revOwn (GF := GF) γ σ) := by
  unfold revOwn; infer_instance

/-- **One key under the prefix per revision** (persistent; the cached objects' clause, `Cache.lean`):
the history's entries at the revisions `1` to `n`, each changing at most one key under the store's
prefix. -/
def oneKeyRevs (c : StoreCfg GF DObj) (n : Nat) : IProp GF :=
  iprop(□ ∀ r : Nat, ⌜1 ≤ r ∧ r ≤ n⌝ → ∃ ch : Changes,
    ghostMapElem c.γh (W64 (r : Int)) DFrac.discard ch ∗
      ⌜((ch.map Prod.fst).filter (fun k => decide (c.pfx <+: k))).length ≤ 1⌝)

instance oneKeyRevs_persistent (c : StoreCfg GF DObj) (n : Nat) :
    Persistent (oneKeyRevs (GF := GF) c n) := by
  unfold oneKeyRevs; infer_instance

/-- **The store's history at etcd's state `σ`**: its authority (`histAuth`), every revision so
far changing one key under the prefix at most (`oneKeyRevs`). -/
def shistOwn (c : StoreCfg GF DObj) (σ : KVState) : IProp GF :=
  iprop(histAuth c.γh σ ∗ oneKeyRevs c σ.rev)

/-- The invariant's contents (see the file header). -/
def kInvBody (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames) : IProp GF :=
  iprop(∃ (h : List OpV) (S : linkv.PSet HSt Input) (σ : KVState) (M : GMap Nat Input) (nx : Nat),
    ghostVar γ.h (1 : Qp).half h ∗ etcdKV γk σ ∗ ghostMapAuth γ.p 1 M ∗ revOwn γ σ ∗
    shistOwn c σ ∗
    ⌜run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) h = some S ∧ KOk c g0 S σ M nx⌝)

instance kInvBody_timeless (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames) :
    Timeless (kInvBody (GF := GF) γ c g0 γk) := by
  unfold kInvBody shistOwn oneKeyRevs; infer_instance

/-- **The instance's invariant**. -/
def kInv (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames) : IProp GF :=
  iprop(inv drvInvN (kInvBody γ c g0 γk))

instance kInv_persistent (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames) :
    Persistent (kInv (GF := GF) γ c g0 γk) := by
  unfold kInv; infer_instance

/-- `kInv` reads only the KV state's ghost name (`kvSame`'s first part): the invariant at one
member's names is the invariant at any member's of the same cluster. -/
theorem kInv_same (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk γk' : KVNames)
    (hs : kvSame γk' γk) : kInv (GF := GF) γ c g0 γk' = kInv γ c g0 γk := by
  unfold kInv kInvBody etcdKV; rw [hs.1]

/-- One `kInv` at the cluster's KV names is one at every member's (`kInv_same`). -/
theorem kInvs_of_same (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (γk : KVNames)
    (ms : List (EtcdGrove.client.SrvAt GF)) (h : ∀ x ∈ ms, kvSame x.γr.kv γk) :
    kInv (GF := GF) γ c g0 γk ⊢ [∗list] sv ∈ ms, kInv γ c g0 sv.γr.kv := by
  induction ms with
  | nil => iintro _; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons y ys ih =>
    iintro #H
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · rw [kInv_same γ c g0 _ _ (h y (by simp))]; iexact H
    · iapply (ih (fun x hx => h x (List.mem_cons_of_mem _ hx))); iexact H

/-- **`lintest`'s linearization point** for the input `i`, the continuation `Φ`: the atomic
triple's update, its `▷` stripped. -/
def linU (γ : KNames) (g0 : HSt) (i : GoInterface) (Φ : val → IProp GF) : IProp GF :=
  iprop(|={⊤ \ drvE, ∅}=> ∃ S, kState γ g0 S ∗ ∀ S' o,
    (kState γ g0 S' ∗ ⌜(k8setcd3S (GF := GF) g0).M.step S (i, o) = some S'⌝) -∗
      |={∅, ⊤ \ drvE}=> ((k8setcd3S (GF := GF) g0).ioOk i o -∗ Φ #o))

/-- The continuation at the output `y`. -/
abbrev contAt (g0 : HSt) (x : Input) (y : Output) (Φ : val → IProp GF) : IProp GF :=
  iprop((k8setcd3S (GF := GF) g0).ioOk (boxIn x) (boxOut y) -∗ Φ #(boxOut y))

/-- **A write's call invariant** (`Delete`, `GuaranteedUpdate`; see the file header): `lintest`'s
update with a later credit, until the store hands the token `γt` back at its linearization
point. -/
def rwCall (γ : KNames) (g0 : HSt) (γt : GName) (x : Input) (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop((linU γ g0 (boxIn x) Φ ∗ £ 1) ∨ dghostVar γt (DFrac.own 1) ())

instance rwCall_persistent (γ : KNames) (g0 : HSt) (γt : GName) (x : Input)
    (Φ : val → IProp GF) : Persistent (rwCall γ g0 γt x Φ) := by
  unfold rwCall; infer_instance

/-- **A cached object** (`Cache.lean`): it fits a `DObj`, its resource version is not `0`, it has
no annotation (`objOf` sets none), and every key held it at that resource version. -/
def cachedObjOk (c : StoreCfg GF DObj) (ob : Obj) : IProp GF :=
  iprop(⌜fitsD ob ∧ ob.ResourceVersion' ≠ W64 0 ∧ ob.Annotated' = false⌝ ∗
    □ ∀ k : GoString, ⌜c.pfx <+: k⌝ → versionAt c k ob.ResourceVersion' (dobjOf ob))

instance cachedObjOk_persistent (c : StoreCfg GF DObj) (ob : Obj) :
    Persistent (cachedObjOk (GF := GF) c ob) := by
  unfold cachedObjOk; infer_instance

/-- **An answer's cached object** (persistent): an object answer with a name (`Apply` caches it) is
a cached object. -/
def ansOk (c : StoreCfg GF DObj) (y : Output) : IProp GF :=
  if y.Err' = W64 0 ∧ y.Name' ≠ [] then cachedObjOk c (cachedOf y) else iprop(True)

instance ansOk_persistent (c : StoreCfg GF DObj) (y : Output) :
    Persistent (ansOk (GF := GF) c y) := by
  unfold ansOk; split <;> infer_instance

/-- **A read's call invariant** (`Get`; see the file header): `lintest`'s update with a later
credit and the commit bit `γc` at `none`, or, once committed at a state `σ`, `γc` read-only at
`σ`, `σ` the state of its revision and that revision the one the client prophesied (`γp`, set
once by the maker `Get` calls), and the continuation, until `Apply` takes it with its token
`γt`. -/
def getCall (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (eD eU : GoInterface)
    (γc γt γp : GName) (x : Input) (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop(
    (linU γ g0 (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
    (∃ (σ : KVState) (R : w64), dghostVar γc DFrac.discard (some σ) ∗
      dghostVar γp DFrac.discard (some R) ∗ ⌜σ.rev = uint.nat R⌝ ∗
      ghostMapElem γ.r σ.rev DFrac.discard σ ∗
      ((contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∗ ansOk c (kStep eD eU x (c.abs σ)).2) ∨
        dghostVar γt (DFrac.own 1) ())))

instance getCall_persistent (γ : KNames) (c : StoreCfg GF DObj) (g0 : HSt) (eD eU : GoInterface)
    (γc γt γp : GName) (x : Input) (Φ : val → IProp GF) :
    Persistent (getCall γ c g0 eD eU γc γt γp x Φ) := by
  unfold getCall; infer_instance

/-- **A read's result** at a firing at `σ`: the state is the store's, with room, and, at the
prophesied revision `R`, the commit bit holds it. (Stage 7e-4: whatever the read's minimum resource
version `n`, now unused: below it the answer is `ETooLarge`, committed there too; drop `n` with
`call`/`Apply`.) -/
def readQ (c : StoreCfg GF DObj) (γc : GName) (n : Nat) (R : w64) (σ : KVState) : IProp GF :=
  iprop(⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗
    (⌜σ.rev = uint.nat R⌝ → dghostVar γc DFrac.discard (some σ)))

instance readQ_persistent (c : StoreCfg GF DObj) (γc : GName) (n : Nat) (R : w64)
    (σ : KVState) : Persistent (readQ c γc n R σ) := by
  unfold readQ; infer_instance

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
