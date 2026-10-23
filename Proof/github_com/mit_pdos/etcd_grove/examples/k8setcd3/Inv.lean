/-
Lean-first (no Rocq counterpart).

# k8setcd3: the library's abstract state over etcd, through the store (stage 6f)

As linkvtxn's `Inv.lean`, for the driver's model `k8setcd3S g0` (`pM (kSpec g0) decOp`) and the
store's specs (`Proof/k8s_io/apiserver/pkg/storage/etcd3/`).

## The pure part

- `kStep eD eU x ks`: the store's model (`KSt`) on the input `x` (its kind: `create` of the
  object `mkObj x`, `delete` with `validateFor`'s function `rejD`, `update` with `tryUpdateFor`'s
  `updD`, or `get`), its next state and the driver's output of its answer (`outOf`). On related
  states (`KRel`) it is the driver's model's step (`refine_step`, from 6b's `refine_*`).
- `KOk c g0 S σ M nx`: the instance's relation, as linkvtxn's `LinkvOk`: `S` closed under late
  effects, etcd's state the store's (`kvWf`) with room for two revisions, the pending writes `M`
  (inputs `Gen` may return, `InOk`) keyed below `nx`, and some configuration of `S` whose store
  the store's model of `σ` refines (`KRel (c.abs σ)`) with exactly `M`'s writes pending.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Refine
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8setcd3.Callbacks
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.History
public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Steps

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8setcd3

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode k8s
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8setcd3 (Input Output Obj item)
open go_etcd_io.etcd.server.v3.etcdserver

/-! ## The inputs are countable (the pending writes' ghost map) -/

section enc
variable [ext : FfiSyntax]

/-- An input, injectively. -/
def encIn (x : Input) : w64 × GoString × GoString × GoString × Bool × Bool :=
  (x.Kind', x.Key', x.Val', x.Reject', x.NoOp', x.IgnoreNotFound')

theorem encIn_inj : Function.Injective encIn := by
  intro a b h
  cases a; cases b
  simp only [encIn, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  subst h1 h2 h3 h4 h5 h6
  rfl

instance Input.countable : Pos.Countable Input :=
  .ofInjective (fun i => Pos.Countable.encode (encIn i))
    (fun _ _ h => encIn_inj (Pos.encode_inj h))

end enc

instance KVState.inhabited : Inhabited KVState := ⟨⟨[], 0⟩⟩

/-! ## Pure part -/

section pure
variable [ext : FfiSyntax]

/-- **An input `Gen` may return**, as far as the model needs: its name fits an object's. -/
def InOk (x : Input) : Prop := x.Key'.length < 256

/-- `call`'s object for a `Create` of `x` (`&Obj{Name: in.Key, Value: in.Val}`). -/
def mkObj (x : Input) : DObj :=
  if h : x.Key'.length < 256 then ⟨(x.Key', x.Val'), h⟩ else dzero

/-- **The store's model on the input `x`** (see the file header): its next state and the
driver's output of its answer. -/
def kStep (eD eU : GoInterface) (x : Input) (ks : KSt DObj) : KSt DObj × Output :=
  if x.Kind' = W64 0 then
    ((ks.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).1,
      outOf (ks.create (E := Empty) (mkeyL x.Key') (mkObj x) 0).2)
  else if x.Kind' = W64 1 then
    ((ks.delete (mkeyL x.Key') (fun _ _ => none) (rejD eD x.Reject')).1,
      outOf (ks.delete (mkeyL x.Key') (fun _ _ => none) (rejD eD x.Reject')).2)
  else if x.Kind' = W64 2 then
    ((ks.update (mkeyL x.Key') false dzero (fun _ _ => none) (updD eU x)).1,
      outOf (ks.update (mkeyL x.Key') false dzero (fun _ _ => none) (updD eU x)).2)
  else (ks, outOf (ks.get (E := Empty) (mkeyL x.Key') 0 x.IgnoreNotFound'))

/-- **The store's model refines the driver's on an input** (6b's `refine_*`). -/
theorem refine_step (eD eU : GoInterface) (ks : KSt DObj) (g : GSt) (h : KRel ks g) (x : Input)
    (hx : InOk x) (hrv : ks.rv + 1 < 2 ^ 64) :
    KRel (kStep eD eU x ks).1 (mstepL x g).1 ∧ (kStep eD eU x ks).2 = (mstepL x g).2 := by
  have hmk : mkObj x = ⟨(x.Key', x.Val'), hx⟩ := dif_pos hx
  unfold kStep mstepL
  by_cases h0 : x.Kind' = W64 0
  · simp only [h0, ↓reduceIte, hmk]
    exact refine_create ks g h x hx hrv
  by_cases h1 : x.Kind' = W64 1
  · simp only [h0, h1, ↓reduceIte]
    exact refine_delete ks g h x eD hrv
  by_cases h2 : x.Kind' = W64 2
  · simp only [h0, h1, h2, ↓reduceIte]
    exact refine_update ks g h x eU hrv
  simp only [h0, h1, h2, ↓reduceIte]
  exact ⟨h, refine_get ks g h x⟩

/-- **The driver's model never answers `EOther`**: its outputs are objects, "not found", "key
exists", the zero object or a rejection. -/
theorem mstepL_err (x : Input) (g : GSt) : (mstepL x g).2.Err' ≠ W64 4 := by
  unfold mstepL mcreateL mdeleteL mupdateL mgetL
  simp only [objOutL, existsL, notFoundL, rejectedL, zeroOutL]
  repeat' split
  all_goals simp

/-- An input's model answer, as porcupine's model decodes its output. -/
theorem ansOf_mstepL (x : Input) (g : GSt) : ansOf (mstepL x g).2 = .ok (mstepL x g).2 := by
  unfold ansOf
  rw [if_neg (mstepL_err x g)]

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

end pure

section rel
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- **The instance's relation** (see the file header). -/
structure KOk (c : StoreCfg GF DObj) (g0 : GSt) (S : linkv.PSet GSt Input) (σ : KVState)
    (M : GMap Nat Input) (nx : Nat) : Prop where
  closed : linkv.PSet.Closed (kSpec g0) S
  wf : kvWf c σ
  room : σ.rev + 2 < 2 ^ 63
  fresh : ∀ n, nx ≤ n → M !! n = none
  ins : ∀ n i, M !! n = some i → InOk i
  cfg : ∃ cf, S cf ∧ KRel (c.abs σ) cf.st ∧ (pendIns M).Perm cf.pend

variable {c : StoreCfg GF DObj} {g0 : GSt}

/-- The relation at the start: the model's initial state, nothing pending. -/
theorem kOk_init (σ : KVState) (hw : kvWf c σ) (hr : σ.rev + 2 < 2 ^ 63)
    (he : KRel (c.abs σ) g0) : KOk c g0 (linkv.pInit (kSpec g0)) σ (∅ : GMap Nat Input) 0 := by
  refine ⟨linkv.pInit_closed, hw, hr, fun _ _ => rfl, (fun _ _ h => by cases h),
    ⟨⟨g0, []⟩, rfl, he, ?_⟩⟩
  simp [pendIns]

/-- **An operation answered at the real configuration**: the store's model of `σ` stepped by
the input to the store's model of `σ'`, which has room. -/
theorem kOk_ok {S : linkv.PSet GSt Input} {σ σ' : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) (eD eU : GoInterface) (x : Input) (hx : InOk x)
    (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1) (hw' : kvWf c σ')
    (hr' : σ'.rev + 2 < 2 ^ 63) :
    ∃ S', (linkv.pSeq (kSpec g0)).step S (x, .ok (kStep eD eU x (c.abs σ)).2) = some S' ∧
      KOk c g0 S' σ' M nx := by
  obtain ⟨cf, hc, hrel, hp⟩ := H.cfg
  have hrv : (c.abs σ).rv + 1 < 2 ^ 64 := by rw [abs_rv]; have := H.room; omega
  obtain ⟨hrel', hout⟩ := refine_step eD eU _ _ hrel x hx hrv
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_ok (P := kSpec g0) hc x
  refine ⟨S', ?_, linkv.pSeq_step_closed hS', hw', hr', H.fresh, H.ins, ⟨_, hc', ?_, hp⟩⟩
  · rw [hout]; exact hS'
  · rw [habs]; exact hrel'

/-- A write committed as pending, its token minted at `nx`. -/
theorem kOk_errW {S : linkv.PSet GSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) (x : Input) (hw : isWriteL x = true) (hx : InOk x) :
    ∃ S', (linkv.pSeq (kSpec g0)).step S (x, .err) = some S' ∧
      KOk c g0 S' σ (GMap.insert nx x M) (nx + 1) := by
  obtain ⟨cf, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errW_pending (P := kSpec g0) hc x hw
  refine ⟨S', hS', linkv.pSeq_step_closed hS', H.wf, H.room, ?_, ?_, ⟨_, hc', hst, ?_⟩⟩
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
      exact hx
    · have : (GMap.insert nx x M) !! n = M !! n := GMap.lookup_insert_ne _ _ e
      rw [this] at hn
      exact H.ins n j hn
  · exact (pendIns_insert M nx x (H.fresh nx (Nat.le_refl _))).trans (hp.cons _)

/-- A read that failed. -/
theorem kOk_errR {S : linkv.PSet GSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) (x : Input) (hw : isWriteL x = false) :
    ∃ S', (linkv.pSeq (kSpec g0)).step S (x, .err) = some S' ∧ KOk c g0 S' σ M nx := by
  obtain ⟨cf, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errR (P := kSpec g0) hc x hw
  exact ⟨S', hS', linkv.pSeq_step_closed hS', H.wf, H.room, H.fresh, H.ins, ⟨cf, hc', hst, hp⟩⟩

/-- **A late effect**: the pending write `n ↦ x` takes effect, the model state unchanged. -/
theorem kOk_pend {S : linkv.PSet GSt Input} {σ σ' : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) (eD eU : GoInterface) (n : Nat) (x : Input) (hn : M !! n = some x)
    (habs : c.abs σ' = (kStep eD eU x (c.abs σ)).1) (hw' : kvWf c σ')
    (hr' : σ'.rev + 2 < 2 ^ 63) :
    KOk c g0 S σ' (GMap.delete n M) nx := by
  obtain ⟨cf, hc, hst, hp⟩ := H.cfg
  have hd := pendIns_delete M n x hn
  have hmem : x ∈ cf.pend := hp.subset (hd.symm.subset List.mem_cons_self)
  have hrv : (c.abs σ).rv + 1 < 2 ^ 64 := by rw [abs_rv]; have := H.room; omega
  obtain ⟨hrel', -⟩ := refine_step eD eU _ _ hst x (H.ins n x hn) hrv
  refine ⟨H.closed, hw', hr', ?_, ?_, ⟨_, H.closed.apply hc hmem, ?_, ?_⟩⟩
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
  · show KRel (c.abs σ') (mstepL x cf.st).1
    rw [habs]; exact hrel'
  · refine List.Perm.cons_inv ((hd.symm.trans hp).trans ?_)
    exact List.perm_cons_erase hmem

/-- A firing that leaves etcd's state as it was. -/
theorem kOk_same {S : linkv.PSet GSt Input} {σ : KVState} {M : GMap Nat Input} {nx : Nat}
    (H : KOk c g0 S σ M nx) : KOk c g0 S σ M nx := H

end rel

/-! ## The ghost state and the invariant -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8setcd3.Assumptions]
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
def kState (γ : KNames) (g0 : GSt) (S : linkv.PSet GSt Input) : IProp GF :=
  iprop(∃ h : List OpV, ghostVar γ.h (1 : Qp).half h ∗
    ⌜run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) h = some S⌝)

/-- **A pending write's token** (exclusive): the write `x` committed as pending under `n`. -/
def pendTok (γ : KNames) (n : Nat) (x : Input) : IProp GF :=
  ghostMapElem γ.p n (DFrac.own 1) x

/-- The revisions' map at the state `σ`: its revision holds it, no later one is there. -/
def RevOk (Mr : GMap Nat KVState) (σ : KVState) : Prop :=
  Mr !! σ.rev = some σ ∧ ∀ n, σ.rev < n → Mr !! n = none

/-- **The revisions' states**, with the current one's element, read-only: a revision determines
the state. -/
def revOwn (γ : KNames) (σ : KVState) : IProp GF :=
  iprop(∃ Mr : GMap Nat KVState, ghostMapAuth γ.r 1 Mr ∗
    ghostMapElem γ.r σ.rev DFrac.discard σ ∗ ⌜RevOk Mr σ⌝)

instance revOwn_timeless (γ : KNames) (σ : KVState) : Timeless (revOwn (GF := GF) γ σ) := by
  unfold revOwn; infer_instance

/-- The invariant's contents (see the file header). -/
def kInvBody (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames) : IProp GF :=
  iprop(∃ (h : List OpV) (S : linkv.PSet GSt Input) (σ : KVState) (M : GMap Nat Input) (nx : Nat),
    ghostVar γ.h (1 : Qp).half h ∗ etcdKV γk σ ∗ ghostMapAuth γ.p 1 M ∗ revOwn γ σ ∗
    histAuth c.γh σ ∗
    ⌜run (k8setcd3S (GF := GF) g0).M (linkv.pInit (kSpec g0)) h = some S ∧ KOk c g0 S σ M nx⌝)

instance kInvBody_timeless (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames) :
    Timeless (kInvBody (GF := GF) γ c g0 γk) := by
  unfold kInvBody; infer_instance

/-- **The instance's invariant**; the server's workload lets the store deposit every
operation. -/
def kInv (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames) : IProp GF :=
  iprop(⌜∀ op, γk.wl.writes op⌝ ∗ inv drvInvN (kInvBody γ c g0 γk))

instance kInv_persistent (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (γk : KVNames) :
    Persistent (kInv (GF := GF) γ c g0 γk) := by
  unfold kInv; infer_instance

/-- **`lintest`'s linearization point** for the input `i`, the continuation `Φ`: the atomic
triple's update, its `▷` stripped. -/
def linU (γ : KNames) (g0 : GSt) (i : GoInterface) (Φ : val → IProp GF) : IProp GF :=
  iprop(|={⊤ \ drvE, ∅}=> ∃ S, kState γ g0 S ∗ ∀ S' o,
    (kState γ g0 S' ∗ ⌜(k8setcd3S (GF := GF) g0).M.step S (i, o) = some S'⌝) -∗
      |={∅, ⊤ \ drvE}=> ((k8setcd3S (GF := GF) g0).ioOk i o -∗ Φ #o))

/-- The continuation at the output `y`. -/
abbrev contAt (g0 : GSt) (x : Input) (y : Output) (Φ : val → IProp GF) : IProp GF :=
  iprop((k8setcd3S (GF := GF) g0).ioOk (boxIn x) (boxOut y) -∗ Φ #(boxOut y))

/-- **A write's call invariant** (`Delete`, `GuaranteedUpdate`; see the file header): `lintest`'s
update with a later credit, until the store hands the token `γt` back at its linearization
point. -/
def rwCall (γ : KNames) (g0 : GSt) (γt : GName) (x : Input) (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop((linU γ g0 (boxIn x) Φ ∗ £ 1) ∨ dghostVar γt (DFrac.own 1) ())

instance rwCall_persistent (γ : KNames) (g0 : GSt) (γt : GName) (x : Input)
    (Φ : val → IProp GF) : Persistent (rwCall γ g0 γt x Φ) := by
  unfold rwCall; infer_instance

/-- **A read's call invariant** (`Get`; see the file header): `lintest`'s update with a later
credit and the commit bit `γc` at `none`, or, once committed at a state `σ`, `γc` read-only at
`σ`, `σ` the state of its revision and that revision the one the client prophesied (`γp`, set
once by the maker `Get` calls), and the continuation, until `Apply` takes it with its token
`γt`. -/
def getCall (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (eD eU : GoInterface)
    (γc γt γp : GName) (x : Input) (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop(
    (linU γ g0 (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
    (∃ (σ : KVState) (R : w64), dghostVar γc DFrac.discard (some σ) ∗
      dghostVar γp DFrac.discard (some R) ∗ ⌜σ.rev = uint.nat R⌝ ∗
      ghostMapElem γ.r σ.rev DFrac.discard σ ∗
      (contAt g0 x (kStep eD eU x (c.abs σ)).2 Φ ∨ dghostVar γt (DFrac.own 1) ())))

instance getCall_persistent (γ : KNames) (c : StoreCfg GF DObj) (g0 : GSt) (eD eU : GoInterface)
    (γc γt γp : GName) (x : Input) (Φ : val → IProp GF) :
    Persistent (getCall γ c g0 eD eU γc γt γp x Φ) := by
  unfold getCall; infer_instance

/-- **A read's result** at a firing at `σ`: the state is the store's, with room, and, at the
prophesied revision `R`, the commit bit holds it. -/
def readQ (c : StoreCfg GF DObj) (γc : GName) (R : w64) (σ : KVState) : IProp GF :=
  iprop(⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗
    (⌜σ.rev = uint.nat R⌝ → dghostVar γc DFrac.discard (some σ)))

instance readQ_persistent (c : StoreCfg GF DObj) (γc : GName) (R : w64) (σ : KVState) :
    Persistent (readQ c γc R σ) := by
  unfold readQ; infer_instance

end defs

end k8setcd3
end EtcdGrove
end Perennial
