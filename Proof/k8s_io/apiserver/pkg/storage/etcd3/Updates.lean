/-
Lean-first (no Rocq counterpart).

# The store's atomic updates (D30h, `notes/k8s-etcd3-plan.md` phase 4)

- `k8sAu1 γk c step Φ`: the caller's update for an operation that writes, fired at most once: at a
  state of the store `σ` (`kvWf`, with room for one more revision), the next state is any state of
  the store whose model is the model's `step`'s (`∀∀ σ'`: the store chooses it, the transaction it
  sends), and the caller learns `Φ σ`. Relational, since the caller cannot name the transaction:
  its value is the transformer's (encryption may be randomized).
- `KvNext σ σ'`: what a firing tells of etcd's next state beyond its model, for the caller's
  history (`kvSeen`, D30j): the state is kept, or moves to the next revision, every new key-value
  at that revision (`kvNext_step`: any operation's step).
- `k8sAu1_kvAu1`: such an update gives the client's update (`kvAu1`) for a transaction whose step
  keeps the store's states and moves the model as `step` (`StepOk`), whose result also says the
  state it fired at was the store's.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Store

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]
variable {Obj : Type} [DecidableEq Obj]

/-- **A step of etcd's state, for the caller's history** (see the file header). -/
def KvNext (σ σ' : KVState) : Prop :=
  σ' = σ ∨ (σ'.rev = σ.rev + 1 ∧ ∀ v ∈ σ'.kvs, v ∈ σ.kvs ∨ v.modRev = W64 ((σ'.rev : Nat) : Int))

/-- A commit is such a step. -/
theorem kvNext_commit (σ : KVState) (cs : List mvcc.Change) : KvNext σ (σ.commit cs) := by
  unfold KVState.commit
  split
  · exact Or.inl rfl
  · refine Or.inr ⟨rfl, fun v hv => ?_⟩
    by_cases hm : v.modRev = W64 ((σ.rev + 1 : Nat) : Int)
    · exact Or.inr hm
    · exact Or.inl (txn.mem_applyChanges_modRev cs _ v hv hm)

/-- **Any key-value operation's step is such a step** (unit T3: a lease's grant changes the state
at the same revision). -/
theorem kvNext_step (op : KVOp) (σ : KVState) (hop : op.isKV) : KvNext σ (kvOpStep op σ) := by
  cases op with
  | put o =>
    simp only [kvOpStep]
    split
    · exact Or.inl rfl
    split
    · exact Or.inl rfl
    · exact kvNext_commit _ _
  | range o => exact Or.inl rfl
  | deleteRange o => exact kvNext_commit _ _
  | txn t =>
    simp only [kvOpStep]
    split
    · exact kvNext_commit _ _
    · exact Or.inl rfl
  | leaseGrant _ _ => exact hop.elim
  | leaseRevoke _ => exact hop.elim

/-- **The caller's update for a write** (see the file header). -/
def k8sAu1 (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj)
    (Φ : KVState → IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ (σ : KVState), etcdKV γk σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ }>
      @ (⊤ \ ↑srvRaftN) \ ↑kvN, ∅
    <{ ∀∀ (σ' : KVState), etcdKV γk σ' ∗ ⌜kvWf c σ' ∧ c.abs σ' = step (c.abs σ) ∧ KvNext σ σ'⌝,
      COMM Φ σ }>)

/-- **A transaction's step is the model's** at the store's states (with room for a revision). -/
def StepOk (c : StoreCfg GF Obj) (op : KVOp) (step : KSt Obj → KSt Obj) : Prop :=
  ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 →
    kvWf c (kvOpStep op σ) ∧ c.abs (kvOpStep op σ) = step (c.abs σ)

/-- **The caller's update gives the client's** for a transaction whose step is the model's. -/
theorem k8sAu1_kvAu1 (γk : KVNames) (c : StoreCfg GF Obj) (op : KVOp)
    (step : KSt Obj → KSt Obj) (Φ : KVState → IProp GF) (h : StepOk c op step) (hop : op.isKV) :
    k8sAu1 γk c step Φ ⊢
      kvAu1 γk (kvOpStep op)
        (fun σ => iprop(Φ σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ)) := by
  unfold kvAu1
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, HAU⟩
  unfold k8sAu1
  ihave HAC := aupd_aacc $$ HAU
  iunfold atomic_acc at HAC
  unfold atomic_acc
  imod HAC with HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  icases HAC with ⟨%σ, ⟨Hkv, %Hwf, #Hseen⟩, Hcl⟩
  imodintro
  iexists σ
  iframe Hkv
  isplit
  · iintro Hkv
    icases Hcl with ⟨Habort, -⟩
    iapply Habort
    iframe Hkv Hseen
    ipureintro; exact Hwf
  · iintro Hkv
    icases Hcl with ⟨-, Hcommit⟩
    obtain ⟨hwf', habs⟩ := h σ Hwf.1 Hwf.2
    ispecialize Hcommit $$ %(kvOpStep op σ)
    imod Hcommit $$ [Hkv] with HΦ
    · iframe Hkv
      ipureintro; exact ⟨hwf', habs, kvNext_step op σ hop⟩
    imodintro
    iframe HΦ Hseen
    ipureintro; exact Hwf


/-! ## Operations that may write: `Delete`, `GuaranteedUpdate` (D30n) -/

/-- The store's namespace: its first read's invariant (`rwInv`). -/
def k8sN : Namespace := nroot .@ "k8sStore"

theorem k8sN_mask : (↑k8sN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

/-- The mask of the caller's updates for operations that may write: the client's, without the
store's namespace (the store opens its invariant around them). -/
abbrev rwMask : CoPset := ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑k8sN

theorem rwMask_sub : rwMask ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff] at hp
  exact hp.1

/-- **The caller's update for an operation that may write** (persistent; D30l, D30n): it fires
any number of times as a plain read (`b = false`: the state unchanged, nothing committed), and
once as the operation's linearization point (`b = true`), handing the caller's token `W` back:
the next state's model is the model's `step` (the write; or, at a state where the step is the
identity, a read-like answer, the state unchanged), and the caller learns `Φ σ`. Once `W` is
handed, the store fires it as a plain read only. -/
def k8sAuRW (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj) (W : IProp GF)
    (Φ : KVState → IProp GF) : IProp GF :=
  iprop(□ AU <{ ∃∃ (σ : KVState), etcdKV γk σ ∗ ⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ }>
      @ rwMask, ∅
    <{ ∀∀ (b : Bool) (σ' : KVState), etcdKV γk σ' ∗
        (if b then W ∗ ⌜kvWf c σ' ∧ c.abs σ' = step (c.abs σ) ∧ KvNext σ σ'⌝ else ⌜σ' = σ⌝),
      COMM if b then Φ σ else iprop(True) }>)

instance k8sAuRW_persistent (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj)
    (W : IProp GF) (Φ : KVState → IProp GF) : Persistent (k8sAuRW γk c step W Φ) := by
  unfold k8sAuRW; infer_instance

/-- What a read through `k8sAuRW` learns of the state it fired at: the store's, with room for a
revision, and seen in the history. -/
def rdFacts (c : StoreCfg GF Obj) (σ : KVState) : IProp GF :=
  iprop(⌜kvWf c σ ∧ σ.rev + 2 < 2 ^ 63⌝ ∗ kvSeen c.γh σ)

instance rdFacts_persistent (c : StoreCfg GF Obj) (σ : KVState) :
    Persistent (rdFacts c σ) := by
  unfold rdFacts; infer_instance

/-- **A conditional transaction's update, from the caller's** (see the file header): at a state
of the store where `A` holds (what the store's history `kvSeen` tells, `HA`), the transaction's
step is the model's when it succeeds (`ok σ`) and the identity when it fails; it fires the
caller's update as the linearization point when it succeeds, or when it fails at a state whose
model step is the identity and the store hands `W` there (`hand σ`, a read-like answer), and as a
plain read otherwise, keeping `W`. -/
theorem k8sAuRW_kvAu1 (γk : KVNames) (c : StoreCfg GF Obj) (step : KSt Obj → KSt Obj)
    (W : IProp GF) (Φ : KVState → IProp GF) (op : KVOp) (hop : op.isKV) (ok hand : KVState → Bool)
    (A : KVState → Prop)
    (h : ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → A σ →
      (ok σ = true → kvWf c (kvOpStep op σ) ∧ c.abs (kvOpStep op σ) = step (c.abs σ)) ∧
      (ok σ = false → kvOpStep op σ = σ ∧ (hand σ = true → step (c.abs σ) = c.abs σ))) :
    k8sAuRW γk c step W Φ ∗ W ∗ □ (∀ σ, kvSeen c.γh σ -∗ ⌜A σ⌝) ⊢
      kvAu1 γk (kvOpStep op) (fun σ => iprop((if ok σ || hand σ then Φ σ else W) ∗
        rdFacts c σ ∗ ⌜A σ⌝)) := by
  unfold kvAu1
  refine (BI.and_intro BI.true_intro .rfl).trans (aupd_intro ?_)
  iintro ⟨-, #HAU0, HW, #HA⟩
  ihave #HAU := HAU0
  iunfold k8sAuRW at HAU
  ihave #HAU' := atomic_update_mask_weaken rwMask_sub $$ HAU
  ihave HAC := aupd_aacc $$ HAU'
  iunfold atomic_acc at HAC
  unfold atomic_acc
  imod HAC with HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down] at HAC
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  icases HAC with ⟨%σ, ⟨Hkv, %Hwf, #Hseen⟩, Hcl⟩
  ihave %HAσ := HA $$ %σ Hseen
  have hst := h σ Hwf.1 Hwf.2 HAσ
  imodintro
  iexists σ
  iframe Hkv
  isplit
  · iintro Hkv
    icases Hcl with ⟨Habort, -⟩
    imod Habort $$ [Hkv] with -
    · iframe Hkv Hseen
      ipureintro; exact Hwf
    imodintro
    iframe HAU0 HW HA
  · icases Hcl with ⟨-, Hcommit⟩
    cases hok : ok σ
    · obtain ⟨hid, hhand⟩ := hst.2 hok
      rw [hid]
      iintro Hkv
      cases hh : hand σ
      · ispecialize Hcommit $$ %false %σ
        isimp only [Bool.false_eq_true, ↓reduceIte] at Hcommit
        imod Hcommit $$ [Hkv] with -
        · iframe Hkv
        imodintro
        simp only [Bool.false_or, Bool.false_eq_true, ↓reduceIte]
        iframe HW
        unfold rdFacts
        iframe Hseen
        ipureintro; exact ⟨Hwf, HAσ⟩
      · ispecialize Hcommit $$ %true %σ
        isimp only [↓reduceIte] at Hcommit
        imod Hcommit $$ [Hkv HW] with HΦ
        · iframe Hkv HW
          ipureintro; exact ⟨Hwf.1, (hhand hh).symm, Or.inl rfl⟩
        imodintro
        simp only [Bool.false_or, ↓reduceIte]
        iframe HΦ
        unfold rdFacts
        iframe Hseen
        ipureintro; exact ⟨Hwf, HAσ⟩
    · obtain ⟨hwf', habs⟩ := hst.1 hok
      iintro Hkv
      ispecialize Hcommit $$ %true %(kvOpStep op σ)
      isimp only [↓reduceIte] at Hcommit
      imod Hcommit $$ [Hkv HW] with HΦ
      · iframe Hkv HW
        ipureintro; exact ⟨hwf', habs, kvNext_step op σ hop⟩
      imodintro
      simp only [Bool.true_or, ↓reduceIte]
      iframe HΦ
      unfold rdFacts
      iframe Hseen
      ipureintro; exact ⟨Hwf, HAσ⟩

/-- **The caller's updates at the members and its token give the client's updates** for a
conditional transaction (`k8sAuRW_kvAu1` at each member). -/
theorem k8sAusRW_kvAu1 (ms : List (client.SrvAt GF)) (c : StoreCfg GF Obj)
    (step : KSt Obj → KSt Obj) (W : IProp GF) (Φ : KVState → IProp GF) (op : KVOp) (hop : op.isKV)
    (ok hand : KVState → Bool) (A : KVState → Prop) (hw : ∀ x ∈ ms, x.γr.kv.wl.writes op)
    (h : ∀ σ, kvWf c σ → σ.rev + 2 < 2 ^ 63 → A σ →
      (ok σ = true → kvWf c (kvOpStep op σ) ∧ c.abs (kvOpStep op σ) = step (c.abs σ)) ∧
      (ok σ = false → kvOpStep op σ = σ ∧ (hand σ = true → step (c.abs σ) = c.abs σ))) :
    (W ∗ □ (∀ σ, kvSeen c.γh σ -∗ ⌜A σ⌝)) ∗ ([∗list] x ∈ ms, k8sAuRW x.γr.kv c step W Φ) ⊢
      [∧list] x ∈ ms, kvOpAu1 x.γr.kv op (fun σ => iprop((if ok σ || hand σ then Φ σ else W) ∗
        rdFacts c σ ∗ ⌜A σ⌝)) := by
  apply client.bigAndL_of_sep ms _ (fun x => k8sAuRW x.γr.kv c step W Φ)
  intro x hx
  iintro ⟨⟨HW, #HA⟩, #Hx⟩
  unfold kvOpAu1
  isplitr
  · ipureintro; exact hw x hx
  iapply k8sAuRW_kvAu1 x.γr.kv c step W Φ op hop ok hand A h
  iframe Hx HW HA

end defs

end k8s
end EtcdGrove
end Perennial
