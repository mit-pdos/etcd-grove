/-
Lean-first (no Rocq counterpart).

# linkvtxn: the library's abstract state over etcd's KV (linkv-txn stage F)

What `Apply`'s spec (`Spec/.../linkvtxn/Apply.lean`) is stated with, and the ghost steps its proof
takes at the linearization points: `linkv/Inv.lean`'s, for every kind of operation and the model
`pM TS decOp` (`linkvtxnS`).

## The state

`lintest`'s `libState` is `linkvState γ S`: half of a ghost variable at `γ.h` holding the history
`h`, with `S` the model state `run` reaches from it. The other half is in the instance's invariant
`linkvInv γ γk` (at `linkvInvN`), with the server's `etcdKV γk σ`, the authority of the **pending
writes** `M` (a ghost map, `γ.p`, of model inputs: the failed writes committed as pending, whose
update the server has not yet fired) and the **revisions' states** (`revOwn`: every revision the
state had to the state, a ghost map at `γ.r`). `LinkvOk S σ M nx` relates them: some configuration
`c` of `S` is the server's state (`c.st = linkv.absSt σ`) with exactly `M`'s writes pending,
`S` is closed under late effects, the state is good (`GoodKV`: sorted, its keys the workload's),
the pending writes are of the workload's keys, and the keys of `M` are below `nx`.

## The steps (the commits of `Apply`'s cases)

`linU γ i Φ` is `lintest`'s linearization point (the atomic triple's update, its `▷` stripped).
An operation's input is a boxed `Input` `x` decoding to `i` (`decIn x = some i`); its answer, as
`call` builds it, is `outAt i σ` (`outOf` of the model's answer at the state `σ` it ran at).

- `write_ok_au`: a write whose prophecy says `ok` hands the server an update fired at most once
  (`kvOpAu1`) that commits `lintest`'s update at the firing with the output `outAt i σ`, leaving
  the continuation as its result (`wQ`). The output's revision must fit a word for the model to
  decode it; at a state where it does not (which a reply excludes: its log is below `2^63`), the
  update commits the write as failed and applied (`pSeq_errW_applied`), its result saying so.
- `write_err_commit`: a write whose prophecy says error commits at once, as pending (output
  `errOut`), minting the pending write's token; `write_pend_au` is the update the server is
  handed: at its firing (during the call, after it, or never) the pending write takes effect.
- `read_err_commit`: a read whose prophecy says error commits at once.
- `read_ok_au`: a read (get, list, read-only transaction) whose prophecies say `ok` at revision
  `R`: the persistent read update. Its commit-once state is the call invariant `callInv` (at
  `callN`): `lintest`'s update with a later credit and the commit bit `γc` at `none`, or, once
  committed at a state `σ` of revision `R`, `γc` read-only at `σ` and the continuation (until
  `Apply` takes it with its token: `callInv_take`). A firing at a state of revision `R` sees the
  same state as the commit did (the revisions' map: a state's revision determines it, every step
  keeping the state or moving to the next revision, `kvOpStep_cases`). The read's result `readQ`
  says the state is good and, at revision `R`, the bit holds it.
- `linkvInv_alloc`: the invariant and `linkvState γ (pInit TS)`, from `etcdKV` at a good state
  that is the model's initial one.

The invariant's namespace is `linkvInvN`, the call invariants' `callN`, both under `linkvN` (in
`Apply`'s mask `linkvE`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkvtxn.Enc
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkvtxn

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.linkvtxn

/-! ## The model inputs are countable (the pending writes' ghost map) -/

/-- A comparison, injectively. -/
def encCmp : linkv.MCmp GoString GoString → (GoString × GoString) ⊕ (GoString × w64) ⊕ (GoString × w64)
  | .val k v => .inl (k, v)
  | .ver k n => .inr (.inl (k, n))
  | .mod k n => .inr (.inr (k, n))

/-- A transaction operation, injectively. -/
def encTOp : linkv.MOp GoString GoString → GoString ⊕ (GoString × GoString) ⊕ GoString
  | .get k => .inl k
  | .put k v => .inr (.inl (k, v))
  | .del k => .inr (.inr k)

/-- A model input, injectively. -/
def encMI : MI → GoString ⊕ Unit ⊕ (GoString × GoString) ⊕ GoString ⊕
    (List ((GoString × GoString) ⊕ (GoString × w64) ⊕ (GoString × w64)) ×
      List (GoString ⊕ (GoString × GoString) ⊕ GoString) ×
      List (GoString ⊕ (GoString × GoString) ⊕ GoString))
  | .get k => .inl k
  | .list => .inr (.inl ())
  | .put k v => .inr (.inr (.inl (k, v)))
  | .del k => .inr (.inr (.inr (.inl k)))
  | .txn cs t e => .inr (.inr (.inr (.inr (cs.map encCmp, t.map encTOp, e.map encTOp))))

theorem encCmp_inj : Function.Injective encCmp := by
  intro a b h
  cases a <;> cases b <;> simp_all [encCmp]

theorem encTOp_inj : Function.Injective encTOp := by
  intro a b h
  cases a <;> cases b <;> simp_all [encTOp]

theorem map_inj_of_inj {α β : Type} {f : α → β} (hf : Function.Injective f) :
    ∀ {l l' : List α}, l.map f = l'.map f → l = l'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | a :: l, b :: l', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [hf h.1, map_inj_of_inj hf h.2]

theorem encMI_inj : Function.Injective encMI := by
  intro a b h
  cases a <;> cases b <;> simp only [encMI, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
    Prod.mk.injEq] at h
  all_goals first
    | rfl
    | (subst_vars; rfl)
    | (obtain ⟨h1, h2⟩ := h; subst h1 h2; rfl)
    | skip
  case txn.txn cs t e cs' t' e' =>
    obtain ⟨h1, h2, h3⟩ := h
    rw [map_inj_of_inj encCmp_inj h1, map_inj_of_inj encTOp_inj h2, map_inj_of_inj encTOp_inj h3]

instance MI.countable : Pos.Countable MI :=
  .ofInjective (fun i => Pos.Countable.encode (encMI i))
    (fun _ _ h => encMI_inj (Pos.encode_inj h))

instance KVState.inhabited : Inhabited KVState := ⟨⟨0, ∅, []⟩⟩

/-! ## Pure part -/

section pure
variable [GooseExts]

/-- The pending writes (in some order). -/
def pendIns (M : GMap Nat MI) : List MI := M.toList.map Prod.snd

theorem pendIns_insert (M : GMap Nat MI) (n : Nat) (i : MI) (h : M !! n = none) :
    (pendIns (GMap.insert n i M)).Perm (i :: pendIns M) := by
  unfold pendIns
  have hp := Iris.Std.LawfulFiniteMap.toList_insert (M := GMap Nat) (m := M) (k := n) (v := i) h
  exact hp.map Prod.snd

theorem pendIns_delete (M : GMap Nat MI) (n : Nat) (i : MI) (h : M !! n = some i) :
    (pendIns M).Perm (i :: pendIns (GMap.delete n M)) := by
  unfold pendIns
  have hp := Iris.Std.LawfulFiniteMap.toList_delete (M := GMap Nat) (m := M) (k := n) (v := i) h
  exact hp.map Prod.snd

/-- **The invariant's relation** (see the file header). -/
structure LinkvOk (S : linkv.PSet MS MI) (σ : KVState) (M : GMap Nat MI) (nx : Nat) : Prop where
  closed : linkv.PSet.Closed TS S
  good : GoodKV σ
  fresh : ∀ n, nx ≤ n → M !! n = none
  keys : ∀ n i, M !! n = some i → i.KeysIn wks
  cfg : ∃ c, S c ∧ c.st = linkv.absSt σ ∧ (pendIns M).Perm c.pend

/-- **`call`'s output** for the model input `i` at the state `σ` (see the file header). -/
def outAt (i : MI) (σ : KVState) : Output := outOf (linkv.mStep wks i (linkv.absSt σ)).2

/-- The relation at the start: the model's initial state, nothing pending. -/
theorem linkvOk_init (σ : KVState) (hg : GoodKV σ) (he : linkv.absSt σ = TS.init) :
    LinkvOk (linkv.pInit TS) σ (∅ : GMap Nat MI) 0 := by
  refine ⟨linkv.pInit_closed, hg, fun _ _ => rfl, (fun _ _ h => by cases h),
    ⟨⟨TS.init, []⟩, rfl, he.symm, ?_⟩⟩
  simp [pendIns]

/-- An operation that returned its answer, at the real configuration: the state stepped. -/
theorem linkvOk_ok {S : linkv.PSet MS MI} {σ : KVState} {M : GMap Nat MI} {nx : Nat}
    (H : LinkvOk S σ M nx) (i : MI) (hi : i.KeysIn wks) :
    ∃ S', (linkv.pSeq TS).step S (i, .ok (linkv.mStep wks i (linkv.absSt σ)).2) = some S' ∧
      LinkvOk S' (kvOpStep (opIn i) σ) M nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_ok (P := TS) hc i
  rw [hst] at hS' hc'
  refine ⟨S', hS', linkv.pSeq_step_closed hS', goodKV_step σ H.good i hi, H.fresh, H.keys,
    ⟨_, hc', ?_, hp⟩⟩
  exact (absSt_step σ H.good i).symm

/-- A read that returned its answer: the state unchanged. -/
theorem linkvOk_read {S : linkv.PSet MS MI} {σ : KVState} {M : GMap Nat MI} {nx : Nat}
    (H : LinkvOk S σ M nx) (i : MI) (hw : i.isWrite = false) :
    ∃ S', (linkv.pSeq TS).step S (i, .ok (linkv.mStep wks i (linkv.absSt σ)).2) = some S' ∧
      LinkvOk S' σ M nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_ok (P := TS) hc i
  rw [hst] at hS' hc'
  refine ⟨S', hS', linkv.pSeq_step_closed hS', H.good, H.fresh, H.keys, ⟨_, hc', ?_, hp⟩⟩
  exact linkv.mStep_read wks i _ hw

/-- A write that failed, applied at the commit: the state stepped. -/
theorem linkvOk_errApplied {S : linkv.PSet MS MI} {σ : KVState} {M : GMap Nat MI} {nx : Nat}
    (H : LinkvOk S σ M nx) (i : MI) (hw : i.isWrite = true) (hi : i.KeysIn wks) :
    ∃ S', (linkv.pSeq TS).step S (i, .err) = some S' ∧
      LinkvOk S' (kvOpStep (opIn i) σ) M nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errW_applied (P := TS) hc i hw
  rw [hst] at hc'
  refine ⟨S', hS', linkv.pSeq_step_closed hS', goodKV_step σ H.good i hi, H.fresh, H.keys,
    ⟨_, hc', ?_, hp⟩⟩
  exact (absSt_step σ H.good i).symm

/-- A write committed as pending, its token minted at `nx`. -/
theorem linkvOk_errW {S : linkv.PSet MS MI} {σ : KVState} {M : GMap Nat MI} {nx : Nat}
    (H : LinkvOk S σ M nx) (i : MI) (hw : i.isWrite = true) (hi : i.KeysIn wks) :
    ∃ S', (linkv.pSeq TS).step S (i, .err) = some S' ∧
      LinkvOk S' σ (GMap.insert nx i M) (nx + 1) := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errW_pending (P := TS) hc i hw
  refine ⟨S', hS', linkv.pSeq_step_closed hS', H.good, ?_, ?_, ⟨_, hc', hst, ?_⟩⟩
  · intro n hn
    show (GMap.insert nx i M) !! n = none
    rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact H.fresh n (by omega)
  · intro n j hn
    by_cases e : nx = n
    · subst e
      have : (GMap.insert nx i M) !! nx = some i := GMap.lookup_insert _ _ _
      rw [this] at hn
      cases hn
      exact hi
    · have : (GMap.insert nx i M) !! n = M !! n := GMap.lookup_insert_ne _ _ e
      rw [this] at hn
      exact H.keys n j hn
  · exact (pendIns_insert M nx i (H.fresh nx (Nat.le_refl _))).trans (hp.cons _)

/-- A read that failed. -/
theorem linkvOk_errR {S : linkv.PSet MS MI} {σ : KVState} {M : GMap Nat MI} {nx : Nat}
    (H : LinkvOk S σ M nx) (i : MI) (hw : i.isWrite = false) :
    ∃ S', (linkv.pSeq TS).step S (i, .err) = some S' ∧ LinkvOk S' σ M nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := linkv.pSeq_errR (P := TS) hc i hw
  exact ⟨S', hS', linkv.pSeq_step_closed hS', H.good, H.fresh, H.keys, ⟨c, hc', hst, hp⟩⟩

/-- **A late effect**: the pending write `n ↦ i` takes effect, the model state unchanged. -/
theorem linkvOk_pend {S : linkv.PSet MS MI} {σ : KVState} {M : GMap Nat MI} {nx : Nat}
    (H : LinkvOk S σ M nx) (n : Nat) (i : MI) (hn : M !! n = some i) :
    LinkvOk S (kvOpStep (opIn i) σ) (GMap.delete n M) nx := by
  obtain ⟨c, hc, hst, hp⟩ := H.cfg
  have hd := pendIns_delete M n i hn
  have hmem : i ∈ c.pend := hp.subset (hd.symm.subset List.mem_cons_self)
  refine ⟨H.closed, goodKV_step σ H.good i (H.keys n i hn), ?_, ?_,
    ⟨_, H.closed.apply hc hmem, ?_, ?_⟩⟩
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
      exact H.keys m j hm
  · show (TS.step i c.st).1 = linkv.absSt (kvOpStep (opIn i) σ)
    rw [hst]
    exact (absSt_step σ H.good i).symm
  · refine List.Perm.cons_inv ((hd.symm.trans hp).trans ?_)
    exact List.perm_cons_erase hmem

/-- A model input's answer's revision: the state's after it. -/
theorem outRev_le (i : MI) (σ : KVState) :
    (linkv.mStep wks i (linkv.absSt σ)).2.rev ≤ σ.rev + 1 := by
  rw [linkv.mStep_rev]
  exact (linkv.mStep_rev_le wks i _).2

/-- A read's answer's revision is the state's. -/
theorem outRev_read (i : MI) (σ : KVState) (hw : i.isWrite = false) :
    (linkv.mStep wks i (linkv.absSt σ)).2.rev = σ.rev := by
  rw [linkv.mStep_rev, linkv.mStep_read wks i _ hw]
  rfl

end pure

/-! ## The ghost state and the invariant -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- The instance's ghost names: the history's variable, the pending writes' map, the revisions'
states' map. -/
structure LinkvNames where
  h : GName
  p : GName
  r : GName

/-- The instance's namespace: its invariant's (`linkvInvN`) and a read's call's (`callN`). -/
def linkvN : Namespace := nroot .@ "linkvtxn"

/-- The instance's invariant's namespace. -/
def linkvInvN : Namespace := linkvN .@ "inv"

/-- A read's call invariant's namespace (`callInv`). -/
def callN : Namespace := linkvN .@ "call"

/-- **`Apply`'s mask** (`applySpec`'s `Eapp`): the server's invariants open where it fires a
client's update (`kvAu1`'s outer mask leaves them out), and the instance's. -/
def linkvE : CoPset := ↑srvRaftN ∪ ↑kvN ∪ ↑linkvN

theorem linkvN_mask : (↑linkvN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN :=
  Perennial.mask_ndot_ne2 nroot _ _ _ (by decide) (by decide)

theorem linkvInvN_mask : (↑linkvInvN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN :=
  nclose_subseteq' _ linkvN_mask

theorem callN_mask : (↑callN : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvInvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨linkvN_mask p (nclose_subseteq _ _ p hp),
    fun h' => ndot_ne_disjoint linkvN (by decide : "call" ≠ "inv") p ⟨hp, h'⟩⟩

theorem linkvE_mask' : ⊤ \ linkvE ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff] at hp
  obtain ⟨-, hn⟩ := hp
  unfold linkvE at hn
  simp only [Iris.Std.LawfulSet.mem_union, not_or] at hn
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, hn.1.1⟩, hn.1.2⟩, hn.2⟩

theorem linkvE_mask : ⊤ \ linkvE ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvInvN := by
  intro p hp
  have := linkvE_mask' p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this ⊢
  exact ⟨this.1, fun h' => this.2 (nclose_subseteq _ _ p h')⟩

theorem linkvE_mask_call :
    ⊤ \ linkvE ⊆ (((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvInvN) \ ↑callN := by
  intro p hp
  have := linkvE_mask' p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨linkvE_mask p hp, fun h' => this.2 (nclose_subseteq _ _ p h')⟩

theorem linkvE_mask_top : ⊤ \ linkvE ⊆ ⊤ \ ↑linkvInvN := by
  intro p hp
  have := linkvE_mask p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this ⊢
  exact ⟨CoPset.mem_full, this.2⟩

/-- **The library's abstract state** (`lintest`'s `libState`; see the file header). -/
def linkvState (γ : LinkvNames) (S : linkv.PSet MS MI) : IProp GF :=
  iprop(∃ h : List OpV, ghostVar γ.h (1 : Qp).half h ∗
    ⌜run (linkvtxnS (GF := GF)).M (linkv.pInit TS) h = some S⌝)

/-- **A pending write's token** (exclusive): the write `i` committed as pending under `n`. -/
def pendTok (γ : LinkvNames) (n : Nat) (i : MI) : IProp GF :=
  ghostMapElem γ.p n (DFrac.own 1) i

/-- The revisions' map at the state `σ`: its revision holds it, no later one is there. -/
def RevOk (Mr : GMap Nat KVState) (σ : KVState) : Prop :=
  Mr !! σ.rev = some σ ∧ ∀ n, σ.rev < n → Mr !! n = none

/-- **The revisions' states** (see the file header), with the current one's element, read-only. -/
def revOwn (γ : LinkvNames) (σ : KVState) : IProp GF :=
  iprop(∃ Mr : GMap Nat KVState, ghostMapAuth γ.r 1 Mr ∗
    ghostMapElem γ.r σ.rev DFrac.discard σ ∗ ⌜RevOk Mr σ⌝)

instance revOwn_timeless (γ : LinkvNames) (σ : KVState) : Timeless (revOwn (GF := GF) γ σ) := by
  unfold revOwn; infer_instance

/-- The invariant's contents (see the file header). -/
def linkvInvBody (γ : LinkvNames) (γk : KVNames) : IProp GF :=
  iprop(∃ (h : List OpV) (S : linkv.PSet MS MI) (σ : KVState) (M : GMap Nat MI) (nx : Nat),
    ghostVar γ.h (1 : Qp).half h ∗ etcdKV γk σ ∗ ghostMapAuth γ.p 1 M ∗ revOwn γ σ ∗
    ⌜run (linkvtxnS (GF := GF)).M (linkv.pInit TS) h = some S ∧ LinkvOk S σ M nx⌝)

instance linkvInvBody_timeless (γ : LinkvNames) (γk : KVNames) :
    Timeless (linkvInvBody (GF := GF) γ γk) := by
  unfold linkvInvBody; infer_instance

/-- **The instance's invariant** (see the file header). -/
def linkvInv (γ : LinkvNames) (γk : KVNames) : IProp GF :=
  iprop(inv linkvInvN (linkvInvBody γ γk))

instance linkvInv_persistent (γ : LinkvNames) (γk : KVNames) :
    Persistent (linkvInv (GF := GF) γ γk) := by
  unfold linkvInv; infer_instance

/-- **`lintest`'s linearization point** for the input `i`, the continuation `Φ` (see the file
header): the atomic triple's update, its `▷` stripped. -/
def linU (γ : LinkvNames) (i : GoInterface) (Φ : val → IProp GF) : IProp GF :=
  iprop(|={⊤ \ linkvE, ∅}=> ∃ S, linkvState γ S ∗ ∀ S' o,
    (linkvState γ S' ∗ ⌜(linkvtxnS (GF := GF)).M.step S (i, o) = some S'⌝) -∗
      |={∅, ⊤ \ linkvE}=> ((linkvtxnS (GF := GF)).ioOk i o -∗ Φ #o))

/-- The continuation at the output `y`. -/
abbrev contAt (x : Input) (y : Output) (Φ : val → IProp GF) : IProp GF :=
  iprop((linkvtxnS (GF := GF)).ioOk (boxIn x) (boxOut y) -∗ Φ #(boxOut y))

/-- **A write's result** at its firing at `σ` (see the file header): committed with `call`'s
output (the continuation; the state good), or, at a state whose answer's revision does not fit a word, committed
as failed. -/
def wQ (x : Input) (i : MI) (Φ : val → IProp GF) (σ : KVState) : IProp GF :=
  iprop((⌜GoodKV σ ∧ (linkv.mStep wks i (linkv.absSt σ)).2.rev < 2 ^ 64⌝ ∗
      contAt x (outAt i σ) Φ) ∨
    ⌜2 ^ 64 ≤ (linkv.mStep wks i (linkv.absSt σ)).2.rev⌝)

/-- **A read's call invariant** (see the file header), for the input `x` decoding to `i`, the
revision prophesied `R`, the continuation `Φ`. -/
def callInv (γ : LinkvNames) (γc γt : GName) (x : Input) (i : MI) (R : w64)
    (Φ : val → IProp GF) : IProp GF :=
  inv callN iprop(
    (linU γ (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option KVState)) ∨
    (∃ σ : KVState, dghostVar γc DFrac.discard (some σ) ∗
      ghostMapElem γ.r (uint.nat R) DFrac.discard σ ∗
      (contAt x (outAt i σ) Φ ∨ dghostVar γt (DFrac.own 1) ())))

instance callInv_persistent (γ : LinkvNames) (γc γt : GName) (x : Input) (i : MI) (R : w64)
    (Φ : val → IProp GF) : Persistent (callInv γ γc γt x i R Φ) := by
  unfold callInv; infer_instance

/-- **A read's result** at a firing at `σ` (see the file header). -/
def readQ (γc : GName) (R : w64) (σ : KVState) : IProp GF :=
  iprop(⌜GoodKV σ⌝ ∗ (⌜σ.rev = uint.nat R⌝ → dghostVar γc DFrac.discard (some σ)))

end defs

/-! ## The steps -/

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkvtxn.Assumptions]

/-- The model's step of a boxed input and output is the abstract model's of the decoded pair. -/
theorem step_box (S : linkv.PSet MS MI) (x : Input) (i : MI) (hx : decIn x = some i)
    (y : Output) :
    (linkvtxnS (GF := GF)).M.step S (boxIn x, boxOut y) =
      (linkv.pSeq TS).step S (i, decOut x.Kind' y) := by
  apply linkv.pM_step
  rw [decOp_box (sem := sem) (package_sem := package_sem)]
  simp [decIO, hx]

theorem run_snoc (h : List OpV) (S S' : linkv.PSet MS MI) (a : OpV)
    (h1 : run (linkvtxnS (GF := GF)).M (linkv.pInit TS) h = some S)
    (h2 : (linkvtxnS (GF := GF)).M.step S a = some S') :
    run (linkvtxnS (GF := GF)).M (linkv.pInit TS) (h ++ [a]) = some S' := by
  suffices H : ∀ (s0 : linkv.PSet MS MI) (l : List OpV),
      run (linkvtxnS (GF := GF)).M s0 (l ++ [a]) =
        (run (linkvtxnS (GF := GF)).M s0 l).bind ((linkvtxnS (GF := GF)).M.step · a) by
    rw [H, h1]; exact h2
  intro s0 l
  induction l generalizing s0 with
  | nil =>
    simp only [List.nil_append, run, Option.bind_some]
    cases (linkvtxnS (GF := GF)).M.step s0 a <;> rfl
  | cons b l ih =>
    simp only [List.cons_append, run]
    cases (linkvtxnS (GF := GF)).M.step s0 b with
    | none => rfl
    | some s1 => exact ih s1

/-- The revisions' map, after a step: the next revision's state added, if it moved. -/
theorem revOwn_step (γ : LinkvNames) (op : KVOp) (σ : KVState) :
    revOwn (GF := GF) γ σ ⊢ |==> revOwn γ (kvOpStep op σ) := by
  iintro H
  rcases kvOpStep_cases op σ with he | hr
  · rw [he]; imodintro; iexact H
  iunfold revOwn at H
  icases H with ⟨%Mr, HA, -, %Hok⟩
  have hfresh : Mr !! (σ.rev + 1) = none := Hok.2 _ (by omega)
  imod ghost_map_insert_persist (σ.rev + 1) (kvOpStep op σ) hfresh $$ HA with ⟨HA, #He⟩
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
theorem revOwn_elem (γ : LinkvNames) (σ : KVState) :
    revOwn (GF := GF) γ σ ⊢ revOwn γ σ ∗ ghostMapElem γ.r σ.rev DFrac.discard σ := by
  iintro H
  iunfold revOwn at H
  icases H with ⟨%Mr, HA, #He, %Hok⟩
  iframe He
  iunfold revOwn
  iexists Mr
  iframe He HA
  ipureintro; exact Hok

/-- **The invariant, allocated** from `etcdKV` at a good state that is the model's initial one;
with the library's initial state. -/
theorem linkvInv_alloc (γk : KVNames) (σ : KVState) (hg : GoodKV σ)
    (he : linkv.absSt σ = TS.init) (Em : CoPset) :
    etcdKV (GF := GF) γk σ ⊢ |={Em}=> ∃ γ : LinkvNames, linkvInv γ γk ∗
      linkvState γ (linkv.pInit TS) := by
  iintro Hσ
  imod ghostVar_alloc (GF := GF) ([] : List OpV) with ⟨%γh, Hh⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := MI) with ⟨%γp, Hp⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := KVState) with ⟨%γr, Hr⟩
  imod ghost_map_insert_persist σ.rev σ rfl $$ Hr with ⟨Hr, #He⟩
  icases (ghostVar_split_half γh 1 ([] : List OpV)).1 $$ Hh with ⟨Hh1, Hh2⟩
  imod inv_alloc linkvInvN Em (linkvInvBody (GF := GF) ⟨γh, γp, γr⟩ γk) $$ [Hh1 Hσ Hp Hr]
    with #Hinv
  · inext
    iunfold linkvInvBody
    iexists [], linkv.pInit TS, σ, ∅, 0
    iframe
    isplitl
    · iunfold revOwn
      iexists _
      iframe He Hr
      ipureintro
      exact ⟨GMap.lookup_insert _ _ _, fun n hn => by
        rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl⟩
    ipureintro; exact ⟨rfl, linkvOk_init σ hg he⟩
  imodintro
  iexists ⟨γh, γp, γr⟩
  iunfold linkvInv
  iframe Hinv
  iunfold linkvState
  iexists []
  iframe
  ipureintro; rfl

/-- **A write whose prophecy says `ok`** (see the file header). -/
theorem write_ok_au (γ : LinkvNames) (γk : KVNames) (x : Input) (i : MI) (hx : decIn x = some i)
    (hi : i.KeysIn wks) (hw : i.isWrite = true) (Φ : val → IProp GF) :
    linkvInv γ γk ∗ linU γ (boxIn x) Φ ⊢ kvOpAu1 γk (opIn i) (wQ x i Φ) := by
  have Hm := linkvInvN_mask
  have HE := linkvE_mask
  iintro ⟨#Hinv, HU⟩
  unfold kvOpAu1 kvAu1
  iunfold linkvInv at Hinv
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold linkvInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · -- abort: nothing moved
    iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv] with -
    · inext
      iunfold linkvInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact HU
  · -- commit: the write takes effect, `lintest`'s update commits
    iintro Hσ
    imod Hclose2 with -
    imod (revOwn_step γ (opIn i) σ) $$ Hrv with Hrv
    imod (fupd_mask_subseteq HE) with Hclose3
    iunfold linU at HU
    imod HU with ⟨%S0, HS, HU⟩
    iunfold linkvState at HS
    icases HS with ⟨%h0, Hh0, %Hr0⟩
    ihave %Heq := ghostVar_agree γ.h h (1 : Qp).half h0 (1 : Qp).half $$ Hh Hh0
    subst Heq
    have HS0 : S0 = S := Option.some.inj (Hr0.symm.trans Hr)
    subst HS0
    by_cases Hb : (linkv.mStep wks i (linkv.absSt σ)).2.rev < 2 ^ 64
    · -- the answer `call` builds
      obtain ⟨S', HS', Hok'⟩ := linkvOk_ok Hok i hi
      have Hst : (linkvtxnS (GF := GF)).M.step S0 (boxIn x, boxOut (outAt i σ)) = some S' := by
        rw [step_box S0 x i hx, outAt, decOut_outOf x i hx _ Hb]; exact HS'
      have Hr' := run_snoc h S0 S' _ Hr Hst
      imod ghostVar_update_halves (h ++ [(boxIn x, boxOut (outAt i σ))]) γ.h h h $$ Hh Hh0
        with ⟨Hh, Hh0⟩
      imod HU $$ %S' %(boxOut (outAt i σ)) [Hh0] with HΦ
      · isplitl [Hh0]
        · iunfold linkvState
          iexists _
          iframe Hh0
          ipureintro; exact Hr'
        · ipureintro; exact Hst
      imod Hclose3 with -
      imod Hclose $$ [Hh Hσ HM Hrv] with -
      · inext
        iunfold linkvInvBody
        iexists _, S', _, M, nx
        iframe
        ipureintro; exact ⟨Hr', Hok'⟩
      imodintro
      unfold wQ
      ileft
      iframe HΦ
      ipureintro; exact ⟨Hok.good, Hb⟩
    · -- an answer the model cannot decode: committed as failed, applied
      obtain ⟨S', HS', Hok'⟩ := linkvOk_errApplied Hok i hw hi
      have Hst : (linkvtxnS (GF := GF)).M.step S0 (boxIn x, boxOut errOut) = some S' := by
        rw [step_box S0 x i hx, decOut_errOut]; exact HS'
      have Hr' := run_snoc h S0 S' _ Hr Hst
      imod ghostVar_update_halves (h ++ [(boxIn x, boxOut errOut)]) γ.h h h $$ Hh Hh0
        with ⟨Hh, Hh0⟩
      imod HU $$ %S' %(boxOut errOut) [Hh0] with -
      · isplitl [Hh0]
        · iunfold linkvState
          iexists _
          iframe Hh0
          ipureintro; exact Hr'
        · ipureintro; exact Hst
      imod Hclose3 with -
      imod Hclose $$ [Hh Hσ HM Hrv] with -
      · inext
        iunfold linkvInvBody
        iexists _, S', _, M, nx
        iframe
        ipureintro; exact ⟨Hr', Hok'⟩
      imodintro
      unfold wQ
      iright
      ipureintro; omega

/-- **A pending write's update** (see the file header): at its firing (if ever) the write takes
effect, its token consumed; the history and the model state do not move (`linkvOk_pend`). -/
theorem write_pend_au (γ : LinkvNames) (γk : KVNames) (n : Nat) (i : MI) :
    linkvInv γ γk ∗ pendTok γ n i ⊢ kvOpAu1 (GF := GF) γk (opIn i) (fun _ => iprop(True)) := by
  have Hm := linkvInvN_mask
  iintro ⟨#Hinv, Htok⟩
  unfold kvOpAu1 kvAu1
  iunfold linkvInv at Hinv
  iauintro
  unfold atomic_acc
  iinv Hinv with >Hi Hclose
  iunfold linkvInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv] with -
    · inext
      iunfold linkvInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact Htok
  · iintro Hσ
    imod Hclose2 with -
    imod (revOwn_step γ (opIn i) σ) $$ Hrv with Hrv
    iunfold pendTok at Htok
    ihave %Hn := ghost_map_lookup $$ HM Htok
    imod ghost_map_delete $$ HM Htok with HM
    imod Hclose $$ [Hh Hσ HM Hrv] with -
    · inext
      iunfold linkvInvBody
      iexists h, S, _, _, nx
      iframe
      ipureintro; exact ⟨Hr, linkvOk_pend Hok n i Hn⟩
    imodintro
    itrivial

/-- **A write whose prophecy says error** (see the file header): `lintest`'s update commits at
once, the write pending (output `errOut`, `linkvOk_errW`), with the pending write's token. -/
theorem write_err_commit (γ : LinkvNames) (γk : KVNames) (x : Input) (i : MI)
    (hx : decIn x = some i) (hi : i.KeysIn wks) (hw : i.isWrite = true) (Φ : val → IProp GF) :
    linkvInv γ γk ∗ linU γ (boxIn x) Φ ⊢
      |={⊤}=> ∃ n : Nat, contAt x errOut Φ ∗ pendTok γ n i := by
  have HE := linkvE_mask_top
  iintro ⟨#Hinv, HU⟩
  iunfold linkvInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold linkvInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  imod (fupd_mask_subseteq HE) with Hclose3
  iunfold linU at HU
  imod HU with ⟨%S0, HS, HU⟩
  iunfold linkvState at HS
  icases HS with ⟨%h0, Hh0, %Hr0⟩
  ihave %Heq := ghostVar_agree γ.h h (1 : Qp).half h0 (1 : Qp).half $$ Hh Hh0
  subst Heq
  have HS0 : S0 = S := Option.some.inj (Hr0.symm.trans Hr)
  subst HS0
  obtain ⟨S', HS', Hok'⟩ := linkvOk_errW Hok i hw hi
  have Hst : (linkvtxnS (GF := GF)).M.step S0 (boxIn x, boxOut errOut) = some S' := by
    rw [step_box S0 x i hx, decOut_errOut]; exact HS'
  have Hr' := run_snoc h S0 S' _ Hr Hst
  imod ghostVar_update_halves (h ++ [(boxIn x, boxOut errOut)]) γ.h h h $$ Hh Hh0
    with ⟨Hh, Hh0⟩
  imod ghost_map_insert nx i (Hok.fresh nx (Nat.le_refl _)) $$ HM with ⟨HM, Htok⟩
  imod HU $$ %S' %(boxOut errOut) [Hh0] with HΦ
  · isplitl [Hh0]
    · iunfold linkvState
      iexists _
      iframe Hh0
      ipureintro; exact Hr'
    · ipureintro; exact Hst
  imod Hclose3 with -
  imod Hclose $$ [Hh Hσ HM Hrv] with -
  · inext
    iunfold linkvInvBody
    iexists _, S', σ, _, nx + 1
    iframe
    ipureintro; exact ⟨Hr', Hok'⟩
  imodintro
  iexists nx
  iframe HΦ
  iunfold pendTok
  iexact Htok

/-- **A read whose prophecy says error** (see the file header): `lintest`'s update commits at
once with output `errOut` (`linkvOk_errR`). -/
theorem read_err_commit (γ : LinkvNames) (γk : KVNames) (x : Input) (i : MI)
    (hx : decIn x = some i) (hw : i.isWrite = false) (Φ : val → IProp GF) :
    linkvInv γ γk ∗ linU γ (boxIn x) Φ ⊢ |={⊤}=> contAt x errOut Φ := by
  have HE := linkvE_mask_top
  iintro ⟨#Hinv, HU⟩
  iunfold linkvInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold linkvInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  imod (fupd_mask_subseteq HE) with Hclose3
  iunfold linU at HU
  imod HU with ⟨%S0, HS, HU⟩
  iunfold linkvState at HS
  icases HS with ⟨%h0, Hh0, %Hr0⟩
  ihave %Heq := ghostVar_agree γ.h h (1 : Qp).half h0 (1 : Qp).half $$ Hh Hh0
  subst Heq
  have HS0 : S0 = S := Option.some.inj (Hr0.symm.trans Hr)
  subst HS0
  obtain ⟨S', HS', Hok'⟩ := linkvOk_errR Hok i hw
  have Hst : (linkvtxnS (GF := GF)).M.step S0 (boxIn x, boxOut errOut) = some S' := by
    rw [step_box S0 x i hx, decOut_errOut]; exact HS'
  have Hr' := run_snoc h S0 S' _ Hr Hst
  imod ghostVar_update_halves (h ++ [(boxIn x, boxOut errOut)]) γ.h h h $$ Hh Hh0
    with ⟨Hh, Hh0⟩
  imod HU $$ %S' %(boxOut errOut) [Hh0] with HΦ
  · isplitl [Hh0]
    · iunfold linkvState
      iexists _
      iframe Hh0
      ipureintro; exact Hr'
    · ipureintro; exact Hst
  imod Hclose3 with -
  imod Hclose $$ [Hh Hσ HM Hrv] with -
  · inext
    iunfold linkvInvBody
    iexists _, S', σ, M, nx
    iframe
    ipureintro; exact ⟨Hr', Hok'⟩
  imodintro
  iexact HΦ

/-- **A read whose prophecies say `ok` at revision `R`** (see the file header): the read update
the server fires at every committed state from the read index on. At a firing at a state of
revision `R`, if `lintest`'s update is not yet committed, it commits with `call`'s output at the
state, and the commit bit records the state; a later firing at revision `R` sees the same state
(the revisions' map) and does nothing. Either way the result says the state is good and the bit
holds it. -/
theorem read_ok_au (γ : LinkvNames) (γk : KVNames) (γc γt : GName) (x : Input) (i : MI)
    (hx : decIn x = some i) (hw : i.isWrite = false) (R : w64) (Φ : val → IProp GF) :
    linkvInv γ γk ∗ callInv γ γc γt x i R Φ ⊢ kvReadAu γk (readQ γc R) := by
  have Hm := linkvInvN_mask
  have Hcm := callN_mask
  have HE := linkvE_mask_call
  iintro ⟨#Hinv, #Hc⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold linkvInv at Hinv
  iinv Hinv with >Hi Hclose
  iunfold linkvInvBody at Hi
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, Hrv, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  ihave ⟨Hrv, #Hel⟩ := revOwn_elem γ σ $$ Hrv
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvInvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM Hrv] with -
    · inext
      iunfold linkvInvBody
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iempintro
  · iintro Hσ
    imod Hclose2 with -
    by_cases Hrev : σ.rev = uint.nat R
    · unfold callInv
      iinv Hc with Hci Hclosec
      icases Hci with (⟨HU, >Hlc, >Hγc⟩ | ⟨%σ0, >#Hv, >#HL, Hrest⟩)
      · -- the first firing at revision `R`: commit
        imod lc_fupd_elim_later $$ Hlc HU with HU
        imod (fupd_mask_subseteq HE) with Hclose3
        iunfold linU at HU
        imod HU with ⟨%S0, HS, HU⟩
        iunfold linkvState at HS
        icases HS with ⟨%h0, Hh0, %Hr0⟩
        ihave %Heq := ghostVar_agree γ.h h (1 : Qp).half h0 (1 : Qp).half $$ Hh Hh0
        subst Heq
        have HS0 : S0 = S := Option.some.inj (Hr0.symm.trans Hr)
        subst HS0
        obtain ⟨S', HS', Hok'⟩ := linkvOk_read Hok i hw
        have Hb : (linkv.mStep wks i (linkv.absSt σ)).2.rev < 2 ^ 64 := by
          rw [outRev_read i σ hw, Hrev]
          unfold uint.nat; word
        have Hst : (linkvtxnS (GF := GF)).M.step S0 (boxIn x, boxOut (outAt i σ)) = some S' := by
          rw [step_box S0 x i hx, outAt, decOut_outOf x i hx _ Hb]; exact HS'
        have Hr' := run_snoc h S0 S' _ Hr Hst
        imod ghostVar_update_halves (h ++ [(boxIn x, boxOut (outAt i σ))]) γ.h h h
          $$ Hh Hh0 with ⟨Hh, Hh0⟩
        imod HU $$ %S' %(boxOut (outAt i σ)) [Hh0] with HΦ
        · isplitl [Hh0]
          · iunfold linkvState
            iexists _
            iframe Hh0
            ipureintro; exact Hr'
          · ipureintro; exact Hst
        imod Hclose3 with -
        imod dghostVar_update (some σ) γc none $$ Hγc with Hγc
        imod dghostVar_persist γc 1 _ $$ Hγc with #Hγc
        imod Hclosec $$ [HΦ] with -
        · inext
          iright
          iexists σ
          rw [← Hrev]
          iframe Hγc Hel
          ileft
          iexact HΦ
        imod Hclose $$ [Hh Hσ HM Hrv] with -
        · inext
          iunfold linkvInvBody
          iexists _, S', σ, M, nx
          iframe
          ipureintro; exact ⟨Hr', Hok'⟩
        imodintro
        imodintro
        unfold readQ
        isplitr
        · ipureintro; exact Hok.good
        iintro %_
        iexact Hγc
      · -- a later firing at revision `R`: the same state, nothing to do
        ihave %HLe := ghostMapElem_agree (uint.nat R) γ.r _ _ _ _ $$ HL [Hel]
        · rw [← Hrev]; iexact Hel
        subst HLe
        imod Hclosec $$ [Hrest] with -
        · inext
          iright
          iexists σ0
          iframe Hv HL Hrest
        imod Hclose $$ [Hh Hσ HM Hrv] with -
        · inext
          iunfold linkvInvBody
          iexists h, S, _, M, nx
          iframe
          ipureintro; exact ⟨Hr, Hok⟩
        imodintro
        imodintro
        unfold readQ
        isplitr
        · ipureintro; exact Hok.good
        iintro %_
        iexact Hv
    · imod Hclose $$ [Hh Hσ HM Hrv] with -
      · inext
        iunfold linkvInvBody
        iexists h, S, σ, M, nx
        iframe
        ipureintro; exact ⟨Hr, Hok⟩
      imodintro
      imodintro
      unfold readQ
      isplitr
      · ipureintro; exact Hok.good
      iintro %H
      exact absurd H Hrev

/-- **`Apply` takes the continuation** after the reply: the commit bit holds `σ`, so the call
invariant is on its committed side, its continuation still there (`Apply` holds the token). -/
theorem callInv_take (γ : LinkvNames) (γc γt : GName) (x : Input) (i : MI) (R : w64)
    (Φ : val → IProp GF) (σ : KVState) :
    callInv γ γc γt x i R Φ ∗ dghostVar γc DFrac.discard (some σ) ∗
      dghostVar γt (DFrac.own 1) () ∗ £ 1 ⊢ |={⊤}=> contAt x (outAt i σ) Φ := by
  iintro ⟨#Hc, #Hv, Htok, Hlc⟩
  unfold callInv
  iinv Hc with Hci Hclosec
  icases Hci with (⟨-, -, >Hγc⟩ | ⟨%σ', >#Hv', >#HL, Hrest⟩)
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
        iexists σ
        iframe Hv HL
        iright
        iexact Htok
      imodintro
      iexact HΦ
    · ihave %Hbad := dghostVar_valid_2 γt _ _ _ _ $$ Htok Htok'
      exfalso
      have h := DFrac.valid_own_op Hbad.1
      exact absurd h (by decide)

end proofs

end linkvtxn
end EtcdGrove
end Perennial
