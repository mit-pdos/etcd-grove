/-
Lean-first (no Rocq counterpart).

# linkv: the library's abstract state over etcd's KV (D20 (c), 2026-10-19)

What `Apply`'s spec (`Spec/.../linkv/Apply.lean`) is stated with, and the ghost steps its
proof takes at the linearization points.

## The state

`lintest`'s `libState` is `linkvState γ S`: half of a ghost variable at `γ.h` holding the
**history** `h` (porcupine's operations linearized so far), with `S` the model state `run`
reaches from it (`kvM decOp`). The model state is a set of configurations, not countable, so the
ghost variable holds the history, which determines it. The other half is in the instance's
invariant `linkvInv γ γk` (at `linkvInvN`), which also holds the server's `etcdKV γk σ` (the client's
half of the KV state) and the authority of the **pending puts** `M` (a ghost map, `γ.p`): the
failed puts committed as pending (`CStep.putErr`) whose update the server has not yet fired.
`LinkvOk S σ M nx` relates them: some configuration `c` of `S` is the server's store
(`c.kv = absKV σ`) with exactly `M`'s puts pending (`pendVals M` a permutation of `c.pend`),
`S` is closed under late effects, the server's state is sorted (`absKV_put`'s premise), and the
keys of `M` are below `nx` (a fresh key for the next).

Why the pending puts live in the invariant: a failed put's update may fire *after* `Apply`
returned (the proposal still in raft), when `lintest`'s update is gone. It then fires from the
invariant alone: it consumes the put's token (`pendTok`), so the put is in `c.pend`, and the
configuration with it applied (`KVSet.Closed.apply`) is in `S`, which does not change (a late
effect is no operation of the history).

## The steps (the commits of `Apply`'s cases)

`linU γ i Φ` is `lintest`'s linearization point (the one-shot update of the atomic triple's
notation, `Perennial/ProgramLogic/AtomicFupd.lean`, its `▷` stripped).

- `put_ok_au`: a put whose prophecy says `ok` hands the server an update fired at most once
  (`kvOpAu1`) that commits `lintest`'s update at the firing, with output `ok`, and leaves its
  continuation as the update's result (which `Put` returns on success).
- `put_err_commit`: a put whose prophecy says error commits at once, as pending (output
  `Err`), minting the pending put's token; `put_pend_au` is the update the server is handed:
  at its firing (during the call or after it, or never) the pending put takes effect.
- `get_err_commit`: a get whose prophecy says error commits at once (a failed get constrains
  nothing).
- `linkvInv_alloc`: the invariant and `linkvState γ kvInit`, from `etcdKV` at an empty store.

- `get_ok_au`: a get whose prophecies say `ok` at revision `R`: the read update (persistent:
  the server fires it at every committed state from the read index on). Its commit-once state is
  the call invariant `callInv` (at `callN`): `lintest`'s update with a later credit and the commit
  bit `γc` at `none`, or, once committed at a state of revision `R`, `γc` read-only at the value
  the store gave and the continuation (until `Apply` takes it with its token: `callInv_take`).
  A firing at a state of revision `R` sees the same store as the commit did: `linkvInv` keeps the
  revisions' map (`revOwn`: every revision the state had to its key-values, `kvProj`, written at
  each put, which bumps the revision, `kvOpStep_put_rev`; reads do not change the state), whose
  read-only elements agree. The read's result `getQ` says the bit holds the store's value at a
  state of revision `R`.

The invariant's namespace is `linkvInvN`, the call invariants' `callN`, both under `linkvN`
(in `Apply`'s mask `linkvE`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.Defs
public import Proof.github_com.mit_pdos.etcd_grove.examples.linkv.ModelKV
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.InvRequest

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace linkv

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.linkv

/-! ## Pure part -/

section pure
variable [ext : FfiSyntax]

/-- The pending puts' values (in some order). -/
def pendVals (M : GMap Nat (GoString × GoString)) : List (GoString × GoString) :=
  M.toList.map Prod.snd

/-- **The invariant's relation** (see the file header). -/
structure LinkvOk (S : KVSet GoString GoString) (σ : KVState) (M : GMap Nat (GoString × GoString))
    (nx : Nat) : Prop where
  closed : S.Closed
  sorted : σ.kvs.Pairwise etcdKvLess
  fresh : ∀ n, nx ≤ n → M !! n = none
  cfg : ∃ c, S c ∧ c.kv = absKV σ ∧ (pendVals M).Perm c.pend

theorem pendVals_insert (M : GMap Nat (GoString × GoString)) (n : Nat) (x : GoString × GoString)
    (h : M !! n = none) : (pendVals (GMap.insert n x M)).Perm (x :: pendVals M) := by
  unfold pendVals
  have hp := Iris.Std.LawfulFiniteMap.toList_insert (M := GMap Nat) (m := M) (k := n) (v := x) h
  exact hp.map Prod.snd

theorem pendVals_delete (M : GMap Nat (GoString × GoString)) (n : Nat) (x : GoString × GoString)
    (h : M !! n = some x) : (pendVals M).Perm (x :: pendVals (GMap.delete n M)) := by
  unfold pendVals
  have hp := Iris.Std.LawfulFiniteMap.toList_delete (M := GMap Nat) (m := M) (k := n) (v := x) h
  exact hp.map Prod.snd

/-- A state's key-values, as pairs (what the revisions' map keeps: countable). -/
def kvProj (kvs : List EtcdKv) : List (GoString × GoString) := kvs.map fun e => (e.key, e.value)

/-- The store of a list of pairs: a key's first pair's value. -/
def absP (l : List (GoString × GoString)) (k : GoString) : Option GoString :=
  (l.find? fun p => decide (p.1 = k)).map Prod.snd

theorem absKV_proj (σ : KVState) (k : GoString) : absKV σ k = absP (kvProj σ.kvs) k := by
  unfold absKV absP kvProj mvcc.findKey
  rw [List.find?_map, Option.map_map]
  rfl

/-- The revisions' map at the state `σ`: its revision holds its key-values, no later one is
there. -/
def RevOk (Mr : GMap Nat (List (GoString × GoString))) (σ : KVState) : Prop :=
  Mr !! σ.rev = some (kvProj σ.kvs) ∧ ∀ n, σ.rev < n → Mr !! n = none

theorem kvOpStep_put_rev (k v : GoString) (σ : KVState) :
    (kvOpStep (.put (putOp k v)) σ).rev = σ.rev + 1 := by
  rw [kvOpStep_put_eq]

/-- The relation at the start: the empty store, nothing pending. -/
theorem linkvOk_init (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess)
    (he : absKV σ = fun _ => none) : LinkvOk kvInit σ (∅ : GMap Nat (GoString × GoString)) 0 := by
  refine ⟨kvInit_closed, hs, fun _ _ => rfl, ⟨⟨fun _ => none, []⟩, rfl, he.symm, ?_⟩⟩
  simp [pendVals]

/-- A put that returned `ok` (`kvSeq_putOk`), at the real configuration. -/
theorem linkvOk_putOk {S : KVSet GoString GoString} {σ : KVState} {M : GMap Nat (GoString × GoString)}
    {nx : Nat} (H : LinkvOk S σ M nx) (k v : GoString) :
    ∃ S', kvSeq.step S (.put k v, .ok) = some S' ∧
      LinkvOk S' (kvOpStep (.put (putOp k v)) σ) M nx := by
  obtain ⟨c, hc, hkv, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := kvSeq_putOk hc k v
  refine ⟨S', hS', kvSeq_step_closed hS', kvOpStep_put_sorted k v σ H.sorted, H.fresh,
    ⟨_, hc', ?_, hp⟩⟩
  rw [absKV_put k v σ H.sorted, hkv]

/-- A put committed as pending (`kvSeq_putErr_pending`), its token minted at `nx`. -/
theorem linkvOk_putErr {S : KVSet GoString GoString} {σ : KVState} {M : GMap Nat (GoString × GoString)}
    {nx : Nat} (H : LinkvOk S σ M nx) (k v : GoString) :
    ∃ S', kvSeq.step S (.put k v, .err) = some S' ∧
      LinkvOk S' σ (GMap.insert nx (k, v) M) (nx + 1) := by
  obtain ⟨c, hc, hkv, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := kvSeq_putErr_pending hc k v
  refine ⟨S', hS', kvSeq_step_closed hS', H.sorted, ?_, ⟨_, hc', hkv, ?_⟩⟩
  · intro n hn
    show (GMap.insert nx (k, v) M) !! n = none
    rw [GMap.lookup_insert_ne _ _ (by omega)]
    exact H.fresh n (by omega)
  · exact (pendVals_insert M nx (k, v) (H.fresh nx (Nat.le_refl _))).trans (hp.cons _)

/-- A failed get (`kvSeq_getErr`). -/
theorem linkvOk_getErr {S : KVSet GoString GoString} {σ : KVState} {M : GMap Nat (GoString × GoString)}
    {nx : Nat} (H : LinkvOk S σ M nx) (k : GoString) :
    ∃ S', kvSeq.step S (.get k, .err) = some S' ∧ LinkvOk S' σ M nx := by
  obtain ⟨c, hc, hkv, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := kvSeq_getErr hc k
  exact ⟨S', hS', kvSeq_step_closed hS', H.sorted, H.fresh, ⟨c, hc', hkv, hp⟩⟩

/-- A get that read the server's store (`kvSeq_getOk`). -/
theorem linkvOk_getOk {S : KVSet GoString GoString} {σ : KVState} {M : GMap Nat (GoString × GoString)}
    {nx : Nat} (H : LinkvOk S σ M nx) (k : GoString) :
    ∃ S', kvSeq.step S (.get k, .okGet (absKV σ k)) = some S' ∧ LinkvOk S' σ M nx := by
  obtain ⟨c, hc, hkv, hp⟩ := H.cfg
  obtain ⟨S', hS', hc'⟩ := kvSeq_getOk hc k
  rw [hkv] at hS'
  exact ⟨S', hS', kvSeq_step_closed hS', H.sorted, H.fresh, ⟨c, hc', hkv, hp⟩⟩

/-- **A late effect**: the pending put `n ↦ (k, v)` takes effect, the model state unchanged. -/
theorem linkvOk_pend {S : KVSet GoString GoString} {σ : KVState} {M : GMap Nat (GoString × GoString)}
    {nx : Nat} (H : LinkvOk S σ M nx) (n : Nat) (k v : GoString) (hn : M !! n = some (k, v)) :
    LinkvOk S (kvOpStep (.put (putOp k v)) σ) (GMap.delete n M) nx := by
  obtain ⟨c, hc, hkv, hp⟩ := H.cfg
  have hd := pendVals_delete M n (k, v) hn
  have hmem : (k, v) ∈ c.pend := hp.subset (hd.symm.subset List.mem_cons_self)
  refine ⟨H.closed, kvOpStep_put_sorted k v σ H.sorted, ?_, ⟨_, H.closed.apply hc hmem, ?_, ?_⟩⟩
  · intro m hm
    show (GMap.delete n M) !! m = none
    by_cases e : n = m
    · subst e; exact GMap.lookup_delete _ _
    · rw [GMap.lookup_delete_ne _ e]; exact H.fresh m hm
  · rw [absKV_put k v σ H.sorted, hkv]
  · refine List.Perm.cons_inv ((hd.symm.trans hp).trans ?_)
    exact @List.perm_cons_erase (GoString × GoString)
      (@instBEqProd GoString GoString instBEqOfDecidableEq instBEqOfDecidableEq) _ (k, v) c.pend hmem

end pure

/-! ## The ghost state and the invariant -/

section defs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- The instance's ghost names: the history's variable and the pending puts' map. -/
structure LinkvNames where
  h : GName
  p : GName
  r : GName

/-- The instance's namespace: its invariant's (`linkvInvN`) and a get's call's (`callN`). -/
def linkvN : Namespace := nroot .@ "linkv"

/-- The instance's invariant's namespace. -/
def linkvInvN : Namespace := linkvN .@ "inv"

/-- A get's call invariant's namespace (`callInv`). -/
def callN : Namespace := linkvN .@ "call"

/-- **`Apply`'s mask** (`applySpec`'s `Eapp`): the server's invariants open where it fires a
client's update (`kvAu1`'s outer mask leaves them out), and the instance's. -/
def linkvE : CoPset := ↑srvRaftN ∪ ↑kvN ∪ ↑linkvN

theorem linkvN_mask : (↑linkvN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

theorem linkvInvN_mask : (↑linkvInvN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN :=
  nclose_subseteq' _ linkvN_mask

theorem callN_mask : (↑callN : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvInvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff]
  exact ⟨linkvN_mask p (nclose_subseteq _ _ p hp),
    fun h' => ndot_ne_disjoint linkvN (by decide : "call" ≠ "inv") p ⟨hp, h'⟩⟩

theorem callN_top : (↑callN : CoPset) ⊆ ⊤ \ ↑linkvInvN := by
  intro p hp
  have := callN_mask p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this ⊢
  exact ⟨CoPset.mem_full, this.2⟩

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

theorem linkvE_mask_top_call : ⊤ \ linkvE ⊆ (⊤ \ ↑linkvInvN) \ ↑callN := by
  intro p hp
  have := linkvE_mask_call p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this ⊢
  exact ⟨linkvE_mask_top p hp, this.2⟩

/-- **The library's abstract state** (`lintest`'s `libState`; see the file header). -/
def linkvState (γ : LinkvNames) (S : KVSet GoString GoString) : IProp GF :=
  iprop(∃ h : List OpV, ghostVar γ.h (1 : Qp).half h ∗ ⌜run (kvM decOp) kvInit h = some S⌝)

/-- **A pending put's token** (exclusive): the put `k ↦ v` committed as pending under `n`. -/
def pendTok (γ : LinkvNames) (n : Nat) (k v : GoString) : IProp GF :=
  ghostMapElem γ.p n (DFrac.own 1) (k, v)

/-- **The revisions' stores** (see the file header): the map `Mr` from every revision the server's
state had to its store's key-values (`kvProj`), with the current one's element, read-only. -/
def revOwn (γ : LinkvNames) (σ : KVState) : IProp GF :=
  iprop(∃ Mr : GMap Nat (List (GoString × GoString)), ghostMapAuth γ.r 1 Mr ∗
    ghostMapElem γ.r σ.rev DFrac.discard (kvProj σ.kvs) ∗ ⌜RevOk Mr σ⌝)

instance revOwn_timeless (γ : LinkvNames) (σ : KVState) : Timeless (revOwn (GF := GF) γ σ) := by
  unfold revOwn; infer_instance

/-- **The instance's invariant** (see the file header). -/
def linkvInv (γ : LinkvNames) (γk : KVNames) : IProp GF :=
  inv linkvInvN iprop(∃ (h : List OpV) (S : KVSet GoString GoString) (σ : KVState)
      (M : GMap Nat (GoString × GoString)) (nx : Nat),
    ghostVar γ.h (1 : Qp).half h ∗ etcdKV γk σ ∗ ghostMapAuth γ.p 1 M ∗ revOwn γ σ ∗
    ⌜run (kvM decOp) kvInit h = some S ∧ LinkvOk S σ M nx⌝)

instance linkvInv_persistent (γ : LinkvNames) (γk : KVNames) :
    Persistent (linkvInv (GF := GF) γ γk) := by
  unfold linkvInv; infer_instance

/-- **`lintest`'s linearization point** for the input `i`, the continuation `Φ` (see the file
header): the atomic triple's update, its `▷` stripped. -/
def linU (γ : LinkvNames) (i : GoInterface) (Φ : val → IProp GF) : IProp GF :=
  iprop(|={⊤ \ linkvE, ∅}=> ∃ S, linkvState γ S ∗ ∀ S' o,
    (linkvState γ S' ∗ ⌜(linkvS (GF := GF)).M.step S (i, o) = some S'⌝) -∗
      |={∅, ⊤ \ linkvE}=> (linkvS.ioOk i o -∗ Φ #o))

/-- A successful get's output for the value `v` at its key. -/
def getOut (v : Option GoString) : Output :=
  match v with
  | none => ⟨false, false, go!""⟩
  | some s => ⟨false, true, s⟩

/-- **A get's call invariant** (see the file header), for the input `x`, the revision prophesied
`R`, the continuation `Φ`: `lintest`'s update not yet committed (with a later credit to take it
out, and the commit bit `γc` at `none`), or committed at a state of revision `R` whose store
gives the value `v` (`γc` read-only at `some v`), its continuation left until `Apply` takes it
with the token `γt`. -/
def callInv (γ : LinkvNames) (γc γt : GName) (x : Input) (R : w64) (Φ : val → IProp GF) :
    IProp GF :=
  inv callN iprop(
    (linU γ (boxIn x) Φ ∗ £ 1 ∗ dghostVar γc (DFrac.own 1) (none : Option (Option GoString))) ∨
    (∃ (v : Option GoString) (L : List (GoString × GoString)),
      dghostVar γc DFrac.discard (some v) ∗ ghostMapElem γ.r (uint.nat R) DFrac.discard L ∗
      ⌜v = absP L x.Key'⌝ ∗
      ((linkvS.ioOk (boxIn x) (boxOut (getOut v)) -∗ Φ #(boxOut (getOut v))) ∨
        dghostVar γt (DFrac.own 1) ())))

instance callInv_persistent (γ : LinkvNames) (γc γt : GName) (x : Input) (R : w64)
    (Φ : val → IProp GF) : Persistent (callInv γ γc γt x R Φ) := by
  unfold callInv; infer_instance

/-- **A get's read result** at a firing at `σ`: if `σ` is of the prophesied revision, the commit
bit holds the value `σ`'s store gives the key. -/
def getQ (γc : GName) (x : Input) (R : w64) (σ : KVState) : IProp GF :=
  iprop(⌜σ.rev = uint.nat R⌝ → dghostVar γc DFrac.discard (some (absKV σ x.Key')))

end defs

/-! ## The steps -/

section proofs
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.linkv.Assumptions]

/-- A put's input. -/
abbrev putIn (k v : GoString) : Input := ⟨true, k, v⟩

/-- A get's input. -/
abbrev getIn (k : GoString) : Input := ⟨false, k, go!""⟩

/-- A call's output when it returned `ok` with nothing found (a put's). -/
abbrev okOut : Output := ⟨false, false, go!""⟩

/-- A call's output when it failed. -/
abbrev errOut : Output := ⟨true, false, go!""⟩

theorem step_put_ok (S : KVSet GoString GoString) (x : Input) (hx : x.Put' = true) :
    (linkvS (GF := GF)).M.step S (boxIn x, boxOut okOut) = kvSeq.step S (.put x.Key' x.Val', .ok) := by
  apply kvM_step
  rw [decOp_box (sem := sem) (package_sem := package_sem)]
  simp [decIO, hx]

theorem step_put_err (S : KVSet GoString GoString) (x : Input) (hx : x.Put' = true) :
    (linkvS (GF := GF)).M.step S (boxIn x, boxOut errOut) = kvSeq.step S (.put x.Key' x.Val', .err) := by
  apply kvM_step
  rw [decOp_box (sem := sem) (package_sem := package_sem)]
  simp [decIO, hx]

theorem step_get_err (S : KVSet GoString GoString) (x : Input) (hx : x.Put' = false) :
    (linkvS (GF := GF)).M.step S (boxIn x, boxOut errOut) = kvSeq.step S (.get x.Key', .err) := by
  apply kvM_step
  rw [decOp_box (sem := sem) (package_sem := package_sem)]
  simp [decIO, hx]

theorem step_get_ok (S : KVSet GoString GoString) (x : Input) (hx : x.Put' = false)
    (v : Option GoString) :
    (linkvS (GF := GF)).M.step S (boxIn x, boxOut (getOut v)) =
      kvSeq.step S (.get x.Key', .okGet v) := by
  apply kvM_step
  rw [decOp_box (sem := sem) (package_sem := package_sem)]
  cases v <;> simp [decIO, hx, getOut]

theorem run_snoc (h : List OpV) (S S' : KVSet GoString GoString) (a : OpV)
    (h1 : run (kvM decOp) kvInit h = some S) (h2 : (kvM decOp).step S a = some S') :
    run (kvM decOp) kvInit (h ++ [a]) = some S' := by
  suffices H : ∀ (s0 : KVSet GoString GoString) (l : List OpV),
      run (kvM decOp) s0 (l ++ [a]) = (run (kvM decOp) s0 l).bind ((kvM decOp).step · a) by
    rw [H, h1]; exact h2
  intro s0 l
  induction l generalizing s0 with
  | nil =>
    simp only [List.nil_append, run, Option.bind_some]
    cases (kvM decOp).step s0 a <;> rfl
  | cons b l ih =>
    simp only [List.cons_append, run]
    cases (kvM decOp).step s0 b with
    | none => rfl
    | some s1 => exact ih s1

/-- The revisions' map, after a put: the next revision's store added. -/
theorem revOwn_put (γ : LinkvNames) (k v : GoString) (σ : KVState) :
    revOwn (GF := GF) γ σ ⊢ |==> revOwn γ (kvOpStep (.put (putOp k v)) σ) := by
  iintro H
  iunfold revOwn at H
  icases H with ⟨%Mr, HA, -, %Hok⟩
  have hr := kvOpStep_put_rev k v σ
  have hfresh : Mr !! (σ.rev + 1) = none := Hok.2 _ (by omega)
  imod ghost_map_insert_persist (σ.rev + 1) (kvProj (kvOpStep (.put (putOp k v)) σ).kvs) hfresh
    $$ HA with ⟨HA, #He⟩
  imodintro
  iunfold revOwn
  iexists _
  rw [hr]
  iframe He HA
  ipureintro
  refine ⟨GMap.lookup_insert _ _ _, fun n hn => ?_⟩
  rw [GMap.lookup_insert_ne _ _ (by omega)]
  exact Hok.2 n (by omega)

/-- The current revision's store, read-only. -/
theorem revOwn_elem (γ : LinkvNames) (σ : KVState) :
    revOwn (GF := GF) γ σ ⊢ revOwn γ σ ∗ ghostMapElem γ.r σ.rev DFrac.discard (kvProj σ.kvs) := by
  iintro H
  iunfold revOwn at H
  icases H with ⟨%Mr, HA, #He, %Hok⟩
  iframe He
  iunfold revOwn
  iexists Mr
  iframe He HA
  ipureintro; exact Hok

/-- **The invariant, allocated** from `etcdKV` at a sorted state with an empty store; with the
library's initial state. -/
theorem linkvInv_alloc (γk : KVNames) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess)
    (he : absKV σ = fun _ => none) (Em : CoPset) :
    etcdKV (GF := GF) γk σ ⊢ |={Em}=> ∃ γ : LinkvNames, linkvInv γ γk ∗ linkvState γ kvInit := by
  iintro Hσ
  imod ghostVar_alloc (GF := GF) ([] : List OpV) with ⟨%γh, Hh⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := GoString × GoString) with ⟨%γp, Hp⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := List (GoString × GoString))
    with ⟨%γr, Hr⟩
  imod ghost_map_insert_persist σ.rev (kvProj σ.kvs) rfl $$ Hr with ⟨Hr, #He⟩
  icases (ghostVar_split_half γh 1 ([] : List OpV)).1 $$ Hh with ⟨Hh1, Hh2⟩
  imod inv_alloc linkvInvN Em (iprop(∃ (h : List OpV) (S : KVSet GoString GoString) (σ : KVState)
      (M : GMap Nat (GoString × GoString)) (nx : Nat),
    ghostVar γh (1 : Qp).half h ∗ etcdKV γk σ ∗ ghostMapAuth γp 1 M ∗ revOwn ⟨γh, γp, γr⟩ σ ∗
    ⌜run (kvM decOp) kvInit h = some S ∧ LinkvOk S σ M nx⌝)) $$ [Hh1 Hσ Hp Hr] with #Hinv
  · inext
    iexists [], kvInit, σ, ∅, 0
    iframe
    isplitl
    · iunfold revOwn
      iexists _
      iframe He Hr
      ipureintro
      exact ⟨GMap.lookup_insert _ _ _, fun n hn => by
        rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl⟩
    ipureintro; exact ⟨rfl, linkvOk_init σ hs he⟩
  imodintro
  iexists ⟨γh, γp, γr⟩
  iunfold linkvInv
  iframe Hinv
  iunfold linkvState
  iexists []
  iframe
  ipureintro; rfl

/-- **A put whose prophecy says `ok`** (see the file header): the update the server fires (at most
once, `kvOpAu1`) commits `lintest`'s update with output `ok`, the store stepped by the put
(`linkvOk_putOk`); its result is the call's continuation. -/
theorem put_ok_au (γ : LinkvNames) (γk : KVNames) (x : Input) (hx : x.Put' = true)
    (Φ : val → IProp GF) :
    linkvInv γ γk ∗ linU γ (boxIn x) Φ ⊢
      kvOpAu1 γk (.put (putOp x.Key' x.Val'))
        (fun _ => iprop(linkvS.ioOk (boxIn x) (boxOut okOut) -∗ Φ #(boxOut okOut))) := by
  have Hm := linkvInvN_mask
  have HE := linkvE_mask
  iintro ⟨#Hinv, HU⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc linkvInv
  iinv Hinv with >Hi Hclose
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
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact HU
  · -- commit: the put takes effect, `lintest`'s update commits with `ok`
    iintro Hσ
    imod Hclose2 with -
    imod (revOwn_put γ x.Key' x.Val' σ) $$ Hrv with Hrv
    imod (fupd_mask_subseteq HE) with Hclose3
    iunfold linU at HU
    imod HU with ⟨%S0, HS, HU⟩
    iunfold linkvState at HS
    icases HS with ⟨%h0, Hh0, %Hr0⟩
    ihave %Heq := ghostVar_agree γ.h h (1 : Qp).half h0 (1 : Qp).half $$ Hh Hh0
    subst Heq
    have HS0 : S0 = S := Option.some.inj (Hr0.symm.trans Hr)
    subst HS0
    obtain ⟨S', HS', Hok'⟩ := linkvOk_putOk Hok x.Key' x.Val'
    have Hst : (linkvS (GF := GF)).M.step S0 (boxIn x, boxOut okOut) = some S' := by
      rw [step_put_ok S0 x hx]; exact HS'
    have Hr' := run_snoc h S0 S' (boxIn x, boxOut okOut) Hr Hst
    imod ghostVar_update_halves (h ++ [(boxIn x, boxOut okOut)]) γ.h h h $$ Hh Hh0
      with ⟨Hh, Hh0⟩
    imod HU $$ %S' %(boxOut okOut) [Hh0] with HΦ
    · isplitl [Hh0]
      · iunfold linkvState
        iexists _
        iframe Hh0
        ipureintro; exact Hr'
      · ipureintro; exact Hst
    imod Hclose3 with -
    imod Hclose $$ [Hh Hσ HM Hrv] with -
    · inext
      iexists _, S', _, M, nx
      iframe
      ipureintro; exact ⟨Hr', Hok'⟩
    imodintro
    iexact HΦ

/-- **A pending put's update** (see the file header): at its firing (if ever) the put takes
effect, its token consumed; the history and the model state do not move (`linkvOk_pend`). -/
theorem put_pend_au (γ : LinkvNames) (γk : KVNames) (n : Nat) (k v : GoString) :
    linkvInv γ γk ∗ pendTok γ n k v ⊢
      kvOpAu1 (GF := GF) γk (.put (putOp k v)) (fun _ => iprop(True)) := by
  have Hm := linkvInvN_mask
  iintro ⟨#Hinv, Htok⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc linkvInv
  iinv Hinv with >Hi Hclose
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
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact Htok
  · iintro Hσ
    imod Hclose2 with -
    imod (revOwn_put γ k v σ) $$ Hrv with Hrv
    iunfold pendTok at Htok
    ihave %Hn := ghost_map_lookup $$ HM Htok
    imod ghost_map_delete $$ HM Htok with HM
    imod Hclose $$ [Hh Hσ HM Hrv] with -
    · inext
      iexists h, S, _, _, nx
      iframe
      ipureintro; exact ⟨Hr, linkvOk_pend Hok n k v Hn⟩
    imodintro
    itrivial

/-- **A put whose prophecy says error** (see the file header): `lintest`'s update commits at
once, the put pending (output `Err`, `linkvOk_putErr`), with the pending put's token. -/
theorem put_err_commit (γ : LinkvNames) (γk : KVNames) (x : Input) (hx : x.Put' = true)
    (Φ : val → IProp GF) :
    linkvInv γ γk ∗ linU γ (boxIn x) Φ ⊢
      |={⊤}=> ∃ n : Nat, (linkvS.ioOk (boxIn x) (boxOut errOut) -∗ Φ #(boxOut errOut)) ∗
        pendTok γ n x.Key' x.Val' := by
  have HE := linkvE_mask_top
  iintro ⟨#Hinv, HU⟩
  unfold linkvInv
  iinv Hinv with >Hi Hclose
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
  obtain ⟨S', HS', Hok'⟩ := linkvOk_putErr Hok x.Key' x.Val'
  have Hst : (linkvS (GF := GF)).M.step S0 (boxIn x, boxOut errOut) = some S' := by
    rw [step_put_err S0 x hx]; exact HS'
  have Hr' := run_snoc h S0 S' (boxIn x, boxOut errOut) Hr Hst
  imod ghostVar_update_halves (h ++ [(boxIn x, boxOut errOut)]) γ.h h h $$ Hh Hh0
    with ⟨Hh, Hh0⟩
  imod ghost_map_insert nx (x.Key', x.Val') (Hok.fresh nx (Nat.le_refl _)) $$ HM with ⟨HM, Htok⟩
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
    iexists _, S', σ, _, nx + 1
    iframe
    ipureintro; exact ⟨Hr', Hok'⟩
  imodintro
  iexists nx
  iframe HΦ
  iunfold pendTok
  iexact Htok

/-- **A get whose prophecy says error** (see the file header): `lintest`'s update commits at
once with output `Err` (`linkvOk_getErr`). -/
theorem get_err_commit (γ : LinkvNames) (γk : KVNames) (x : Input) (hx : x.Put' = false)
    (Φ : val → IProp GF) :
    linkvInv γ γk ∗ linU γ (boxIn x) Φ ⊢
      |={⊤}=> (linkvS.ioOk (boxIn x) (boxOut errOut) -∗ Φ #(boxOut errOut)) := by
  have HE := linkvE_mask_top
  iintro ⟨#Hinv, HU⟩
  unfold linkvInv
  iinv Hinv with >Hi Hclose
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
  obtain ⟨S', HS', Hok'⟩ := linkvOk_getErr Hok x.Key'
  have Hst : (linkvS (GF := GF)).M.step S0 (boxIn x, boxOut errOut) = some S' := by
    rw [step_get_err S0 x hx]; exact HS'
  have Hr' := run_snoc h S0 S' (boxIn x, boxOut errOut) Hr Hst
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
    iexists _, S', σ, M, nx
    iframe
    ipureintro; exact ⟨Hr', Hok'⟩
  imodintro
  iexact HΦ


/-- **A get whose prophecies say `ok` at revision `R`** (see the file header): the read update the
server fires at every committed state from the read index on. At a firing at a state of
revision `R`, if `lintest`'s update is not yet committed (the call invariant's left side), it
commits with the output of the store's value there, and the commit bit records it; a later
firing at revision `R` sees the same store (the revisions' map) and does nothing. Either way the
result says the bit holds the store's value. -/
theorem get_ok_au (γ : LinkvNames) (γk : KVNames) (γc γt : GName) (x : Input) (hx : x.Put' = false)
    (R : w64) (Φ : val → IProp GF) :
    linkvInv γ γk ∗ callInv γ γc γt x R Φ ⊢ kvReadAu γk (getQ γc x R) := by
  have Hm := linkvInvN_mask
  have Hcm := callN_mask
  have HE := linkvE_mask_call
  iintro ⟨#Hinv, #Hc⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc linkvInv
  iinv Hinv with >Hi Hclose
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
      icases Hci with (⟨HU, >Hlc, >Hγc⟩ | ⟨%v, %L, >#Hv, >#HL, >%HvL, Hrest⟩)
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
        obtain ⟨S', HS', Hok'⟩ := linkvOk_getOk Hok x.Key'
        have Hst : (linkvS (GF := GF)).M.step S0 (boxIn x, boxOut (getOut (absKV σ x.Key'))) =
            some S' := by
          rw [step_get_ok S0 x hx]; exact HS'
        have Hr' := run_snoc h S0 S' _ Hr Hst
        imod ghostVar_update_halves (h ++ [(boxIn x, boxOut (getOut (absKV σ x.Key')))]) γ.h h h
          $$ Hh Hh0 with ⟨Hh, Hh0⟩
        imod HU $$ %S' %(boxOut (getOut (absKV σ x.Key'))) [Hh0] with HΦ
        · isplitl [Hh0]
          · iunfold linkvState
            iexists _
            iframe Hh0
            ipureintro; exact Hr'
          · ipureintro; exact Hst
        imod Hclose3 with -
        imod dghostVar_update (some (absKV σ x.Key')) γc none $$ Hγc with Hγc
        imod dghostVar_persist γc 1 _ $$ Hγc with #Hγc
        imod Hclosec $$ [HΦ] with -
        · inext
          iright
          iexists _, (kvProj σ.kvs)
          rw [← Hrev]
          iframe Hγc Hel
          isplitr
          · ipureintro; exact absKV_proj σ x.Key'
          ileft
          iexact HΦ
        imod Hclose $$ [Hh Hσ HM Hrv] with -
        · inext
          iexists _, S', σ, M, nx
          iframe
          ipureintro; exact ⟨Hr', Hok'⟩
        imodintro
        imodintro
        unfold getQ
        iintro %_
        iexact Hγc
      · -- a later firing at revision `R`: the same store, nothing to do
        ihave %HLe := ghostMapElem_agree (uint.nat R) γ.r _ _ _ _ $$ HL [Hel]
        · rw [← Hrev]; iexact Hel
        subst HLe
        imod Hclosec $$ [Hrest] with -
        · inext
          iright
          iexists v, (kvProj σ.kvs)
          rw [← Hrev]
          iframe Hv HL Hrest
          ipureintro; exact HvL
        imod Hclose $$ [Hh Hσ HM Hrv] with -
        · inext
          iexists h, S, σ, M, nx
          iframe
          ipureintro; exact ⟨Hr, Hok⟩
        imodintro
        imodintro
        unfold getQ
        iintro %_
        rw [absKV_proj, ← HvL]
        iexact Hv
    · imod Hclose $$ [Hh Hσ HM Hrv] with -
      · inext
        iexists h, S, σ, M, nx
        iframe
        ipureintro; exact ⟨Hr, Hok⟩
      imodintro
      imodintro
      unfold getQ
      iintro %H
      exact absurd H Hrev

/-- **`Apply` takes the continuation** after the reply: the commit bit holds `v`, so the call
invariant is on its committed side, its continuation still there (`Apply` holds the token). -/
theorem callInv_take (γ : LinkvNames) (γc γt : GName) (x : Input) (R : w64) (Φ : val → IProp GF)
    (v : Option GoString) :
    callInv γ γc γt x R Φ ∗ dghostVar γc DFrac.discard (some v) ∗ dghostVar γt (DFrac.own 1) () ∗
      £ 1 ⊢ |={⊤}=> (linkvS.ioOk (boxIn x) (boxOut (getOut v)) -∗ Φ #(boxOut (getOut v))) := by
  iintro ⟨#Hc, #Hv, Htok, Hlc⟩
  unfold callInv
  iinv Hc with Hci Hclosec
  icases Hci with (⟨-, -, >Hγc⟩ | ⟨%v', %L, >#Hv', >#HL, >%HvL, Hrest⟩)
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
        iexists v, L
        iframe Hv HL
        isplitr
        · ipureintro; exact HvL
        iright
        iexact Htok
      imodintro
      iexact HΦ
    · ihave %Hbad := dghostVar_valid_2 γt _ _ _ _ $$ Htok Htok'
      exfalso
      have h := DFrac.valid_own_op Hbad.1
      exact absurd h (by decide)

end proofs

end linkv
end EtcdGrove
end Perennial
