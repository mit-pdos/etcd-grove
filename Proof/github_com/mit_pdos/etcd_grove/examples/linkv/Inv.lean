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
invariant `linkvInv γ γk` (at `linkvN`), which also holds the server's `etcdKV γk σ` (the client's
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

A get whose prophecy says `ok` has no step here: see `Proof/.../linkv/Apply.lean`.
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

/-- The instance's invariant's namespace. -/
def linkvN : Namespace := nroot .@ "linkv"

/-- **`Apply`'s mask** (`applySpec`'s `Eapp`): the server's invariants open where it fires a
client's update (`kvAu1`'s outer mask leaves them out), and the instance's. -/
def linkvE : CoPset := ↑srvRaftN ∪ ↑kvN ∪ ↑linkvN

theorem linkvN_mask : (↑linkvN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

theorem linkvE_mask : ⊤ \ linkvE ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff] at hp
  obtain ⟨-, hn⟩ := hp
  unfold linkvE at hn
  simp only [Iris.Std.LawfulSet.mem_union, not_or] at hn
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, hn.1.1⟩, hn.1.2⟩, hn.2⟩

theorem linkvE_mask_top : ⊤ \ linkvE ⊆ ⊤ \ ↑linkvN := by
  intro p hp
  have := linkvE_mask p hp
  rw [Iris.Std.LawfulSet.mem_diff] at this ⊢
  exact ⟨CoPset.mem_full, this.2⟩

/-- **The library's abstract state** (`lintest`'s `libState`; see the file header). -/
def linkvState (γ : LinkvNames) (S : KVSet GoString GoString) : IProp GF :=
  iprop(∃ h : List OpV, ghostVar γ.h (1 : Qp).half h ∗ ⌜run (kvM decOp) kvInit h = some S⌝)

/-- **A pending put's token** (exclusive): the put `k ↦ v` committed as pending under `n`. -/
def pendTok (γ : LinkvNames) (n : Nat) (k v : GoString) : IProp GF :=
  ghostMapElem γ.p n (DFrac.own 1) (k, v)

/-- **The instance's invariant** (see the file header). -/
def linkvInv (γ : LinkvNames) (γk : KVNames) : IProp GF :=
  inv linkvN iprop(∃ (h : List OpV) (S : KVSet GoString GoString) (σ : KVState)
      (M : GMap Nat (GoString × GoString)) (nx : Nat),
    ghostVar γ.h (1 : Qp).half h ∗ etcdKV γk σ ∗ ghostMapAuth γ.p 1 M ∗
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

/-- **The invariant, allocated** from `etcdKV` at a sorted state with an empty store; with the
library's initial state. -/
theorem linkvInv_alloc (γk : KVNames) (σ : KVState) (hs : σ.kvs.Pairwise etcdKvLess)
    (he : absKV σ = fun _ => none) (Em : CoPset) :
    etcdKV (GF := GF) γk σ ⊢ |={Em}=> ∃ γ : LinkvNames, linkvInv γ γk ∗ linkvState γ kvInit := by
  iintro Hσ
  imod ghostVar_alloc (GF := GF) ([] : List OpV) with ⟨%γh, Hh⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := GoString × GoString) with ⟨%γp, Hp⟩
  icases (ghostVar_split_half γh 1 ([] : List OpV)).1 $$ Hh with ⟨Hh1, Hh2⟩
  imod inv_alloc linkvN Em (iprop(∃ (h : List OpV) (S : KVSet GoString GoString) (σ : KVState)
      (M : GMap Nat (GoString × GoString)) (nx : Nat),
    ghostVar γh (1 : Qp).half h ∗ etcdKV γk σ ∗ ghostMapAuth γp 1 M ∗
    ⌜run (kvM decOp) kvInit h = some S ∧ LinkvOk S σ M nx⌝)) $$ [Hh1 Hσ Hp] with #Hinv
  · inext
    iexists [], kvInit, σ, ∅, 0
    iframe
    ipureintro; exact ⟨rfl, linkvOk_init σ hs he⟩
  imodintro
  iexists ⟨γh, γp⟩
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
  have Hm := linkvN_mask
  have HE := linkvE_mask
  iintro ⟨#Hinv, HU⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc linkvInv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · -- abort: nothing moved
    iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM] with -
    · inext
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact HU
  · -- commit: the put takes effect, `lintest`'s update commits with `ok`
    iintro Hσ
    imod Hclose2 with -
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
    imod Hclose $$ [Hh Hσ HM] with -
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
  have Hm := linkvN_mask
  iintro ⟨#Hinv, Htok⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc linkvInv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, %Hok⟩
  obtain ⟨Hr, Hok⟩ := Hok
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑linkvN from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hh Hσ HM] with -
    · inext
      iexists h, S, σ, M, nx
      iframe
      ipureintro; exact ⟨Hr, Hok⟩
    imodintro
    iexact Htok
  · iintro Hσ
    imod Hclose2 with -
    iunfold pendTok at Htok
    ihave %Hn := ghost_map_lookup $$ HM Htok
    imod ghost_map_delete $$ HM Htok with HM
    imod Hclose $$ [Hh Hσ HM] with -
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
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, %Hok⟩
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
  imod Hclose $$ [Hh Hσ HM] with -
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
  icases Hi with ⟨%h, %S, %σ, %M, %nx, Hh, Hσ, HM, %Hok⟩
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
  imod Hclose $$ [Hh Hσ HM] with -
  · inext
    iexists _, S', σ, M, nx
    iframe
    ipureintro; exact ⟨Hr', Hok'⟩
  imodintro
  iexact HΦ

end proofs

end linkv
end EtcdGrove
end Perennial
