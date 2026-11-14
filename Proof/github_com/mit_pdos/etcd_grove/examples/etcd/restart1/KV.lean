/-
**restart1's KV ghost state** (restart S7.5, step d, 2026-11-14; `notes/restart-s7-handoff.md`):
an invariant over the KV state's ghost variable (`etcdKV`) and a counter of the puts that fired, and
the updates the program's in-process `Put`s and its `Range` carry. Lean-first (no Rocq counterpart);
restart3's single-key `client.putGetInv` is the model.

**The keys** (`keyOf`, `valOf`): `restart1`'s `key(i)` and `value(i)`, `"k"` and `"v"` followed by the
byte `i`, for `i < NPuts` (`r1NPuts`, `11`). Every key is in the `Range`'s `["k", "l")`, and they are
in the order of `i`.

**The invariant** (`r1Inv`): the state `σ` and a counter `c ≤ NPuts` (a monotone counter at `γc`,
half its authority in the invariant), such that the key-values of `σ` in `["k", "l")` are exactly the
first `c` pairs `(keyOf i, valOf i)`, in order (`r1Ok`). The program is the only writer, and it puts
sequentially: the other half of the counter's authority is the driver's, and the put of index `c`
carries it (`r1PutAu`): when it fires, the counter is `c` and becomes `c + 1`. It fires at most
once (`kvOpAu1`), so a put that failed but fires later still finds the counter at `c`, and leaves
the invariant true (the program then checks nothing).

**The read** (`r1ReadAu`): after the `NPuts` puts returned, the driver holds the counter's lower
bound `NPuts`; a read update fired at any later state then finds `c = NPuts` (the invariant caps
it), so the state's range is exactly the `NPuts` pairs (`r1Ok σ r1NPuts`).

**Across the restart**: the invariant reads only the KV state's ghost variable, which
`restartNames` keeps (`restartNames_st`), so it is the restarted member's too (`r1Inv_st`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.restart1.Defs
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.txn.ClientLaws
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.NewServerAlloc

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_restart1

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.raft.v3

section pure

/-- `restart1`'s `NPuts`. -/
abbrev r1NPuts : Nat := 11

/-- `restart1`'s `key(i)`: `"k"` followed by the byte `i`. -/
def keyOf (i : Nat) : GoString := [W8 107, W8 (i : Int)]

/-- `restart1`'s `value(i)`: `"v"` followed by the byte `i`. -/
def valOf (i : Nat) : GoString := [W8 118, W8 (i : Int)]

/-- A key in the `Range`'s `["k", "l")` (the server's selection, `inRange`). -/
def inR1 (v : EtcdKv) : Bool := inRange go!"k" go!"l" v.key

/-- **The first `c` pairs** `(keyOf i, valOf i)`, in order. -/
def r1Pairs (c : Nat) : List (GoString × GoString) :=
  (List.range c).map fun i => (keyOf i, valOf i)

/-- **The state's range is the first `c` pairs** (see the file header). -/
def r1Ok (σ : KVState) (c : Nat) : Prop :=
  (σ.kvs.filter inR1).map (fun v => (v.key, v.value)) = r1Pairs c

/-- The put of index `i`: `restart1`'s `&PutRequest{Key: key(i), Value: value(i)}`. -/
abbrev r1PutOp (i : Nat) : OpFull := txn.putOpOf (keyOf i) (valOf i) (W64 0) false false false

theorem keyOf_inR1 (i : Nat) : inRange go!"k" go!"l" (keyOf i) = true := by
  have hk : (go!"k" : GoString) = [W8 107] := rfl
  have hl : (go!"l" : GoString) = [W8 108] := rfl
  have h1 : ¬ go.GoStringLt (keyOf i) go!"k" := by
    intro h
    rw [hk] at h
    unfold keyOf go.GoStringLt at h
    cases h with
    | cons h' => exact go.goStringLt_not_nil _ h'
    | rel h' => exact absurd h' (Int.lt_irrefl _)
  have h2 : go.GoStringLt (keyOf i) go!"l" := by rw [hl]; exact List.Lex.rel (by decide)
  have h3 : (go!"l" : GoString) ≠ [] := by rw [hl]; simp
  have h4 : (go!"l" : GoString) ≠ [W8 0] := by rw [hl]; decide
  simp [inRange, h1, h2, h3, h4]

theorem keyOf_lt {i j : Nat} (hij : i < j) (hj : j < 256) :
    go.GoStringLt (keyOf i) (keyOf j) := by
  unfold keyOf go.GoStringLt
  refine List.Lex.cons (List.Lex.rel ?_)
  word

/-- `btInsert` of an item above every item appends it. -/
theorem btInsert_of_gt_all {v : EtcdKv} :
    ∀ {l : List EtcdKv}, (∀ x ∈ l, etcdKvLess x v) → btInsert etcdKvLess v l = l ++ [v]
  | [], _ => rfl
  | w :: ws, h => by
    have hwv := h w List.mem_cons_self
    simp only [btInsert, hwv, ↓reduceIte, List.cons_append,
      btInsert_of_gt_all (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem r1Pairs_succ (c : Nat) : r1Pairs (c + 1) = r1Pairs c ++ [(keyOf c, valOf c)] := by
  simp [r1Pairs, List.range_succ]

theorem r1Ok_keys {σ : KVState} {c : Nat} (h : r1Ok σ c) :
    ∀ x ∈ σ.kvs.filter inR1, ∃ i < c, x.key = keyOf i := by
  intro x hx
  have hm : (x.key, x.value) ∈ r1Pairs c := by
    rw [← h]; exact List.mem_map.2 ⟨x, hx, rfl⟩
  obtain ⟨i, hi, he⟩ := List.mem_map.1 hm
  exact ⟨i, List.mem_range.1 hi, (Prod.mk.inj he).1.symm⟩

/-- **The put of index `c` extends the range by its pair** (see the file header). -/
theorem r1Ok_put (σ : KVState) (c : Nat) (hc : c < 256) (h : r1Ok σ c) :
    r1Ok (kvOpStep (.put (r1PutOp c)) σ) (c + 1) := by
  have hk : (kvOpStep (.put (r1PutOp c)) σ).kvs =
      putKv (W64 ((σ.rev + 1 : Nat) : Int)) (keyOf c) (valOf c) (W64 0) σ.kvs := by
    simp [kvOpStep, KVState.commit_kvs, KVState.leaseMissing, txn.needsPrev, mvcc.applyChanges,
      mvcc.applyChange, txn.putChangeOf, txn.putValOf, txn.putLeaseOf, txn.putOpOf]
  unfold r1Ok
  rw [hk, txn.putKv_eq]
  have hnk := txn.putNv_key (W64 ((σ.rev + 1 : Nat) : Int)) (keyOf c) (valOf c) (W64 0) σ.kvs
  have hnv : (txn.putNv (W64 ((σ.rev + 1 : Nat) : Int)) (keyOf c) (valOf c) (W64 0) σ.kvs).value =
      valOf c := by
    simp only [txn.putNv]; split <;> rfl
  generalize txn.putNv (W64 ((σ.rev + 1 : Nat) : Int)) (keyOf c) (valOf c) (W64 0) σ.kvs = nv
    at hnk hnv ⊢
  have hresp : txn.RespEquiv etcdKvLess inR1 := by
    intro a b hab hba
    have : a.key = b.key := by
      have := etcdKvLess_swo
      unfold etcdKvLess at hab hba
      exact go.goStringLt_eq_of_not_lt hab hba
    simp [inR1, this]
  rw [txn.filter_btInsert etcdKvLess_swo inR1 hresp nv σ.kvs σ.kvs_sorted]
  have hin : inR1 nv = true := by unfold inR1; rw [hnk]; exact keyOf_inR1 c
  rw [if_pos hin, btInsert_of_gt_all, List.map_append, h, r1Pairs_succ]
  · simp [hnk, hnv]
  · intro x hx
    obtain ⟨i, hi, hx⟩ := r1Ok_keys h x hx
    unfold etcdKvLess; rw [hx, hnk]; exact keyOf_lt hi hc

/-- The `Range` after the restart: `restart1`'s `&RangeRequest{Key: "k", RangeEnd: "l"}`. -/
abbrev r1RangeOp : OpFull :=
  txn.rangeOpOf go!"k" go!"l" (W64 0) (W64 0) (W32 0) (W32 0) false false false (W64 0) (W64 0)
    (W64 0) (W64 0)

/-- **The `Range`'s answer is the state's key-values in `["k", "l")`**, in key order. -/
theorem srvRangeOk_r1 (s kvs : List EtcdKv) (more : Bool)
    (h : txn.srvRangeOk r1RangeOp s kvs more) : kvs = s.filter inR1 := by
  obtain ⟨L, hsort, hmore, hkvs⟩ := h
  have hpre : txn.srvPre r1RangeOp s = s.filter inR1 := by
    have hr : txn.kvRead false = id := by funext v; simp [txn.kvRead]
    unfold txn.srvPre
    simp [txn.rangeLimitOf, txn.hasRevFilters, mvcc.limitOf, mvcc.takeLimit, txn.fastKeysOnly,
      rangeIn, hr]
    apply List.filter_congr
    intro v _
    simp [kvFilterOk, inR1]
  have hord : r1RangeOp.effSortOrder = W64 0 := by
    simp [OpFull.effSortOrder]
  have hL : L = txn.srvPre r1RangeOp s := by
    obtain ⟨-, -, -, h4⟩ := hsort
    exact h4 (by rw [hord]; decide) (by rw [hord]; decide)
  have hm : txn.srvMore r1RangeOp L = false := by
    simp [txn.srvMore]
  rw [hkvs]
  unfold txn.srvTrunc
  rw [hm, hL, hpre]
  have hid : txn.respKv r1RangeOp = id := by funext v; simp [txn.respKv]
  simp [hid]

/-- The range's key-values, by index: the `i`-th is `keyOf i ↦ valOf i`. -/
theorem r1Ok_get (σ : KVState) (h : r1Ok σ r1NPuts) :
    (σ.kvs.filter inR1).length = r1NPuts ∧
      ∀ i (hi : i < r1NPuts) v, (σ.kvs.filter inR1)[i]? = some v →
        v.key = keyOf i ∧ v.value = valOf i := by
  have hl := congrArg List.length h
  simp only [List.length_map, r1Pairs, List.length_range] at hl
  refine ⟨hl, fun i hi v hv => ?_⟩
  have h2 := congrArg (fun l => l[i]?) h
  simp only [List.getElem?_map, hv, r1Pairs, List.getElem?_range hi, Option.map_some] at h2
  exact ⟨(Prod.mk.inj (Option.some.inj h2)).1, (Prod.mk.inj (Option.some.inj h2)).2⟩

end pure

section inv
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- A counter's whole authority is two halves. -/
theorem monoNat_halves (γ : GName) (n : Nat) :
    (monoNatAuthOwn (GF := GF) γ 1 n : IProp GF) ⊣⊢
      monoNatAuthOwn γ (1 : Qp).half n ∗ monoNatAuthOwn γ (1 : Qp).half n := by
  conv => lhs; rw [← Qp.half_add_half (1 : Qp)]
  exact (monoNatAuthOwn_fractional (GF := GF) γ n).fractional _ _

/-- The namespace of `restart1`'s KV invariant. -/
def r1N : Namespace := nroot .@ "restart1_kv"

theorem r1N_mask : (↑r1N : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩,
    fun h => ndot_ne_disjoint nroot (by decide) p ⟨hp, h⟩⟩

/-- **`restart1`'s KV invariant** (see the file header), at the KV names `γk` and the counter
`γc`. -/
def r1Inv (γk : KVNames) (γc : GName) : IProp GF :=
  inv r1N iprop(∃ (σ : KVState) (c : Nat), etcdKV γk σ ∗ monoNatAuthOwn γc (1 : Qp).half c ∗
    ⌜c ≤ r1NPuts ∧ r1Ok σ c⌝)

instance r1Inv_persistent (γk : KVNames) (γc : GName) : Persistent (r1Inv (GF := GF) γk γc) := by
  unfold r1Inv; infer_instance

/-- **The invariant reads only the KV state's ghost variable**: at KV names sharing it, the same. -/
theorem r1Inv_st (γk γk' : KVNames) (h : γk.st = γk'.st) (γc : GName) :
    r1Inv (GF := GF) γk γc = r1Inv γk' γc := by
  unfold r1Inv
  simp only [etcdKV_congr γk γk' h]

/-- **The invariant allocated** at a state with no key in the range (the bootstrap log's: its
entries are conf changes), the driver's half of the counter at `0`. -/
theorem r1Inv_alloc (γk : KVNames) (σ : KVState) (hσ : σ.kvs.filter inR1 = []) (E : CoPset) :
    etcdKV (GF := GF) γk σ ⊢ |={E}=> ∃ γc, r1Inv γk γc ∗ monoNatAuthOwn γc (1 : Qp).half 0 := by
  iintro Hσ
  imod (mono_nat_own_alloc (GF := GF) 0) with ⟨%γc, Hc, -⟩
  icases (monoNat_halves γc 0).1 $$ Hc with ⟨Hc1, Hc2⟩
  imod inv_alloc r1N E iprop(∃ (σ : KVState) (c : Nat), etcdKV γk σ ∗
      monoNatAuthOwn γc (1 : Qp).half c ∗ ⌜c ≤ r1NPuts ∧ r1Ok σ c⌝) $$ [Hσ Hc1] with Hinv
  · inext; iexists σ, 0; iframe Hσ Hc1; ipureintro
    exact ⟨Nat.zero_le _, by simp [r1Ok, hσ, r1Pairs]⟩
  imodintro
  iexists γc
  iframe Hc2
  iunfold r1Inv
  iexact Hinv

/-- **The update of the put of index `c`** (see the file header): it carries the driver's half of
the counter at `c`, and its result is the half at `c + 1`. -/
theorem r1PutAu (γk : KVNames) (γc : GName) (c : Nat) (hc : c < r1NPuts) :
    r1Inv (GF := GF) γk γc ∗ monoNatAuthOwn γc (1 : Qp).half c ⊢
      kvOpAu1 γk (.put (r1PutOp c)) (fun _ => monoNatAuthOwn γc (1 : Qp).half (c + 1)) := by
  have Hm := r1N_mask
  iintro ⟨#Hinv, Hd⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc
  iunfold r1Inv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %c', Hσ, Hc, %Hok⟩
  ihave %Hag := monoNatAuthOwn_agree γc (1 : Qp).half (1 : Qp).half c c' $$ Hd Hc
  obtain ⟨-, rfl⟩ := Hag
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑r1N from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ, c; iframe; ipureintro; exact Hok
    imodintro
    iframe
  · iintro ⟨Hσ, -⟩
    imod Hclose2 with -
    imod (mono_nat_own_update (GF := GF) (γ := γc) (c + 1) (Nat.le_succ c))
      $$ [Hd Hc] with ⟨Hf, -⟩
    · iapply (monoNat_halves γc c).2; iframe
    icases (monoNat_halves γc (c + 1)).1 $$ Hf with ⟨Hc, Hd⟩
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists _, (c + 1); iframe Hσ Hc; ipureintro
      exact ⟨hc, r1Ok_put σ c (by simp only [r1NPuts] at hc; omega) Hok.2⟩
    imodintro
    iexact Hd

/-- **The read update after the `NPuts` puts fired** (see the file header): its result is that the
state's range is exactly the `NPuts` pairs. -/
theorem r1ReadAu (γk : KVNames) (γc : GName) :
    r1Inv (GF := GF) γk γc ∗ monoNatLbOwn γc r1NPuts ⊢
      kvReadAu γk (fun σ => iprop(⌜r1Ok σ r1NPuts⌝)) := by
  have Hm := r1N_mask
  iintro ⟨#Hinv, #Hlb⟩
  unfold kvReadAu kvAu
  imodintro
  iauintro
  unfold atomic_acc
  iunfold r1Inv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with ⟨%σ, %c, Hσ, Hc, %Hok⟩
  ihave %Hv := monoNatLbOwn_valid γc _ c r1NPuts $$ Hc Hlb
  have hc : c = r1NPuts := by omega
  subst hc
  iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑r1N from
    Std.LawfulSet.empty_subset)
  iintro Hclose2
  isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iexists σ
  iframe Hσ
  isplit
  · iintro Hσ
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ, r1NPuts; iframe; ipureintro; exact Hok
    imodintro
    iempintro
  · iintro ⟨Hσ, -⟩
    imod Hclose2 with -
    imod Hclose $$ [Hσ Hc] with -
    · inext; iexists σ, r1NPuts; iframe; ipureintro; exact Hok
    imodintro
    iintro !>
    ipureintro; exact Hok.2
end inv

end etcd_restart1
end EtcdGrove
end Perennial
