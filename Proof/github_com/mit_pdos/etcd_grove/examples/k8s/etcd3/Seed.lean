/-
Lean-first (no Rocq counterpart).

# k8setcd3: the seeded store (stage 6g; stage 7e-4: the workload's keys, the history)

`Main` seeds the keys `ns-1/pod-1` and `ns-2/pod-2` with value `x` in the older encoding
(`seedOne`: a client `Put` of `encodeV0` of the key's object at the store key, D30g) on a new
member's start state (no key, at revision `1`). The pure part: the two puts' states (`σs2`: the
first key at revision 2, the second at 3, `σs2_at_kvs` at every revision) and the driver's seeded
store with its history (`g0s`: the stores at revisions 1, 2, 3), related as the instance's
invariant takes them (`kvWf`, `kvWfHist`, `keysOk`, `KRelH`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.InvSteps

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI k8s go_etcd_io.etcd.server.v3.etcdserver
open github_com.anishathalye.porcupine github_com.anishathalye.porcupine.Theory
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3 (Input Output Obj item mstore)

section pure
variable [GooseExts]

/-- The seed keys. -/
abbrev kA : GoString := go!"ns-1/pod-1"
abbrev kB : GoString := go!"ns-2/pod-2"

/-- `seedOne`'s object of the key `k`: its namespace and name (`splitKey`), value `x`, no UID, node
or app. -/
def seedObj (k : GoString) : Obj :=
  ⟨(splitKeyL k).1, (splitKeyL k).2, go!"", go!"x", go!"", go!"", W64 0, false⟩

/-- A seed key's stored value: its object in the older encoding (`encodeV0`). -/
def v0 (k : GoString) : GoString := encodeWith tagV0 (seedObj k)

/-- `seedOne`'s put of the key `k`. -/
def seedOp (k : GoString) : KVOp := .put (linkv.putOp (mkeyL k) (v0 k))

/-- `seedOne`'s item of the key `k` at the revision `rv`. -/
def seedItem (k : GoString) (rv : w64) : item :=
  ⟨k, ⟨(splitKeyL k).1, (splitKeyL k).2, go!"", go!"x", go!"", go!"", rv, false⟩, false⟩

theorem splitKeyL_kA : splitKeyL kA = (go!"ns-1", go!"pod-1") := by
  unfold splitKeyL; decide

theorem splitKeyL_kB : splitKeyL kB = (go!"ns-2", go!"pod-2") := by
  unfold splitKeyL; decide

/-- The seeds' store objects. -/
def dA : DObj := ⟨go!"ns-1", go!"pod-1", go!"", go!"x", go!"", go!"", by decide⟩
def dB : DObj := ⟨go!"ns-2", go!"pod-2", go!"", go!"x", go!"", go!"", by decide⟩

theorem seedObj_kA : seedObj kA = dA.toObj 0 := by unfold seedObj; rw [splitKeyL_kA]; rfl
theorem seedObj_kB : seedObj kB = dB.toObj 0 := by unfold seedObj; rw [splitKeyL_kB]; rfl

theorem seedItem_kA (rv : w64) : seedItem kA rv = ⟨kA, dA.toObj rv, false⟩ := by
  unfold seedItem; rw [splitKeyL_kA]; rfl
theorem seedItem_kB (rv : w64) : seedItem kB rv = ⟨kB, dB.toObj rv, false⟩ := by
  unfold seedItem; rw [splitKeyL_kB]; rfl

theorem tag_ne (a b : Obj) : encodeWith tagV1 a ≠ encodeWith tagV0 b := by
  intro h
  have := congrArg (fun l => l[1]?) h
  simp [encodeWith, putF, tagV0, tagV1] at this

/-- The driver's codec reads a seed's value as its object, not canonical. -/
theorem dec_v0A : driverCodec.dec (v0 kA) = some (dA, false) := by
  unfold v0; rw [seedObj_kA]
  simp only [ObjCodec.dec, driverCodec, decodeObjD_encode tagV0 (.inr rfl) dA 0, Option.map_some,
    Bool.not_false, Bool.true_and]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  exact Bool.eq_false_iff.2 (fun h => tag_ne _ _ (of_decide_eq_true h))

theorem dec_v0B : driverCodec.dec (v0 kB) = some (dB, false) := by
  unfold v0; rw [seedObj_kB]
  simp only [ObjCodec.dec, driverCodec, decodeObjD_encode tagV0 (.inr rfl) dB 0, Option.map_some,
    Bool.not_false, Bool.true_and]
  simp only [Option.some.injEq, Prod.mk.injEq, true_and]
  exact Bool.eq_false_iff.2 (fun h => tag_ne _ _ (of_decide_eq_true h))

/-- A new member's start state (the start log's): no key, at revision `1`. -/
def σb : KVState := kvStateOf [[], []]

/-- The seeded key-values. -/
def kvA : EtcdKv := ⟨mkeyL kA, W64 2, W64 2, W64 1, v0 kA, W64 0⟩
def kvB : EtcdKv := ⟨mkeyL kB, W64 3, W64 3, W64 1, v0 kB, W64 0⟩

/-- After the seeds. -/
def σs1 : KVState := kvOpStep (seedOp kA) σb
def σs2 : KVState := kvOpStep (seedOp kB) σs1

theorem seed_step1 : kvOpStep (seedOp kA) σb = σs1 := rfl

theorem seed_step2 : kvOpStep (seedOp kB) σs1 = σs2 := rfl

theorem σb_rev : σb.rev = 1 := by unfold σb; rw [kvStateOf_rev]; rfl

theorem σs1_rev : σs1.rev = 2 := by
  unfold σs1 seedOp; rw [linkv.kvOpStep_put_rev, σb_rev]

theorem σs1_kvs : σs1.kvs = [kvA] := by
  unfold σs1 seedOp; rw [linkv.kvOpStep_put_kvs, σb, kvStateOf_kvs, kvStateOf_rev]; rfl

theorem σs2_rev : σs2.rev = 3 := by
  unfold σs2 seedOp; rw [linkv.kvOpStep_put_rev, σs1_rev]

theorem σs2_kvs : σs2.kvs = [kvA, kvB] := by
  unfold σs2 seedOp; rw [linkv.kvOpStep_put_kvs, σs1_kvs, σs1_rev]; rfl

theorem absSt_σs2 : linkv.absSt σs2 = ⟨linkv.absM [kvA, kvB], 3⟩ := by
  unfold linkv.absSt; rw [σs2_kvs, σs2_rev]

/-- The driver's seeded items (`seedOne`'s). -/
abbrev itA : item := seedItem kA (W64 2)
abbrev itB : item := seedItem kB (W64 3)

/-- The driver's stores at the revisions `1` (empty), `2` and `3`. -/
def st1 : GSt := ⟨[], W64 1⟩
def st2 : GSt := ⟨setItemL [] itA, W64 2⟩
def st3 : GSt := ⟨setItemL (setItemL [] itA) itB, W64 3⟩

/-- **The driver's seeded store** (`seed`'s result), with its history. -/
def g0s : HSt := ⟨st3, [st1, st2, st3]⟩

theorem st2_items : st2.items = [itA] := by rfl

theorem st3_items : st3.items = [itA, itB] := by rfl

end pure

section rel
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

/-- The seeded key-values at each revision: none at `0` and `1`, the first seed's at `2`, both
after. -/
def seedKvs (r : Nat) : List EtcdKv := if r ≤ 1 then [] else if r = 2 then [kvA] else [kvA, kvB]

theorem σs2_at_kvs (r : Nat) (hr : r ≤ 3) : (σs2.at r).kvs = seedKvs r := by
  have h1 : k8s.KvNext σb σs1 := k8s.kvNext_step _ _ (by simp [seedOp, KVOp.isKV])
  have h2 : k8s.KvNext σs1 σs2 := k8s.kvNext_step _ _ (by simp [seedOp, KVOp.isKV])
  unfold seedKvs
  by_cases e3 : r = 3
  · subst e3
    rw [show σs2.at 3 = σs2.store by rw [← σs2_rev]; rfl]
    exact σs2_kvs
  rw [kvNext_at h2 r (by rw [σs1_rev]; omega)]
  by_cases e2 : r = 2
  · subst e2
    rw [show σs1.at 2 = σs1.store by rw [← σs1_rev]; rfl]
    exact σs1_kvs
  rw [kvNext_at h1 r (by rw [σb_rev]; omega), if_pos (by omega)]
  by_cases e1 : r = 1
  · subst e1
    rw [show σb.at 1 = σb.store by rw [← σb_rev]; rfl]
    exact (kvStateOf_kvs _).trans rfl
  · obtain rfl : r = 0 := by omega
    rw [KVState.at_kvs σb 0 (Nat.le_refl _)]
    simp only [σb, kvStateOf, runFrom, List.take_zero]
    rw [show mvcc.stateAt [[], []] 0 = [] from rfl]
    exact kvs_storeOf [] List.Pairwise.nil

theorem mkeyA_ne (n : GoString) (h : n ≠ kA) : ¬ mkeyL kA = mkeyL n :=
  fun e => h (mkeyL_inj e).symm

theorem mkeyB_ne (n : GoString) (h : n ≠ kB) : ¬ mkeyL kB = mkeyL n :=
  fun e => h (mkeyL_inj e).symm

theorem absK_seed (L : List EtcdKv) (rv : Nat) (k : GoString) (kv : EtcdKv) (d : DObj)
    (hL : linkv.absM L (mkeyL k) = some (linkv.absVR kv))
    (hd : driverCodec.dec kv.value = some (d, false)) :
    (absK driverCodec.dec kpfxD ⟨linkv.absM L, rv⟩).items (mkeyL k) =
      some ⟨d, uint.nat kv.modRev, false⟩ := by
  have hp : kpfxD <+: mkeyL k := ⟨go!"/" ++ k, rfl⟩
  simp only [absK, if_pos hp, hL, Option.bind_some, itemOf, linkv.absVR, hd, Option.map_some]

theorem absK_none (L : List EtcdKv) (rv : Nat) (k : GoString)
    (hL : linkv.absM L (mkeyL k) = none) :
    (absK driverCodec.dec kpfxD ⟨linkv.absM L, rv⟩).items (mkeyL k) = none := by
  simp only [absK, hL, Option.bind_none, ite_self]

theorem krelS_st1 (s : KVStore) (hs : s.kvs = []) : KRelS s 1 st1 := by
  refine ⟨by simp [st1, SortedI], rfl, fun n => ?_⟩
  rw [hs, absK_none _ _ _ (by simp [linkv.absM, mvcc.findKey])]
  simp [st1, lookupL, PairRelH]

theorem krelS_st2 (s : KVStore) (hs : s.kvs = [kvA]) : KRelS s 2 st2 := by
  have hits : st2.items = [⟨kA, dA.toObj (W64 2), false⟩] := by simp only [st2_items, itA, seedItem_kA]
  refine ⟨by rw [hits]; simp only [SortedI, List.map]; decide, rfl, fun n => ?_⟩
  rw [hs, hits]
  by_cases ha : n = kA
  · subst ha
    rw [absK_seed [kvA] 2 kA kvA dA (by simp [linkv.absM, mvcc.findKey, kvA]) dec_v0A]
    simp [lookupL, PairRelH, ItemRelH, kvA]
  rw [absK_none _ _ _ (by simp [linkv.absM, mvcc.findKey, kvA, mkeyA_ne n ha])]
  simp [lookupL, PairRelH, Ne.symm ha]

theorem krelS_st3 (s : KVStore) (hs : s.kvs = [kvA, kvB]) : KRelS s 3 st3 := by
  have hits : st3.items = [⟨kA, dA.toObj (W64 2), false⟩, ⟨kB, dB.toObj (W64 3), false⟩] := by
    simp only [st3_items, itA, itB, seedItem_kA, seedItem_kB]
  refine ⟨by rw [hits]; simp only [SortedI, List.map]; decide, rfl, fun n => ?_⟩
  rw [hs, hits]
  by_cases ha : n = kA
  · subst ha
    rw [absK_seed [kvA, kvB] 3 kA kvA dA (by simp [linkv.absM, mvcc.findKey, kvA]) dec_v0A]
    simp [lookupL, PairRelH, ItemRelH, kvA]
  by_cases hb : n = kB
  · subst hb
    rw [absK_seed [kvA, kvB] 3 kB kvB dB
      (by simp [linkv.absM, mvcc.findKey, kvA, kvB, mkeyA_ne kB (by decide)]) dec_v0B]
    simp [lookupL, PairRelH, ItemRelH, kvB]
  rw [absK_none _ _ _ (by simp [linkv.absM, mvcc.findKey, kvA, kvB, mkeyA_ne n ha, mkeyB_ne n hb])]
  simp [lookupL, PairRelH, Ne.symm ha, Ne.symm hb]

/-- **The seeded state is the driver's seeded store and history.** -/
theorem seed_krel : KRelH g0s σs2 := by
  refine ⟨by rw [σs2_rev]; decide, ?_, ?_, ?_⟩
  · rw [σs2_rev]
    exact krelS_st3 _ σs2_kvs
  · intro r h1 h3
    rw [σs2_rev] at h3
    have e := σs2_at_kvs r h3
    have : r = 1 ∨ r = 2 ∨ r = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact krelS_st1 _ e
    · exact krelS_st2 _ e
    · exact krelS_st3 _ e
  · intro r hr v hv
    rw [σs2_rev] at hr
    rw [σs2_at_kvs r hr] at hv
    unfold seedKvs at hv
    repeat' split at hv
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    all_goals (repeat' rcases hv with rfl | hv) <;> (simp only [kvA, kvB]; decide)

theorem g0s_len : g0s.hist.length = σs2.rev := by rw [σs2_rev]; rfl

/-- **The seeded state's keys are the workload's.** -/
theorem seed_keys : keysOk σs2 := by
  intro r hr v hv
  rw [σs2_rev] at hr
  rw [σs2_at_kvs r hr] at hv
  unfold seedKvs at hv
  repeat' split at hv
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  all_goals (repeat' rcases hv with rfl | hv) <;> simp [kvA, kvB]

theorem decA_ne : driverCodec.dec kvA.value ≠ none := by
  show driverCodec.dec (v0 kA) ≠ none; rw [dec_v0A]; simp

theorem decB_ne : driverCodec.dec kvB.value ≠ none := by
  show driverCodec.dec (v0 kB) ≠ none; rw [dec_v0B]; simp

theorem modA : uint.nat kvA.modRev = 2 := rfl
theorem modB : uint.nat kvB.modRev = 3 := rfl

/-- **The seeded state's history is the store's.** -/
theorem seed_wfHist (c : StoreCfg GF DObj) (hc : c.S = driverSpec) : kvWfHist c σs2 := by
  intro r hr v hv
  rw [σs2_rev] at hr
  rw [σs2_at_kvs r hr] at hv
  have hd : c.S.dec = driverCodec.dec := by rw [hc]; rfl
  rw [hd]
  unfold seedKvs at hv
  by_cases h1 : r ≤ 1
  · rw [if_pos h1] at hv; cases hv
  rw [if_neg h1] at hv
  by_cases h2 : r = 2
  · rw [if_pos h2, List.mem_singleton] at hv
    subst hv
    exact ⟨fun _ => decA_ne, by rw [modA]; omega, by rw [modA]; omega⟩
  rw [if_neg h2, List.mem_cons, List.mem_singleton] at hv
  rcases hv with rfl | rfl
  · exact ⟨fun _ => decA_ne, by rw [modA]; omega, by rw [modA]; omega⟩
  · exact ⟨fun _ => decB_ne, by rw [modB]; omega, by rw [modB]; omega⟩

theorem seed_sorted : [kvA, kvB].Pairwise etcdKvLess := by
  refine List.pairwise_pair.2 ?_
  show go.GoStringLt (go!"/registry" ++ (go!"/objs/" ++ kA)) (go!"/registry" ++ (go!"/objs/" ++ kB))
  exact of_decide_eq_true (inst := go.goStringLt_dec _ _) rfl

/-- **The seeded state is the store's.** -/
theorem seed_wf (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (hp : c.pfx = go!"/registry/objs") : kvWf c σs2 := by
  have hfind : ∀ k x, linkv.absM σs2.kvs k = some x → x = linkv.absVR kvA ∨ x = linkv.absVR kvB := by
    intro k x hx
    simp only [linkv.absM, mvcc.findKey, σs2_kvs] at hx
    by_cases e1 : kvA.key = k
    · simp [e1] at hx; exact Or.inl hx.symm
    by_cases e2 : kvB.key = k
    · simp [e1, e2] at hx; exact Or.inr hx.symm
    · simp [e1, e2] at hx
  refine ⟨by rw [σs2_kvs]; exact seed_sorted, ?_, ?_, by simp [linkv.absSt, σs2_kvs, σs2_rev]⟩
  · intro k x _ hx
    rw [hc]
    rcases hfind k x hx with rfl | rfl
    · show (driverCodec.dec (v0 kA)).isSome; rw [dec_v0A]; rfl
    · show (driverCodec.dec (v0 kB)).isSome; rw [dec_v0B]; rfl
  · intro k x hx
    rcases hfind k x hx with rfl | rfl <;> simp [linkv.absVR, kvA, kvB, linkv.absSt, σs2_kvs, σs2_rev]

end rel

/-! ## The seeding's ghost state -/

/-- No fraction added to `1` is valid. -/
theorem qp_one_add (q : Qp) (h : (1 : Qp) + q ≤ 1) : False := by
  have h1 : (1 : Rat) + q.val ≤ 1 := h
  have := q.2
  grind

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]
variable [go_etcd_io.etcd.client.v3.Assumptions]
variable [go_etcd_io.etcd.server.v3.etcdserver.api.v3rpc.Assumptions]

open Iris.ProofMode

/-- The seeding's namespace. -/
def seedN : Namespace := nroot .@ ("k8setcd3_seed" : String)

theorem seedN_mask : (↑seedN : CoPset) ⊆ (⊤ \ ↑srvRaftN) \ ↑kvN := by
  intro p hp
  rw [Iris.Std.LawfulSet.mem_diff, Iris.Std.LawfulSet.mem_diff]
  exact ⟨⟨CoPset.mem_full, fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩,
    fun h' => ndot_ne_disjoint nroot (by decide) p ⟨hp, h'⟩⟩

/-- **The seeding's invariant**: etcd's state, its value half-shared with `Main` (the seed puts'
updates carry `Main`'s half), until `Main` cancels it with its half (then the variable is whole
here, and no update can fire: `seed_au`). -/
def seedInv (γs : GName) (γk : KVNames) : IProp GF :=
  inv seedN iprop((∃ σ : KVState, etcdKV γk σ ∗ ghostVar γs (1 : Qp).half σ) ∨
    (∃ σ : KVState, ghostVar γs 1 σ))

instance seedInv_persistent (γs : GName) (γk : KVNames) : Persistent (seedInv (GF := GF) γs γk) := by
  unfold seedInv; infer_instance

theorem seedInv_alloc (γk : KVNames) (σ : KVState) (E : CoPset) :
    etcdKV (GF := GF) γk σ ⊢ |={E}=> ∃ γs, seedInv γs γk ∗ ghostVar γs (1 : Qp).half σ := by
  iintro Hσ
  imod ghostVar_alloc (GF := GF) σ with ⟨%γs, Hs⟩
  icases (ghostVar_split_half γs 1 σ).1 $$ Hs with ⟨Hs1, Hs2⟩
  imod inv_alloc seedN E (iprop((∃ σ : KVState, etcdKV γk σ ∗ ghostVar γs (1 : Qp).half σ) ∨
      (∃ σ : KVState, ghostVar γs 1 σ)) : IProp GF) $$ [Hσ Hs1] with #Hi
  · inext
    ileft
    iexists σ
    iframe
  imodintro
  iexists γs
  iframe Hs2
  iunfold seedInv
  iexact Hi

/-- **A seed put's update** (fired at most once): at its firing etcd's state is `Main`'s view
`σ`; it moves both halves to the put's next state. -/
theorem seed_au (γs : GName) (γk : KVNames) (op : KVOp) (σ : KVState) :
    seedInv γs γk ∗ ghostVar γs (1 : Qp).half σ ⊢
      kvOpAu1 (GF := GF) γk op
        (fun σ' => iprop(ghostVar γs (1 : Qp).half (kvOpStep op σ) ∗ ⌜σ' = σ⌝)) := by
  have Hm := seedN_mask
  iintro ⟨#Hinv, Hs⟩
  unfold kvOpAu1 kvAu1
  iauintro
  unfold atomic_acc
  iunfold seedInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%σ', Hσ, Hs'⟩ | ⟨%σ', Hfull⟩)
  · ihave %Heq := ghostVar_agree γs σ' (1 : Qp).half σ (1 : Qp).half $$ Hs' Hs
    subst Heq
    iapply fupd_mask_intro (show (∅ : CoPset) ⊆ ((⊤ \ ↑srvRaftN) \ ↑kvN) \ ↑seedN from
      Std.LawfulSet.empty_subset)
    iintro Hclose2
    isimp only [texist_cons, texist_nil, tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
    iexists σ'
    iframe Hσ
    isplit
    · iintro Hσ
      imod Hclose2 with -
      imod Hclose $$ [Hσ Hs'] with -
      · inext
        ileft
        iexists σ'
        iframe
      imodintro
      iexact Hs
    · iintro ⟨Hσ, -⟩
      imod Hclose2 with -
      imod ghostVar_update_halves (kvOpStep op σ') γs σ' σ' $$ Hs' Hs with ⟨Hs', Hs⟩
      imod Hclose $$ [Hσ Hs'] with -
      · inext
        ileft
        iexists _
        iframe
      imodintro
      iframe Hs
      ipureintro; rfl
  · ihave %Hbad := ghostVar_valid_2 γs σ' 1 σ (1 : Qp).half $$ Hfull Hs
    exact (qp_one_add _ Hbad.1).elim

/-- **The seed put's updates at every member** (the client's `[∧list]` over its members): each
member's from its `seedInv` and `Main`'s one half, which every conjunct shares. -/
theorem seed_aus (γs : GName) (ms : List (EtcdGrove.client.SrvAt GF)) (op : KVOp) (σ : KVState) :
    ([∗list] y ∈ ms, seedInv γs y.γr.kv) ∗ ghostVar γs (1 : Qp).half σ ⊢
      [∧list] y ∈ ms, kvOpAu1 (GF := GF) y.γr.kv op
        (fun σ' => iprop(ghostVar γs (1 : Qp).half (kvOpStep op σ) ∗ ⌜σ' = σ⌝)) := by
  refine BigAndL.bigAndL_intro (fun k y hk => ?_)
  iintro ⟨#Hsi, Hs⟩
  ihave #Hy := BigSepL.bigSepL_lookup hk $$ Hsi
  iapply seed_au γs y.γr.kv op σ
  iframe Hy Hs

/-- `seedInv` reads only the KV state's ghost name (`kvSame`'s first part): one invariant serves
every member of a cluster. -/
theorem seedInv_same (γs : GName) (γk γk' : KVNames) (hs : kvSame γk' γk) :
    seedInv (GF := GF) γs γk' = seedInv γs γk := by
  unfold seedInv etcdKV; rw [hs.1]

/-- One `seedInv` at the cluster's KV names is one at every member's (`seedInv_same`). -/
theorem seedInvs_of_same (γs : GName) (γk : KVNames) (ms : List (EtcdGrove.client.SrvAt GF))
    (h : ∀ x ∈ ms, kvSame x.γr.kv γk) :
    seedInv (GF := GF) γs γk ⊢ [∗list] y ∈ ms, seedInv γs y.γr.kv := by
  induction ms with
  | nil => iintro _; iapply BigSepL.bigSepL_nil.2; itrivial
  | cons y ys ih =>
    iintro #H
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · rw [seedInv_same γs _ _ (h y (by simp))]; iexact H
    · iapply (ih (fun x hx => h x (List.mem_cons_of_mem _ hx))); iexact H

/-- **The seeding's end**: `Main` hands its half in for etcd's state. -/
theorem seedInv_cancel (γs : GName) (γk : KVNames) (σ : KVState) :
    seedInv γs γk ∗ ghostVar γs (1 : Qp).half σ ⊢ |={⊤}=> etcdKV (GF := GF) γk σ := by
  iintro ⟨#Hinv, Hs⟩
  iunfold seedInv at Hinv
  iinv Hinv with >Hi Hclose
  icases Hi with (⟨%σ', Hσ, Hs'⟩ | ⟨%σ', Hfull⟩)
  · ihave %Heq := ghostVar_agree γs σ' (1 : Qp).half σ (1 : Qp).half $$ Hs' Hs
    subst Heq
    ihave Hfull := (ghostVar_split_half γs 1 σ').2 $$ [Hs' Hs]
    · iframe
    imod Hclose $$ [Hfull] with -
    · inext
      iright
      iexists σ'
      iexact Hfull
    imodintro
    iexact Hσ
  · ihave %Hbad := ghostVar_valid_2 γs σ' 1 σ (1 : Qp).half $$ Hfull Hs
    exact (qp_one_add _ Hbad.1).elim

/-- **The seeded revisions, one change at most each**: etcd's first revision (none) and the two
seeds' puts. -/
def seedRevs (γh : GName) : IProp GF :=
  iprop(□ ∀ r : Nat, ⌜1 ≤ r ∧ r ≤ 3⌝ → ∃ ch : Changes,
    ghostMapElem γh (W64 (r : Int)) DFrac.discard ch ∗ ⌜ch.length ≤ 1⌝)

instance seedRevs_persistent (γh : GName) : Persistent (seedRevs (GF := GF) γh) := by
  unfold seedRevs; infer_instance

/-- **The store's history at the seeded state**: etcd's first revision, with no changes, and the
two key-values. -/
theorem histAuth_seed :
    ⊢ |==> ∃ γh, histAuth (GF := GF) γh σs2 ∗ seedRevs γh := by
  imod ghost_map_alloc_empty (GF := GF) (K := w64) (V := Changes) with ⟨%γh, HA⟩
  imod ghost_map_insert_persist (W64 1) ([] : Changes) rfl $$ HA with ⟨HA, #H1⟩
  imod ghost_map_insert_persist kvA.modRev [(kvA.key, some kvA.value)] (by rfl) $$ HA
    with ⟨HA, #Ha⟩
  imod ghost_map_insert_persist kvB.modRev [(kvB.key, some kvB.value)] (by rfl) $$ HA
    with ⟨HA, #Hb⟩
  imodintro
  iexists γh
  isplitl
  · iunfold histAuth
    iexists _
    iframe HA
    isplitr
    · ipureintro
      intro r ch hv
      by_cases e2 : kvB.modRev = r
      · subst e2; rw [modB, σs2_rev]; omega
      rw [GMap.lookup_insert_ne _ _ e2] at hv
      by_cases e1 : kvA.modRev = r
      · subst e1; rw [modA, σs2_rev]; omega
      rw [GMap.lookup_insert_ne _ _ e1] at hv
      by_cases e0 : W64 1 = r
      · subst e0; rw [σs2_rev]; decide
      rw [GMap.lookup_insert_ne _ _ e0] at hv
      cases hv
    iunfold kvSeen
    imodintro
    iintro %v %hv
    rw [σs2_kvs] at hv
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hv
    rcases hv with rfl | rfl
    · iexists _
      iframe Ha
      ipureintro; simp
    · iexists _
      iframe Hb
      ipureintro; simp
  iunfold seedRevs
  imodintro
  iintro %r %hr
  have : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl
  · iexists _
    isplit
    · iexact H1
    · ipureintro; simp
  · iexists [(kvA.key, some kvA.value)]
    have e : W64 (((2 : Nat) : Int)) = kvA.modRev := rfl
    rw [e]
    isplit
    · iexact Ha
    · ipureintro; simp
  · iexists [(kvB.key, some kvB.value)]
    have e : W64 (((3 : Nat) : Int)) = kvB.modRev := rfl
    rw [e]
    isplit
    · iexact Hb
    · ipureintro; simp

/-- **The instance's invariant at the seeded state**, and the library's initial state. -/
theorem kInv_seed (γk : KVNames) (c : StoreCfg GF DObj) (hc : c.S = driverSpec)
    (hp : c.pfx = go!"/registry/objs") (E : CoPset) :
    etcdKV (GF := GF) γk σs2 ∗ histAuth c.γh σs2 ∗ seedRevs c.γh ⊢
      |={E}=> ∃ γ : KNames, kInv γ c g0s γk ∗ kState γ g0s (linkv.pInit (kSpec g0s)) := by
  iintro ⟨Hσ, Hhist, #Hsr⟩
  imod ghostVar_alloc (GF := GF) ([] : List OpV) with ⟨%γh, Hh⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Input) with ⟨%γp, Hp⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := KVState) with ⟨%γr, Hr⟩
  imod ghost_map_insert_persist σs2.rev σs2 rfl $$ Hr with ⟨Hr, #He⟩
  icases (ghostVar_split_half γh 1 ([] : List OpV)).1 $$ Hh with ⟨Hh1, Hh2⟩
  imod inv_alloc drvInvN E (kInvBody (GF := GF) ⟨γh, γp, γr⟩ c g0s γk) $$ [Hh1 Hσ Hp Hr Hhist]
    with #Hinv
  · inext
    iunfold kInvBody
    iexists [], linkv.pInit (kSpec g0s), σs2, ∅, 0
    iframe
    isplitl [Hr]
    · iunfold revOwn
      iexists _
      iframe He Hr
      ipureintro
      refine ⟨GMap.lookup_insert _ _ _, fun n hn => by
        rw [GMap.lookup_insert_ne _ _ (by omega)]; rfl, fun n s hs => ?_⟩
      by_cases e : σs2.rev = n
      · subst e; rw [GMap.lookup_insert] at hs; cases hs; exact kvExt_refl _
      · rw [GMap.lookup_insert_ne _ _ e] at hs; cases hs
    isplitl [Hhist]
    · iunfold shistOwn
      iframe Hhist
      iunfold oneKeyRevs
      iunfold seedRevs at Hsr
      imodintro
      iintro %r %hr
      icases Hsr $$ %r %(by rw [σs2_rev] at hr; exact hr) with ⟨%ch, #Hch, %hl⟩
      iexists ch
      isplit
      · iexact Hch
      · ipureintro
        exact Nat.le_trans (List.length_filter_le _ _) (by simpa using hl)
    ipureintro
    exact ⟨rfl, kOk_init σs2 (seed_wf c hc hp) (seed_wfHist c hc) seed_keys seed_krel g0s_len⟩
  imodintro
  iexists ⟨γh, γp, γr⟩
  iunfold kInv
  iframe Hinv
  iunfold kState
  iexists []
  iframe
  ipureintro; rfl

end ghost

end k8s_etcd3
end EtcdGrove
end Perennial
