/-
Lean-first (no Rocq counterpart).

# The shared model's Go values (k8s-dist K9, `notes/k8s-dist-k9.md` §2)

The vocabulary of the specs of `SharedModel`'s search (`examples/k8s/etcd3/export.go`):

- `HWf h`: a configuration the search holds, its history one store per revision, the last its store
  (§2.0);
- `gapsL s len j`: the `j` foreign stores `skipTo` appends to a history of length `len` whose last
  store is `s` (`foreignL`'s, read off the Go: the items unchanged, the revision `histLen + 1`);
- `hhInv hh`: what `hh.mu` protects (§2.3): the maps `canon` and `is` (both `nil`, or both made), each
  node in `canon[k]` a node of `k`'s `prev` and `n` holding some store (`canonNode`), `is` anything
  (nothing relies on it: `canonLocked` walks the caller's own history), and `gaps[base]` the nodes of
  `base`'s history with `i + 1` foreign stores appended (`gapsOwn`). Hash-consing is for speed: no
  spec relies on two equal histories being one node, only on one node holding one history;
- `hhOwn hh`: `hh`'s mutex, with `hhInv hh` (persistent);
- `cfgSetOwn s hh gs`: a `cfgSet` at `s` over `hh`, its list holding the configurations `gs`, its
  buckets' indices into the list.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.MDefs
public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.dist.SharedSearch
public import Perennial.Proof.sync.Base

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s_etcd3

open Iris Iris.BI
open github_com.mit_pdos.etcd_grove.examples.k8s.etcd3
  (mstore mcfg hnode item Input Output state histHashes cfgSet ikey ckey)

/-! ## Well-formed configurations and the foreign stores -/

section pure
variable [GooseExts]

/-- **A configuration the search holds** (§2.0): one store per revision, the last the store. -/
def HWf (h : HSt) : Prop := h.hist.length = uint.nat h.st.rv ∧ h.hist.getLast? = some h.st

/-- The `j` foreign stores `skipTo` appends to a history of length `len` whose last store is `s`. -/
def gapsL (s : GSt) (len j : Nat) : List GSt :=
  (List.range j).map fun m => ⟨s.items, W64 ((len + m + 1 : Nat) : Int)⟩

instance ikey_decEq : DecidableEq ikey := fun a b => Classical.propDecidable (a = b)

instance ckey_decEq : DecidableEq ckey := fun a b => Classical.propDecidable (a = b)

end pure

/-! ## The map keys' values are injective (as `client_go/util/consistency`'s) -/

section inj
variable [GooseExts] [GoGlobalContext] [GoLocalContext] [GoSemanticsFunctions]
variable [go.BasicIntoValInj] [ikey.TypeAssumptions] [ckey.TypeAssumptions]

/-- Two values with a field's deterministic projection have equal projections (`proj_eq`). -/
theorem fld_eq {t : Tag} {f : GoInstruction} {a b : val} {ea eb : Expr}
    (ha : go.IsGoStepPureDetTagged t f a ea) (hb : go.IsGoStepPureDetTagged t f b eb)
    (h : a = b) : ea = eb := by
  have h1 := ha.isGoStep_det_internal.isGoStep_pure_det
  have h2 := hb.isGoStep_det_internal.isGoStep_pure_det
  subst h
  rw [h2] at h1
  exact cast (congrFun h1 eb) rfl

theorem ikey_intoVal_inj : Function.Injective (intoVal (V := ikey)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (fld_eq
    (ikey.TypeAssumptions.get_prev x) (ikey.TypeAssumptions.get_prev y) h))
  have := go.intoVal_inj (Expr.Val.inj (fld_eq
    (ikey.TypeAssumptions.get_n x) (ikey.TypeAssumptions.get_n y) h))
  have := go.intoVal_inj (Expr.Val.inj (fld_eq
    (ikey.TypeAssumptions.get_h x) (ikey.TypeAssumptions.get_h y) h))
  cases x; cases y; simp_all

theorem ckey_intoVal_inj : Function.Injective (intoVal (V := ckey)) := by
  intro x y h
  have h : (#x : val) = #y := h
  have := go.intoVal_inj (Expr.Val.inj (fld_eq
    (ckey.TypeAssumptions.get_hist x) (ckey.TypeAssumptions.get_hist y) h))
  have := go.intoVal_inj (Expr.Val.inj (fld_eq
    (ckey.TypeAssumptions.get_rv x) (ckey.TypeAssumptions.get_rv y) h))
  have := go.intoVal_inj (Expr.Val.inj (fld_eq
    (ckey.TypeAssumptions.get_np x) (ckey.TypeAssumptions.get_np y) h))
  have := go.intoVal_inj (Expr.Val.inj (fld_eq
    (ckey.TypeAssumptions.get_h x) (ckey.TypeAssumptions.get_h y) h))
  cases x; cases y; simp_all

instance ikey_intoValInj : go.IntoValInj ikey := ⟨ikey_intoVal_inj⟩
instance ckey_intoValInj : go.IntoValInj ckey := ⟨ckey_intoVal_inj⟩

end inj

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Assumptions]

/-- A node of `canon[k]`: `k`'s `prev` and `n`, holding some store (read-only). -/
def canonNode (k : ikey) (c : Loc) : IProp GF :=
  iprop(∃ hn : hnode, c ↦□ hn ∗ ⌜hn.prev' = k.prev' ∧ hn.n' = k.n'⌝ ∗ ∃ s : GSt, storeOwn hn.st' s)

instance canonNode_persistent (k : ikey) (c : Loc) : Persistent (canonNode (GF := GF) k c) := by
  unfold canonNode; infer_instance

/-- `gaps[base]`: the nodes of `base`'s history (`hs`, its last `s`) with `i + 1` foreign stores
appended, `i` the node's index (see the file header). -/
def gapsOwn (base : Loc) (sl : GoSlice) : IProp GF :=
  iprop(∃ (ns : List Loc) (hs : List GSt) (s : GSt),
    sl ↦* ns ∗ ownSliceCap Loc sl (DFrac.own 1) ∗ histOwn base hs ∗
    ⌜hs.getLast? = some s ∧ hs.length + ns.length < 2 ^ 63⌝ ∗
    [∗list] i ↦ n ∈ ns, histOwn n (hs ++ gapsL s hs.length (i + 1)))

theorem nil_or_snoc {α : Type} (l : List α) : l = [] ∨ ∃ l' x, l = l' ++ [x] := by
  cases h : l.reverse with
  | nil => exact .inl (List.reverse_eq_nil_iff.mp h)
  | cons x r => exact .inr ⟨r.reverse, x, by rw [← List.reverse_reverse l, h]; simp⟩

/-- **One node holds one history**: a history's nodes record their lengths (below `2^64`), so two
histories of one node have one length (`histOwn_agree`). -/
theorem histOwn_agree_len (h : Loc) (a b : List GSt) (ha : a.length < 2 ^ 64)
    (hb : b.length < 2 ^ 64) : histOwn (GF := GF) h a ⊢ histOwn h b -∗ ⌜a = b⌝ := by
  iintro #Ha #Hb
  icases histOwn_agree _ _ _ $$ Ha Hb with %H
  rcases nil_or_snoc a with rfl | ⟨a', x, rfl⟩ <;> rcases nil_or_snoc b with rfl | ⟨b', y, rfl⟩
  · ipureintro; rfl
  · icases (histOwn_nil (GF := GF) h).mp $$ Ha with %Hn
    icases (histOwn_snoc (GF := GF) h b' y).mp $$ Hb with ⟨%hn, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
    exact absurd Hn Hnn
  · icases (histOwn_nil (GF := GF) h).mp $$ Hb with %Hn
    icases (histOwn_snoc (GF := GF) h a' x).mp $$ Ha with ⟨%hn, Hp, -⟩
    ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
    exact absurd Hn Hnn
  · icases (histOwn_snoc (GF := GF) h a' x).mp $$ Ha with ⟨%hn, #Hp, -, %Hna, -⟩
    icases (histOwn_snoc (GF := GF) h b' y).mp $$ Hb with ⟨%hn', #Hp', -, %Hnb, -⟩
    icases typedPointsto_agree_wand _ _ _ _ _ $$ Hp Hp' with %He
    subst He
    ipureintro
    apply H
    simp only [List.length_append, List.length_singleton] at ha hb ⊢
    rw [Hna] at Hnb
    have := congrArg (fun w : w64 => w.toNat) Hnb
    simp only [W64] at this
    simp only [BitVec.toNat_ofInt] at this
    omega

/-- **What `hh.mu` protects** (see the file header). -/
def hhInv (hh : Loc) : IProp GF :=
  iprop(∃ (mc mi mg : GoMap) (C : GMap ikey GoSlice) (I : GMap Loc Bool) (G : GMap Loc GoSlice),
    structFieldRef histHashes go!"canon" hh ↦ mc ∗ structFieldRef histHashes go!"is" hh ↦ mi ∗
    structFieldRef histHashes go!"gaps" hh ↦ mg ∗
    (⌜mc = map.nil ∧ mi = map.nil⌝ ∨
      mc ↦$ C ∗ mi ↦$ I ∗
      [∗map] k ↦ sl ∈ C, ∃ ns : List Loc, sl ↦* ns ∗ ownSliceCap Loc sl (DFrac.own 1) ∗
        [∗list] n ∈ ns, canonNode k n) ∗
    (⌜mg = map.nil⌝ ∨ mg ↦$ G ∗ [∗map] b ↦ sl ∈ G, gapsOwn b sl))

/-- **`hh`'s mutex**, protecting `hhInv hh` (persistent). -/
def hhOwn (hh : Loc) : IProp GF :=
  iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ sync.isMutex (structFieldRef histHashes go!"mu" hh) (hhInv hh))

instance hhOwn_persistent (hh : Loc) : Persistent (hhOwn (GF := GF) hh) := by
  unfold hhOwn; infer_instance

/-- **A `cfgSet` at `s` over `hh`** holding the configurations `gs` (in its list's order), its
buckets' indices into the list. -/
def cfgSetOwn (s hh : Loc) (gs : List GCfg) : IProp GF :=
  iprop(∃ (lsl : GoSlice) (mb : GoMap) (cs : List mcfg) (B : GMap ckey GoSlice),
    structFieldRef cfgSet go!"hh" s ↦ hh ∗ structFieldRef cfgSet go!"list" s ↦ lsl ∗
    structFieldRef cfgSet go!"buckets" s ↦ mb ∗
    lsl ↦* cs ∗ ownSliceCap mcfg lsl (DFrac.own 1) ∗ ([∗list] c;g ∈ cs;gs, cfgOwn c g) ∗
    ⌜cs.length < 2 ^ 63⌝ ∗
    (⌜mb = map.nil ∧ cs = []⌝ ∨ mb ↦$ B ∗ [∗map] _k ↦ sl ∈ B, ∃ is : List w64,
      sl ↦* is ∗ ownSliceCap w64 sl (DFrac.own 1) ∗ ⌜∀ i ∈ is, 0 ≤ sint.Z i ∧ sint.nat i < cs.length⌝))

end defs

end k8s_etcd3
end EtcdGrove
end Perennial
