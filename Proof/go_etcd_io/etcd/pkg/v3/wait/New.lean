/-
Proof of `Spec/go_etcd_io/etcd/pkg/v3/wait/New.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.pkg.v3.wait.New
public import Spec.go_etcd_io.etcd.pkg.v3.wait.list__Register
public import Spec.go_etcd_io.etcd.pkg.v3.wait.list__Trigger
public import Spec.go_etcd_io.etcd.pkg.v3.wait.list__IsRegistered

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.pkg.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.pkg.v3.wait.Assumptions]


/-- A slice's elements, one points-to each. -/
theorem wait_slice_elems {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V] (sl : GoSlice)
    (vs : List V) :
    (sl ↦* vs : IProp GF) ⊢
      [∗list] j ↦ v ∈ vs, typedPointsto (sliceIndexRef V (j : Int) sl) v (DFrac.own 1) := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨Hsl, -⟩)
  · rw [H.2]; iapply BigSepL.bigSepL_nil.2; iempintro
  · icases typedPointsto_split _ _ _ $$ Hsl with Hsl
    simp only [TypedPointsto.typedPointstoDef]
    icases Hsl with ⟨-, Hsl⟩
    unfold arrayElems
    simp only [sliceIndexRef]
    iexact Hsl

/-- A shard during `New`'s loop: its lock (zero) and map field, until made (`some`): then the
shard and its reader slot. -/
def waitNewShard (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF) (ea : Loc)
    (o : Option Loc) : IProp GF :=
  match o with
  | none => iprop(waitShardLock ea ↦ (zero_val sync.RWMutex) ∗ ∃ v : Loc, waitShardMap ea ↦ v)
  | some _ => iprop(waitShard γw R ea ∗ waitShardReader ea)

theorem wait_elem_new (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF) (ea : Loc) :
    typedPointsto (GF := GF) ea (zero_val wait.listElement) (DFrac.own 1) ⊢
      waitNewShard γw R ea none := by
  iintro Hx
  iStructNamed Hx
  simp only [waitNewShard]
  iframe l
  iexists _
  iframe m

/-- A bigSepL that ignores the list's elements depends only on its length. -/
theorem wait_bigSepL_len {A B : Type} (Ψ : Nat → IProp GF) (l1 : List A) (l2 : List B)
    (h : l1.length = l2.length) :
    ([∗list] k ↦ _x ∈ l1, Ψ k) ⊢ [∗list] k ↦ _x ∈ l2, Ψ k := by
  induction l1 generalizing l2 Ψ with
  | nil =>
    cases l2 with
    | nil => exact .rfl
    | cons _ _ => simp at h
  | cons a l1 ih =>
    cases l2 with
    | nil => simp at h
    | cons b l2 =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      refine (BigSepL.bigSepL_cons).1.trans ?_
      refine .trans ?_ (BigSepL.bigSepL_cons).2
      exact sep_mono .rfl (ih (fun k => Ψ (k + 1)) l2 h)

/-- A shard made: its invariant, its lock initialized (a writer guard and one reader slot). -/
theorem wait_shard_init (γw : GName) (R : w64 → (GoInterface → IProp GF) → IProp GF) (ea v : Loc) :
    ⊢ waitShardLock ea ↦ (zero_val sync.RWMutex) -∗ waitShardMap ea ↦ v -∗
      ownMap v (DFrac.own 1) (∅ : GMap w64 Loc) ={⊤}=∗ waitShard γw R ea ∗ waitShardReader ea := by
  iintro Hl Hm Hmap
  imod ghost_map_alloc_empty (K := w64) (V := Loc) with ⟨%γs, Hg⟩
  icases (waitAuth_halves γs ∅).1 $$ Hg with ⟨Hg1, Hg2⟩
  imod inv_alloc waitShardN ⊤ (waitShardInv γw R γs) $$ [Hg2] with #Hinv
  · inext; unfold waitShardInv; iexists ∅; iframe Hg2
    iapply BigSepM.bigSepM_empty.2; iempintro
  imod sync.init_RWMutex (waitShardP v γs) (E := ⊤) (waitShardLock ea) $$ [Hmap Hg1] Hl with Hrs
  · inext; unfold waitShardP; iexists ∅
    simp only [Qp.half]
    iframe
  have hmax : sync.rwmutex.actualMaxReaders.toNat = (sync.rwmutex.actualMaxReaders.toNat - 1) + 1 := by
    rw [sync.rwmutex.actualMaxReaders_unseal]; decide
  rw [hmax, List.replicate_succ]
  icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hrs with ⟨Hrw, -⟩
  icases sync.ownRWMutex_guard _ _ $$ Hrw with ⟨Hrw, #Hgd⟩
  ipersist Hm
  imodintro
  isplitl []
  · unfold waitShard; iexists v, γs; iframe #
  · unfold waitShardReader; iexists v, γs; iframe Hrw; iframe #

theorem wait.New.wp_proof
    (hR : wait.list.Register.spec (GF := GF) (hG := hG))
    (hT : wait.list.Trigger.spec (GF := GF) (hG := hG))
    (hI : wait.list.IsRegistered.spec (GF := GF) (hG := hG)) :
    wait.New.spec (GF := GF) (hG := hG) := by
  intro γi R
  wp_start
  ihave #Hsync : isPkgInit (PROP := IProp GF) pkg_id.sync $$ []
  · iPkgInit
  wp_apply wp_slice_make2 (V := wait.listElement) (W64 64) as %sl ⟨Hsl, Hcap⟩
  · ipureintro; decide
  ihave %Hsllen := ownSlice_len _ _ _ $$ Hsl
  have Hlen : sint.Z sl.len = 64 := by
    have h1 := Hsllen.1; rw [List.length_replicate] at h1; word
  ihave Hel := wait_slice_elems sl _ $$ Hsl
  imod (ghost_map_alloc_empty (GF := GF) (K := w64) (V := GName)) with ⟨%γw, Hgw⟩
  imod inv_alloc waitRegN ⊤ (waitRegInv γi γw) $$ [Hgw] with #Hreg
  · inext; unfold waitRegInv; iexists ∅; iframe Hgw
    iapply BigSepM.bigSepM_empty.2; iempintro
  ihave Hel := (BigSepL.bigSepL_mono (PROP := IProp GF)
    (Φ := fun j v => typedPointsto (GF := GF) (sliceIndexRef wait.listElement (j : Int) sl) v
      (DFrac.own 1))
    (Ψ := fun j _ => waitNewShard (GF := GF) γw R (waitShardAddr sl j) none)
    (fun {k x} hx => by
      have : x = zero_val wait.listElement := by
        rw [List.getElem?_replicate] at hx; split at hx <;> simp_all
      subst this; exact wait_elem_new γw R _)) $$ Hel
  ihave Hel := (wait_bigSepL_len (fun j => waitNewShard (GF := GF) γw R (waitShardAddr sl j) none) _
    (List.replicate 64 (none : Option Loc)) (by simp)) $$ Hel
  ihave Hel := (BigSepL.bigSepL_mono (PROP := IProp GF)
    (Ψ := fun j o => waitNewShard (GF := GF) γw R (waitShardAddr sl j) o)
    (fun {k x} hx => by
      have : x = none := by
        rw [List.getElem?_replicate] at hx; split at hx <;> simp_all
      subst this; exact .rfl)) $$ Hel
  ipersist res
  iStructNamed res
  ihave IH : iprop(∃ (k : w64) (sts : List (Option Loc)),
      "i" ∷ i_ptr ↦ k ∗
      "Hel" ∷ ([∗list] j ↦ o ∈ sts, waitNewShard γw R (waitShardAddr sl j) o) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ 64 ∧ sts.length = 64 ∧
        (∀ j, j < sint.nat k → ∃ m, sts[j]? = some (some m)) ∧
        ∀ j m, sint.nat k ≤ j → sts[j]? ≠ some (some m)⌝) $$ [i Hel]
  · iexists W64 0, List.replicate 64 none
    simp only [named]
    iframe
    ipureintro
    refine ⟨by decide, by decide, by simp, fun j hj => ?_, fun j m _ => ?_⟩
    · exfalso; simp at hj; omega
    · rw [List.getElem?_replicate]; split <;> simp
  wp_for IH
  wp_if_destruct
  · have hlt : sint.Z k < 64 := by
      omega
    obtain ⟨Hk0, Hk64, Hsts, Hinit, Hfresh⟩ := Hk
    obtain ⟨o, ho⟩ : ∃ o, sts[sint.nat k]? = some o :=
      ⟨_, List.getElem?_eq_getElem (by rw [Hsts]; word)⟩
    wp_apply wp_map_make1 (V := Loc) as %mref Hmref
    have Hbnd : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := ⟨Hk0, by omega⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    have hkk : sint.Z k = ((sint.nat k : Nat) : Int) := by word
    rw [hkk]
    icases (BigSepL.bigSepL_lookup_acc (PROP := IProp GF)
      (Φ := fun j o => waitNewShard (GF := GF) γw R (waitShardAddr sl j) o) ho).1 $$ Hel with ⟨Ho, Hel⟩
    cases o with
    | some m =>
      exact absurd ho (Hfresh _ m (Nat.le_refl _))
    | none =>
    unfold waitNewShard
    icases Ho with ⟨Hl, %v, Hm⟩
    wp_auto
    iapply wp_for_post_do
    imod wait_shard_init γw R _ mref $$ Hl Hm Hmref with Hsh
    ihave Hel := Hel $$ %(some mref) [Hsh]
    · iexact Hsh
    wp_auto
    iframe
    iexists k + W64 1, sts.set (sint.nat k) (some mref)
    simp only [named]
    iframe
    ipureintro
    refine ⟨by word, by word, by simp [Hsts], fun j hj => ?_, fun j m hj => ?_⟩
    · by_cases hjk : j = sint.nat k
      · subst hjk; exact ⟨mref, by simp [List.getElem?_set, Hsts]; word⟩
      · obtain ⟨m, hm⟩ := Hinit j (by word)
        exact ⟨m, by rw [List.getElem?_set_ne (Ne.symm hjk)]; exact hm⟩
    · have hjk : sint.nat k ≠ j := by word
      rw [List.getElem?_set_ne hjk]
      exact Hfresh j m (by word)
  · obtain ⟨Hk0, Hk64, Hsts, Hinit, -⟩ := Hk
    have hk64 : sint.nat k = 64 := by word
    rw [hk64] at Hinit
    ihave Hel := (BigSepL.bigSepL_mono (PROP := IProp GF)
      (Φ := fun j o => waitNewShard (GF := GF) γw R (waitShardAddr sl j) o)
      (Ψ := fun j _ => iprop(waitShard (GF := GF) γw R (waitShardAddr sl j) ∗
        waitShardReader (waitShardAddr sl j)))
      (fun {j x} hx => by
        have hj : j < 64 := by
          rw [← Hsts]; exact (List.getElem?_eq_some_iff.mp hx).1
        obtain ⟨m, hm⟩ := Hinit j hj
        rw [hm] at hx; cases hx
        exact .rfl)) $$ Hel
    icases (BigSepL.bigSepL_sep_eqv (PROP := IProp GF)).1 $$ Hel with ⟨#Hsh, Hrd⟩
    iapply HΦ
    iexists γw, waitListReader res_ptr
    ihave #Hlist : iprop(waitList (GF := GF) res_ptr γi γw R) $$ []
    · iunfold waitList
      iexists sl
      iframe e Hreg
      isplitr
      · ipureintro; exact Hlen
      imodintro
      iintro %i %hi
      obtain ⟨o, ho⟩ : ∃ o, sts[i]? = some o := ⟨_, List.getElem?_eq_getElem (by rw [Hsts]; exact hi)⟩
      iapply (BigSepL.bigSepL_lookup (PROP := IProp GF)
        (Φ := fun j (_ : Option Loc) => waitShard (GF := GF) γw R (waitShardAddr sl j)) ho) $$ Hsh
    isplitl []
    · iunfold isWait
      iexists interface.mk wait.list'.ty.PointerType #res_ptr
      isplitr
      · ipureintro; rfl
      isplitr
      · imodintro
        iintro %id %Ψ %Φ'
        imodintro
        iintro ⟨Hs, #HRi⟩ HΦ'
        iapply (hR res_ptr γi γw R id Ψ) $$ [Hs] HΦ'
        iframe Hs Hpkg Hlist HRi
      isplitr
      · imodintro
        iintro %id %x %Φ'
        imodintro
        iintro Hp HΦ'
        iapply (hT res_ptr γi γw R id x) $$ [Hp] HΦ'
        iframe Hp Hpkg Hlist
      · imodintro
        iintro %id %Φ'
        imodintro
        iintro Hrd HΦ'
        iapply (hI res_ptr id) $$ [Hrd] HΦ'
        iframe Hrd Hpkg
    · iunfold waitListReader
      iexists sl
      iframe e
      isplitr
      · ipureintro; exact Hlen
      iapply (wait_bigSepL_len (fun j => waitShardReader (GF := GF) (waitShardAddr sl j)) sts
        (List.replicate 64 ()) (by simp [Hsts])) $$ Hrd

end proof

end EtcdGrove
end Perennial
