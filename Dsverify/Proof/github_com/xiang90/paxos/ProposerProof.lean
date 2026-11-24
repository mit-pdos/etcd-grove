/-
Ported from dsverify-lab examples/paxos/proof/Paxos/Proof/ProposerProof.lean (lab master 7a84fb35; notes/dsv-paxos.md).

The proposer's proofs (`proposer.go`, `message.go`'s methods through the `promise` interface):
`newProposer.wp_proof` and `proposer.run.wp_proof`, with internal specs of `n`, `majority`,
`majorityReached`, `prepare`, `receivePromise` and `propose`.
-/
module

public import Dsverify.Proof.github_com.xiang90.paxos.Agents

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

namespace github_com.xiang90.paxos

attribute [local instance] GooseGlobalGS.gooseInvGS

section inj
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions] [field_sem : net.FieldAssumptions]

include hG sem package_sem in
/-- Two messages with the same Go value are equal (each field is read back by a deterministic
pure step, `message.TypeAssumptions`' `get_*`). -/
theorem message_intoVal_inj : Function.Injective (intoVal (V := message)) := by
  intro a b h
  have fld : ∀ {V : Type} [go.IntoValInj V] (f : message → V) (fn : GoString)
      (hget : ∀ x : message, go.IsGoStepPureDetTagged under
        (StructFieldGet message.underlying fn) #x (Val #(f x))), f a = f b := by
    intro V _ f fn hget
    have e1 := (hget a).isGoStep_det_internal.isGoStep_pure_det
    have e2 := (hget b).isGoStep_det_internal.isGoStep_pure_det
    rw [show (#a : val) = #b from h, e2] at e1
    have e3 : Val #(f b) = Val #(f a) := (congrFun e1 (Val #(f a))).mpr rfl
    injection e3 with e4
    exact (go.intoVal_inj e4).symm
  have h1 := fld message.from' _ (fun x => package_sem.instance'message.get'from x)
  have h2 := fld message.to' _ (fun x => package_sem.instance'message.get'to x)
  have h3 := fld message.typ' _ (fun x => package_sem.instance'message.get'typ x)
  have h4 := fld message.n' _ (fun x => package_sem.instance'message.get'n x)
  have h5 := fld message.prevn' _ (fun x => package_sem.instance'message.get'prevn x)
  have h6 := fld message.value' _ (fun x => package_sem.instance'message.get'value x)
  cases a; cases b
  simp_all

end inj

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [π : NetProtoGS]
variable [package_sem : paxos.Assumptions] [field_sem : net.FieldAssumptions]

set_option goose.wp.extras true

local notation "pkg" => pkg_id.github_com.xiang90.paxos

/-- The empty promise (`message{}` as a `promise`). -/
abbrev zeroP : GoInterface := interface.mkOk message.ty #(zero_val message)

/-- The map after inserting the empty promise at each of `ks`. -/
def initMap (ks : List w64) : GMap w64 GoInterface :=
  ks.foldl (fun m k => <[k := zeroP]> m) ∅

theorem initMap_take_succ (ks : List w64) (n : Nat) (k : w64) (h : ks[n]? = some k) :
    initMap (ks.take (n + 1)) = <[k := zeroP]> (initMap (ks.take n)) := by
  unfold initMap
  rw [List.take_add_one, List.foldl_append, h]
  rfl

theorem initMap_accIds : initMap accIds =
    (({[W64 1 := zeroP]} ∪ {[W64 2 := zeroP]} ∪ {[W64 3 := zeroP]}) : GMap w64 GoInterface) := by
  apply GMap.map_eq
  intro k
  simp [initMap, accIds, GMap.lookup_union]
  by_cases h1 : (3#64 : w64) = k <;> by_cases h2 : (2#64 : w64) = k <;>
    by_cases h3 : (1#64 : w64) = k <;> simp [h1, h2, h3]

theorem newProposer.wp_proof : newProposer.spec (GF := GF) (hG := hG) :=
  fun Γ id v nt nd amap ids asl hid hv => by
  wp_start as ⟨Henv, #Hasl⟩
  wp_auto
  wp_apply (wp_map_make1 (K := w64) (V := GoInterface)) as %am Ham
  ihave %Hlen := ownSlice_len _ _ _ $$ Hasl
  ihave HI : (∃ i : w64, "i" ∷ i_ptr ↦ i ∗ "a" ∷ (∃ x : w64, a_ptr ↦ x) ∗
      "Ham" ∷ am ↦$ initMap (accIds.take (sint.nat i)) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z asl.len⌝ : IProp GF) $$ [i a Ham]
  · iexists W64 0
    iframe
    isplitl [a]
    · iexists _; iexact a
    ipureintro; simp [accIds] at Hlen; word
  wp_for HI
  wp_if_destruct
  · simp only [Hi.1, Hif, and_self, ↓reduceIte]
    list_elem accIds (sint.nat i) as x
    icases a with ⟨%x0, a⟩
    wp_apply wp_load_slice_index asl (sint.Z i) accIds DFrac.discard x Hi.1 $$ [Hasl] with -
    · isplitr
      · iexact Hasl
      · ipureintro; exact Hx_lookup
    wp_apply wp_mapInsert $$ Ham as Ham
    wp_for_post
    iframe
    iexists i + W64 1
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, initMap_take_succ accIds _ x Hx_lookup]
    iframe
    isplitl [a]
    · iexists _; iexact a
    ipureintro; word
  · have hi3 : sint.nat i = accIds.length := by simp [accIds] at Hlen ⊢; word
    rw [hi3, List.take_length, initMap_accIds]
    iapply HΦ
    unfold own_proposer
    iexists nt, nd, amap, ids, am
    iStructNamed «$r0»
    iframe
    ipureintro; exact ⟨hid, hv⟩

/-! ## The proposer's state -/

/-- The proposer's mutable state: `lastSeq`, `value`, `valueN` and the `acceptors` map. -/
structure PState where
  ls : w64
  w : GoString
  vN : w64
  M : GMap w64 GoInterface

/-- `p.n()`: `lastSeq<<16 | id`. -/
def nOf (ls id : w64) : w64 := ls <<< W64 16 ||| id

theorem lowId_nOf_lt (ls id : w64) (hid : id.toNat < 2 ^ 16) : lowId (nOf ls id) = id := by
  unfold lowId nOf
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.shiftLeft_eq', show (W64 0xffff : w64) = BitVec.ofNat 64 (2 ^ 16 - 1) by decide]
  simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_ofNat, Nat.testBit_two_pow_sub_one]
  have h16 : (W64 16).toNat = 16 := by decide
  rw [h16]
  by_cases h : i < 16
  · simp [h, hi]
  · have hid' : id.getLsbD i = false := by
      rw [BitVec.getLsbD]
      exact Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le hid (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [h, hid']

theorem lowId_nOf (ls id : w64) (hid : id ∈ propIds) : lowId (nOf ls id) = id := by
  apply lowId_nOf_lt
  simp only [propIds, List.mem_cons, List.not_mem_nil, or_false] at hid
  rcases hid with rfl | rfl | rfl | rfl <;> decide

theorem nOf_ne_zero (ls id : w64) (hid : id ∈ propIds) : nOf ls id ≠ W64 0 := by
  intro h
  have h' := lowId_nOf ls id hid
  rw [h] at h'
  simp only [propIds, List.mem_cons, List.not_mem_nil, or_false] at hid
  unfold lowId at h'
  rcases hid with rfl | rfl | rfl | rfl <;> revert h' <;> decide

/-- The proposer's fields and its map, at state `σ`. -/
def pFields (pp : Loc) (id : w64) (nt am : Loc) (σ : PState) : IProp GF :=
  iprop("id" ∷ pp.[proposer, go!"id"] ↦ id ∗ "lastSeq" ∷ pp.[proposer, go!"lastSeq"] ↦ σ.ls ∗
    "value" ∷ pp.[proposer, go!"value"] ↦ σ.w ∗ "valueN" ∷ pp.[proposer, go!"valueN"] ↦ σ.vN ∗
    "acceptors" ∷ pp.[proposer, go!"acceptors"] ↦ am ∗
    "nt" ∷ pp.[proposer, go!"nt"] ↦ ntIface nt ∗ "Ham" ∷ am ↦$ σ.M)

/-- Acceptor `a`'s entry `x` of the map (persistent): a message, empty or a promise from `a`. -/
def entryOK (Γ : Names) (a : w64) (x : GoInterface) : IProp GF :=
  iprop(∃ m : message, ⌜x = interface.mkOk message.ty #m⌝ ∗
    (⌜m.n' = W64 0⌝ ∨ pfW Γ a m.n' m.prevn' m.value'))

instance entryOK_persistent (Γ : Names) (a : w64) (x : GoInterface) :
    Persistent (entryOK (GF := GF) Γ a x) := by
  unfold entryOK; infer_instance

/-- The value's provenance: the input `v` of client `c` (`vN = 0`) or an issued proposal. -/
def valOK (Γ : Names) (c vN : w64) (v w : GoString) : IProp GF :=
  if vN = W64 0 then iprop(regW Γ c w ∗ ⌜w = v⌝) else propW Γ vN w

instance valOK_persistent (Γ : Names) (c vN : w64) (v w : GoString) :
    Persistent (valOK (GF := GF) Γ c vN v w) := by
  unfold valOK; split <;> infer_instance

/-- The map's keys are the acceptors. -/
def domOK (M : GMap w64 GoInterface) : Prop := ∀ a, (M !! a).isSome ↔ a ∈ accIds

/-- Every entry is a message, whose reported number is at most `vN`. -/
def entsOK (M : GMap w64 GoInterface) (vN : w64) : Prop :=
  ∀ a x, M !! a = some x →
    ∃ m : message, x = interface.mkOk message.ty #m ∧ sint.Z m.prevn' ≤ sint.Z vN

/-- The proposer's invariant on its state (persistent). -/
def pInv (Γ : Names) (c : w64) (v : GoString) (σ : PState) : IProp GF :=
  iprop("%Hdom" ∷ ⌜domOK σ.M⌝ ∗ "%Hent" ∷ ⌜entsOK σ.M σ.vN⌝ ∗
    "#Hents" ∷ ([∗map] a ↦ x ∈ σ.M, entryOK Γ a x) ∗
    "%HvN" ∷ ⌜0 ≤ sint.Z σ.vN ∧ (σ.w.length : Int) < 2 ^ 48⌝ ∗
    "#Hval" ∷ valOK Γ c σ.vN v σ.w)

instance pInv_persistent (Γ : Names) (c : w64) (v : GoString) (σ : PState) :
    Persistent (pInv (GF := GF) Γ c v σ) := by
  unfold pInv; infer_instance

/-- Acceptor `a`'s entry is a promise of `n`. -/
def goodAt (M : GMap w64 GoInterface) (n a : w64) : Prop :=
  ∃ m : message, M !! a = some (interface.mkOk message.ty #m) ∧ m.n' = n

/-- Two distinct acceptors' entries are promises of `n`. -/
def twoProm (M : GMap w64 GoInterface) (n : w64) : Prop :=
  ∃ (a1 a2 : w64) (m1 m2 : message), a1 ≠ a2 ∧ M !! a1 = some (interface.mkOk message.ty #m1) ∧
    M !! a2 = some (interface.mkOk message.ty #m2) ∧ m1.n' = n ∧ m2.n' = n

theorem mem_take_ne {l : List w64} {n : Nat} {a k : w64} (hnd : l.Nodup) (ha : a ∈ l.take n)
    (hk : l[n]? = some k) : a ≠ k := by
  rintro rfl
  have h := List.take_append_drop n l
  rw [← h] at hnd
  have hk' : a ∈ l.drop n := by
    rw [List.mem_iff_getElem?]; exact ⟨0, by simp [List.getElem?_drop, hk]⟩
  exact (List.nodup_append.mp hnd).2.2 a ha a hk' rfl

theorem take_succ_mem {l : List w64} {n : Nat} {k : w64} (hk : l[n]? = some k) :
    k ∈ l.take (n + 1) := by
  rw [List.take_add_one, hk]; simp

theorem take_mono_mem {l : List w64} {n : Nat} {a : w64} (ha : a ∈ l.take n) :
    a ∈ l.take (n + 1) := by
  rw [List.take_add_one]; exact List.mem_append_left _ ha

theorem domOK_insert {M : GMap w64 GoInterface} {a : w64} (x : GoInterface) (h : domOK M)
    (ha : a ∈ accIds) : domOK (<[a := x]> M) := by
  intro k
  rw [GMap.lookup_insert_eq_iff]
  by_cases hk : a = k
  · subst hk; simp [ha]
  · simp [hk, h k]

theorem entsOK_insert {M : GMap w64 GoInterface} {vN a : w64} (m : message) (h : entsOK M vN)
    (hle : sint.Z m.prevn' ≤ sint.Z vN) :
    entsOK (<[a := interface.mkOk message.ty #m]> M) vN := by
  intro k x hk
  rw [GMap.lookup_insert_eq_iff] at hk
  by_cases hak : a = k
  · simp only [hak, ↓reduceIte, Option.some.injEq] at hk
    exact ⟨m, hk.symm, hle⟩
  · simp only [hak, ↓reduceIte] at hk
    exact h k x hk

theorem entsOK_mono {M : GMap w64 GoInterface} {vN vN' : w64} (h : entsOK M vN)
    (hle : sint.Z vN ≤ sint.Z vN') : entsOK M vN' := by
  intro k x hk
  obtain ⟨m, hx, hm⟩ := h k x hk
  exact ⟨m, hx, by omega⟩

theorem pInv_intro (Γ : Names) (c : w64) (v : GoString) (σ : PState) (h1 : domOK σ.M)
    (h2 : entsOK σ.M σ.vN) (h3 : 0 ≤ sint.Z σ.vN ∧ (σ.w.length : Int) < 2 ^ 48) :
    ([∗map] a ↦ x ∈ σ.M, entryOK (GF := GF) Γ a x) ∗ valOK Γ c σ.vN v σ.w ⊢ pInv Γ c v σ := by
  iintro ⟨#H1, #H2⟩
  unfold pInv
  simp only [named]
  isplitl []
  · ipureintro; exact h1
  isplitl []
  · ipureintro; exact h2
  isplitl []
  · iexact H1
  isplitl []
  · ipureintro; exact h3
  iexact H2

theorem entry_pfW (Γ : Names) (M : GMap w64 GoInterface) (a : w64) (m : message)
    (hM : M !! a = some (interface.mkOk message.ty #m)) (hn : m.n' ≠ W64 0) :
    ([∗map] a ↦ x ∈ M, entryOK (GF := GF) Γ a x) ⊢ pfW Γ a m.n' m.prevn' m.value' := by
  iintro #H
  ihave #Hx := BI.BigSepM.bigSepM_lookup hM $$ H
  unfold entryOK
  icases Hx with ⟨%m', %heq, Hx⟩
  have h1 := ((interface_mkOk_inj _ _ _ _).1 heq).2
  have h2 : m = m' := message_intoVal_inj (GF := GF) (hG := hG) h1
  subst h2
  icases Hx with (%h0 | #Hx)
  · exact absurd h0 hn
  · iexact Hx

/-- The initial map (`own_proposer`'s). -/
abbrev M0 : GMap w64 GoInterface :=
  {[W64 1 := zeroP]} ∪ {[W64 2 := zeroP]} ∪ {[W64 3 := zeroP]}

theorem M0_lookup (k : w64) (x : GoInterface) (h : M0 !! k = some x) : x = zeroP := by
  rw [show M0 = initMap accIds from initMap_accIds.symm] at h
  simp [initMap, accIds] at h
  by_cases h1 : (3#64 : w64) = k <;> by_cases h2 : (2#64 : w64) = k <;>
    by_cases h3 : (1#64 : w64) = k <;> simp_all

theorem M0_dom : domOK M0 := by
  intro k
  rw [show M0 = initMap accIds from initMap_accIds.symm]
  simp [initMap, accIds]
  by_cases h1 : (3#64 : w64) = k <;> by_cases h2 : (2#64 : w64) = k <;>
    by_cases h3 : (1#64 : w64) = k <;> simp_all <;> grind

theorem M0_ents : entsOK M0 (W64 0) := by
  intro k x h
  exact ⟨Perennial.zero_val message, M0_lookup k x h, Int.le_of_eq (by rfl)⟩

theorem M0_entries (Γ : Names) : ⊢ [∗map] a ↦ x ∈ M0, entryOK (GF := GF) Γ a x := by
  iapply BI.BigSepM.bigSepM_forall_elim
  iintro %k %x %hk
  have := M0_lookup k x hk
  subst this
  unfold entryOK
  iexists Perennial.zero_val message
  isplitl []
  · ipureintro; rfl
  ileft; ipureintro; rfl

theorem pInv_set_ls (Γ : Names) (c : w64) (v : GoString) (σ : PState) (x : w64) :
    pInv (GF := GF) Γ c v { σ with ls := x } = pInv Γ c v σ := rfl

theorem pInv_ls_intro (Γ : Names) (c : w64) (v : GoString) (σ : PState) (x : w64) :
    pInv (GF := GF) Γ c v σ ⊢ pInv Γ c v { σ with ls := x } := by
  unfold pInv; exact .rfl

theorem msgOK_to_prop (Γ : Names) (m : message) (hto : m.to' ∈ propIds) :
    msgOK (GF := GF) Γ m ⊢
      ⌜m.typ' = W64 3 ∧ m.from' ∈ accIds⌝ ∗ pfW Γ m.from' m.n' m.prevn' m.value' := by
  have hacc : m.to' ∉ accIds := by
    simp only [propIds, accIds, List.mem_cons, List.not_mem_nil, or_false] at hto ⊢
    rcases hto with h | h | h | h <;> rw [h] <;> decide
  unfold msgOK
  rw [if_neg hacc, if_pos hto]

theorem valOK_issue (Γ : Names) (c vN : w64) (v w : GoString) :
    valOK (GF := GF) Γ c vN v w ⊢ if vN = W64 0 then ∃ c', regW Γ c' w else propW Γ vN w := by
  unfold valOK
  split
  · iintro ⟨#H, -⟩; iexists c; iexact H
  · exact .rfl

theorem pInv_pure (Γ : Names) (c : w64) (v : GoString) (σ : PState) :
    pInv (GF := GF) Γ c v σ ⊢ ⌜domOK σ.M ∧ entsOK σ.M σ.vN ∧ 0 ≤ sint.Z σ.vN ∧
      (σ.w.length : Int) < 2 ^ 48⌝ := by
  iintro H
  iNamed H
  ipureintro
  exact ⟨Hdom, Hent, HvN⟩

theorem domOK_size (M : GMap w64 GoInterface) (h : domOK M) : GMap.size M = 3 := by
  rw [GMap.size_eq_length M accIds (by decide) (fun k => (h k).symm)]
  rfl

theorem message.wp_number (m : message) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (m @!! message.ty @!! go!"number")) (Val #()))
    {{ RET #m.n'; True }} := by
  wp_start
  wp_auto
  wp_end

theorem message.wp_proposalNumber (m : message) (h : m.typ' = W64 3) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (m @!! message.ty @!! go!"proposalNumber")) (Val #()))
    {{ RET #m.prevn'; True }} := by
  wp_start
  wp_auto
  rw [h]
  wp_auto
  wp_end

theorem message.wp_proposalValue (m : message) (h : m.typ' = W64 3) :
    {{ isPkgInit (PROP := IProp GF) pkg }}
      (App (Val (m @!! message.ty @!! go!"proposalValue")) (Val #()))
    {{ RET #m.value'; True }} := by
  wp_start
  wp_auto
  rw [h]
  wp_auto
  wp_end

theorem proposer.wp_n (pp : Loc) (id ls : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pp.[proposer, go!"id"] ↦ id ∗
        pp.[proposer, go!"lastSeq"] ↦ ls }}
      (App (Val (pp @!! go.GoType.PointerType proposer.ty @!! go!"n")) (Val #()))
    {{ RET #(nOf ls id); pp.[proposer, go!"id"] ↦ id ∗ pp.[proposer, go!"lastSeq"] ↦ ls }} := by
  wp_start as ⟨Hid, Hls⟩
  wp_auto
  unfold nOf
  iapply HΦ; iframe

theorem proposer.wp_majority (pp am : Loc) (M : GMap w64 GoInterface) (dq : DFrac)
    (hdom : domOK M) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pp.[proposer, go!"acceptors"] ↦ am ∗ am ↦${dq} M }}
      (App (Val (pp @!! go.GoType.PointerType proposer.ty @!! go!"majority")) (Val #()))
    {{ RET #(W64 2); pp.[proposer, go!"acceptors"] ↦ am ∗ am ↦${dq} M }} := by
  wp_start as ⟨Hacc, Ham⟩
  wp_auto
  wp_apply wp_map_len $$ Ham as Ham
  rw [domOK_size _ hdom, show BitVec.sdiv (W64 ((3 : Nat) : Int)) (W64 2) + W64 1 = W64 2 by decide]
  iapply HΦ; iframe

theorem ownMap_halves (am : Loc) (M : GMap w64 GoInterface) :
    (am ↦$ M : IProp GF) ⊣⊢ am ↦${DFrac.own (1 : Qp).half} M ∗ am ↦${DFrac.own (1 : Qp).half} M := by
  have h := (ownMap_fractional (GF := GF) am M).fractional (1 : Qp).half (1 : Qp).half
  rw [Qp.half_add_half] at h
  exact h

theorem proposer.wp_majorityReached (pp : Loc) (id : w64) (nt am : Loc) (σ : PState)
    (hdom : domOK σ.M) (hent : entsOK σ.M σ.vN) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pFields pp id nt am σ }}
      (App (Val (pp @!! go.GoType.PointerType proposer.ty @!! go!"majorityReached")) (Val #()))
    {{ (b : Bool), RET #b; pFields pp id nt am σ ∗
        ⌜b = true → twoProm σ.M (nOf σ.ls id)⌝ }} := by
  wp_start as Hf
  iNamed Hf
  wp_auto
  ipersist p
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  wp_func_lits
  iapply (wp_map_for_range (fun keys (i : Int) => iprop(∃ (cnt : w64) (pv : GoInterface),
      "m" ∷ m_ptr ↦ cnt ∗ "promise" ∷ promise_ptr ↦ pv ∗ "id" ∷ pp.[proposer, go!"id"] ↦ id ∗
      "lastSeq" ∷ pp.[proposer, go!"lastSeq"] ↦ σ.ls ∗
      "%Hcnt" ∷ ⌜0 ≤ sint.Z cnt ∧ sint.Z cnt ≤ i ∧ 0 ≤ i ∧ i ≤ 3 ∧
        (1 ≤ sint.Z cnt → ∃ a1, a1 ∈ keys.take i.toNat ∧ goodAt σ.M (nOf σ.ls id) a1) ∧
        (2 ≤ sint.Z cnt → twoProm σ.M (nOf σ.ls id))⌝))) $$ Ham
  iintro %keys %Hkeys
  isplitl [m promise id lastSeq]
  · iexists _, _; iframe; ipureintro; simp
  isplitr
  · imodintro
    iintro %i %key %x %Hkx Hinv
    iNamed Hinv
    obtain ⟨m, rfl, -⟩ := hent key x Hkx.2
    wp_auto
    wp_apply message.wp_number
    wp_apply proposer.wp_n $$ [$id $lastSeq] as ⟨id, lastSeq⟩
    have hnd := Hkeys.2.2
    have hlen : keys.length = 3 := by rw [Hkeys.2.1, domOK_size _ hdom]
    have hi3 : i.toNat < 3 := by
      have := (List.getElem?_eq_some_iff.mp Hkx.1).1; omega
    have hsucc : (i + 1).toNat = i.toNat + 1 := by omega
    obtain ⟨hc0, hci, hi0, -, hc1, hc2⟩ := Hcnt
    wp_if_destruct
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      iframe
      ipureintro
      have hgood : goodAt σ.M (nOf σ.ls id) key := ⟨m, Hkx.2, Hif⟩
      have hc : sint.Z (cnt + W64 1) = sint.Z cnt + 1 := by word
      rw [hc, hsucc]
      refine ⟨by omega, by omega, by omega, by omega, fun _ => ⟨key, take_succ_mem Hkx.1, hgood⟩,
        fun h2 => ?_⟩
      obtain ⟨a1, ha1, hg1⟩ := hc1 (by omega)
      obtain ⟨m1, h1, hn1⟩ := hg1
      exact ⟨a1, key, m1, m, mem_take_ne hnd ha1 Hkx.1, h1, Hkx.2, hn1, Hif⟩
    · unfold forMapPostcondition
      iright; ileft
      isplitr
      · ipureintro; rfl
      iexists _, _
      iframe
      ipureintro
      rw [hsucc]
      refine ⟨by omega, by omega, by omega, by omega, fun h1 => ?_, hc2⟩
      obtain ⟨a1, ha1, hg1⟩ := hc1 h1
      exact ⟨a1, take_mono_mem ha1, hg1⟩
  iintro Hinv Ham
  iNamed Hinv
  wp_auto
  wp_apply proposer.wp_majority pp am σ.M _ hdom $$ [$acceptors $Ham] as ⟨acceptors, Ham⟩
  wp_if_destruct
  · iapply HΦ; unfold pFields; iframe
    ipureintro; intro; exact Hcnt.2.2.2.2.2 (by word)
  · iapply HΦ; unfold pFields; iframe
    ipureintro; intro h; cases h

theorem proposer.wp_receivePromise (Γ : Names) (c : w64) (v : GoString) (pp : Loc) (id : w64)
    (nt am : Loc) (σ : PState) (m : message)
    (htyp : m.typ' = W64 3) (hfrom : m.from' ∈ accIds) (hwf : msgWf m) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ isPaxos Γ ∗ pFields pp id nt am σ ∗ pInv Γ c v σ ∗
        pfW Γ m.from' m.n' m.prevn' m.value' }}
      (App (Val (pp @!! go.GoType.PointerType proposer.ty @!! go!"receivePromise")) (Val #m))
    {{ (σ' : PState), RET #(); pFields pp id nt am σ' ∗ pInv Γ c v σ' ∗ ⌜σ'.ls = σ.ls⌝ }} := by
  wp_start as ⟨#Hpx, Hf, #Hinv, #Hpf⟩
  iNamed Hf
  iNamed Hinv
  have hsome := (Hdom m.from').2 hfrom
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
  obtain ⟨pm, rfl, hpm⟩ := Hent _ _ hx
  wp_auto
  wp_apply wp_map_lookup1 $$ Ham as Ham
  rw [hx]
  wp_auto
  wp_apply message.wp_number
  wp_method_call
  wp_call
  wp_auto
  wp_apply message.wp_number
  iapply fupd_wp
  imod (inv_pf_prop Γ ⊤ m.from' m.n' m.prevn' m.value' CoPset.subseteq_top) $$ Hpx Hpf
    with ⟨%hk0, Hkp⟩
  imodintro
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
      [interface.mkOk go.int #id, interface.mkOk go.int #m.n']
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %args_sl ⟨Hargs, -⟩
    have hpf1 : fmt.ArgsWf [interface.mkOk go.int #id, interface.mkOk go.int #m.n'] :=
      fmt.ArgsWf.cons_int _ _ _ (.int id) (fmt.ArgsWf.cons_int _ _ _ (.int m.n') fmt.ArgsWf.nil)
    wp_apply log.wp_Printf _ _ _ _ hpf1 $$ [Hargs]
    · iframe
    iintro -
    wp_auto
    wp_apply wp_mapInsert $$ Ham as Ham
    wp_method_call; wp_call; wp_auto
    wp_apply message.wp_proposalNumber m htyp
    ihave #Hnew : entryOK Γ m.from' (interface.mkOk message.ty #m) $$ [Hpf]
    · unfold entryOK; iexists m
      isplitl []
      · ipureintro; rfl
      iright; iexact Hpf
    ihave #Hents' := BigSepM.bigSepM_insert_elim $$ Hnew Hents
    wp_if_destruct
    · have hk0' : m.prevn' ≠ W64 0 := by intro h; rw [h] at Hif; simp at Hif; omega
      simp only [hk0', ↓reduceIte]
      icases Hkp with #Hkp
      wp_method_call; wp_call; wp_auto
      wp_apply message.wp_proposalValue m htyp
      wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
        [interface.mkOk go.int #id, interface.mkOk go.string #σ.w, interface.mkOk go.string #m.value']
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %args_sl2 ⟨Hargs, -⟩
      have hpf2 : fmt.ArgsWf [interface.mkOk go.int #id, interface.mkOk go.string #σ.w,
          interface.mkOk go.string #m.value'] :=
        fmt.ArgsWf.cons_int _ _ _ (.int id) (fmt.ArgsWf.cons_string _ _
          (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil))
      wp_apply log.wp_Printf _ _ _ _ hpf2 $$ [Hargs]
      · iframe
      iintro -
      wp_auto
      wp_method_call; wp_call; wp_auto
      wp_apply message.wp_proposalNumber m htyp
      wp_method_call; wp_call; wp_auto
      wp_apply message.wp_proposalValue m htyp
      ispecialize HΦ $$
        %(PState.mk σ.ls m.value' m.prevn' (<[m.from' := interface.mkOk message.ty #m]> σ.M))
      iapply HΦ
      unfold pFields
      iframe
      isplitl []
      · iapply pInv_intro
        · exact domOK_insert _ Hdom hfrom
        · show entsOK (<[m.from' := interface.mkOk message.ty #m]> σ.M) m.prevn'
          exact entsOK_insert m (entsOK_mono Hent (by omega)) (by omega)
        · show 0 ≤ sint.Z m.prevn' ∧ (m.value'.length : Int) < 2 ^ 48
          exact ⟨hk0, hwf⟩
        isplitl []
        · iexact Hents'
        unfold valOK
        simp only [hk0', ↓reduceIte]
        iexact Hkp
      ipureintro; rfl
    · ispecialize HΦ $$ %{ σ with M := <[m.from' := interface.mkOk message.ty #m]> σ.M }
      iapply HΦ
      unfold pFields
      iframe
      isplitl []
      · iapply pInv_intro
        · exact domOK_insert _ Hdom hfrom
        · exact entsOK_insert m Hent (by simp only; omega)
        · exact HvN
        isplitl []
        · iexact Hents'
        iexact Hval
      ipureintro; rfl
  · ispecialize HΦ $$ %σ
    iapply HΦ
    unfold pFields
    iframe
    isplitl []
    · iapply pInv_intro
      · exact Hdom
      · exact Hent
      · exact HvN
      isplitl []
      · iexact Hents
      iexact Hval
    ipureintro; rfl

/-- An outgoing message: it fits and its meaning holds (persistent). -/
def outOK (Γ : Names) (m : message) : IProp GF := iprop(msgOK Γ m ∗ ⌜msgWf m⌝)

instance outOK_persistent (Γ : Names) (m : message) : Persistent (outOK (GF := GF) Γ m) := by
  unfold outOK; infer_instance

theorem outOK_set (Γ : Names) (ms : List message) (j : Nat) (m : message) :
    ([∗list] x ∈ ms, outOK (GF := GF) Γ x) ∗ outOK Γ m ⊢ [∗list] x ∈ ms.set j m, outOK Γ x := by
  iintro ⟨#H, #Hm⟩
  ihave #H' := BI.BigSepL.bigSepL_forall_intro $$ H
  iapply BI.BigSepL.bigSepL_forall_elim
  iintro %k %x %hk
  rw [List.getElem?_set] at hk
  split at hk
  · split at hk
    · cases hk; iexact Hm
    · cases hk
  · iapply H' $$ %k %x %hk

theorem outOK_zero (Γ : Names) : ⊢ outOK (GF := GF) Γ (zero_val message) := by
  unfold outOK msgOK
  rw [show (zero_val message) = ⟨W64 0, W64 0, W64 0, W64 0, W64 0, []⟩ from rfl]
  simp [accIds, propIds, lrnIds, boxIds, msgWf]
  istart
  isplitl [] <;> ipureintro <;> trivial

/-- `prepare`'s message to `to`. -/
abbrev prepMsg (id to n : w64) : message :=
  { from' := id, to' := to, typ' := W64 1, n' := n, prevn' := 0, value' := [] }

theorem proposer.wp_prepare (Γ : Names) (pp : Loc) (id : w64) (nt am : Loc) (σ : PState)
    (hid : id ∈ propIds) (hdom : domOK σ.M) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pFields pp id nt am σ }}
      (App (Val (pp @!! go.GoType.PointerType proposer.ty @!! go!"prepare")) (Val #()))
    {{ (s : GoSlice) (ms : List message), RET #s;
        pFields pp id nt am { σ with ls := σ.ls + W64 1 } ∗ s ↦* ms ∗
        [∗list] m ∈ ms, outOK Γ m }} := by
  wp_start as Hf
  iNamed Hf
  wp_auto
  wp_apply proposer.wp_majority pp am σ.M _ hdom $$ [$acceptors $Ham] as ⟨acceptors, Ham⟩
  wp_apply (wp_slice_make2 (V := message) (W64 2)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  icases (ownMap_halves am σ.M).1 $$ Ham with ⟨Ham1, Ham2⟩
  ipersist p
  ipersist ms
  ihave #Hz := outOK_zero (GF := GF) Γ
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  wp_func_lits
  iapply (wp_map_for_range (fun _keys (_j : Int) => iprop(∃ (i : w64) (ms : List message) (t : w64),
      "i" ∷ i_ptr ↦ i ∗ "Hsl" ∷ sl ↦* ms ∗ "to" ∷ to_ptr ↦ t ∗
      "id" ∷ pp.[proposer, go!"id"] ↦ id ∗ "lastSeq" ∷ pp.[proposer, go!"lastSeq"] ↦ (σ.ls + W64 1) ∗
      "acceptors" ∷ pp.[proposer, go!"acceptors"] ↦ am ∗
      "Ham2" ∷ am ↦${DFrac.own (1 : Qp).half} σ.M ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i < 2 ∧ ms.length = 2⌝ ∗
      "#Hms" ∷ ([∗list] m ∈ ms, outOK Γ m) ∗
      "HΦ" ∷ (∀ (s : GoSlice) (ms : List message),
        (pFields pp id nt am { σ with ls := σ.ls + W64 1 } ∗ s ↦* ms ∗
          [∗list] m ∈ ms, outOK Γ m) -∗ Φ #s) ∗
      "value" ∷ pp.[proposer, go!"value"] ↦ σ.w ∗ "valueN" ∷ pp.[proposer, go!"valueN"] ↦ σ.vN ∗
      "nt" ∷ pp.[proposer, go!"nt"] ↦ ntIface nt ∗
      "res" ∷ «$res0_ptr» ↦ (Perennial.zero_val GoSlice)))) $$ Ham1
  iintro %keys %Hkeys
  isplitl [i Hsl to id lastSeq acceptors Ham2 HΦ value valueN nt «$res0»]
  · iexists _, _, _; iframe
    isplitl []
    · ipureintro; simp
    simp only [named]
    iapply BI.BigSepL.bigSepL_forall_elim
    iintro %k %x %hk
    have : x = Perennial.zero_val message := by
      rw [List.getElem?_replicate] at hk; split at hk <;> simp_all
    subst this; iexact Hz
  isplitr
  · imodintro
    iintro %j %key %x %Hkx Hinv
    iNamed Hinv
    have hkey : key ∈ accIds := (hdom key).1 (by rw [Hkx.2]; rfl)
    wp_auto
    wp_apply proposer.wp_n pp id (σ.ls + W64 1) $$ [$id $lastSeq] as ⟨id, lastSeq⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    have hsl : sint.Z sl.len = 2 := by have h1 := Hlen.1; have h2 := Hi.2.2; word
    rw [if_pos (by omega)]
    wp_apply wp_store_slice_index $$ [Hsl] as Hsl
    · iframe; ipureintro; omega
    wp_apply proposer.wp_majority pp am σ.M _ hdom $$ [$acceptors $Ham2] as ⟨acceptors, Ham2⟩
    ihave #Hm' : outOK Γ (prepMsg id key (nOf (σ.ls + W64 1) id)) $$ []
    · unfold outOK msgOK
      simp only [hkey, ↓reduceIte]
      isplitl []
      · ileft; ipureintro; exact ⟨by trivial, hid⟩
      · ipureintro; simp [msgWf]
    ihave #Hms' : [∗list] m ∈ ms.set (sint.Z i).toNat (prepMsg id key (nOf (σ.ls + W64 1) id)),
      outOK Γ m $$ []
    · iapply outOK_set
      isplitl []
      · iexact Hms
      · iexact Hm'
    wp_if_destruct
    · unfold forMapPostcondition
      iright; iright; ileft
      isplitl []
      · ipureintro; rfl
      iintro Ham1
      ihave Ham := (ownMap_halves am σ.M).2 $$ [Ham1 Ham2]
      · iframe
      wp_auto
      iapply HΦ
      unfold pFields
      iframe
      iexact Hms'
    · unfold forMapPostcondition
      iright; ileft
      isplitl []
      · ipureintro; rfl
      iexists _, _, _
      iframe
      isplitl []
      · ipureintro; simp only [List.length_set]; refine ⟨by word, ?_, Hi.2.2⟩
        have h2 : i + W64 1 ≠ W64 2 := Hif
        have : sint.Z i < 1 ∨ sint.Z i = 1 := by omega
        rcases this with h | h
        · word
        · exfalso; apply h2; word
      iexact Hms'
  iintro Hinv Ham1
  iNamed Hinv
  ihave Ham := (ownMap_halves am σ.M).2 $$ [Ham1 Ham2]
  · iframe
  wp_auto
  iapply HΦ
  unfold pFields
  iframe
  iexact Hms

/-- `propose`'s message to `to`. -/
abbrev propMsg (id to n : w64) (w : GoString) : message :=
  { from' := id, to' := to, typ' := W64 2, n' := n, prevn' := 0, value' := w }

theorem proposer.wp_propose (Γ : Names) (c : w64) (v : GoString) (pp : Loc) (id : w64)
    (nt am : Loc) (σ : PState) (hid : id ∈ propIds) :
    {{ isPkgInit (PROP := IProp GF) pkg ∗ pFields pp id nt am σ ∗ pInv Γ c v σ ∗
        propW Γ (nOf σ.ls id) σ.w }}
      (App (Val (pp @!! go.GoType.PointerType proposer.ty @!! go!"propose")) (Val #()))
    {{ (s : GoSlice) (ms : List message), RET #s;
        pFields pp id nt am σ ∗ s ↦* ms ∗ [∗list] m ∈ ms, outOK Γ m }} := by
  wp_start as ⟨Hf, #Hinv, #Hprop⟩
  iNamed Hf
  iNamed Hinv
  wp_auto
  wp_apply proposer.wp_majority pp am σ.M _ Hdom $$ [$acceptors $Ham] as ⟨acceptors, Ham⟩
  wp_apply (wp_slice_make2 (V := message) (W64 2)) as %sl ⟨Hsl, -⟩
  · ipureintro; decide
  icases (ownMap_halves am σ.M).1 $$ Ham with ⟨Ham1, Ham2⟩
  ipersist p
  ipersist ms
  ihave #Hz := outOK_zero (GF := GF) Γ
  have hn0 := nOf_ne_zero σ.ls id hid
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  wp_func_lits
  iapply (wp_map_for_range (fun _keys (_j : Int) => iprop(∃ (i : w64) (ms : List message) (t : w64)
      (pv : GoInterface),
      "i" ∷ i_ptr ↦ i ∗ "Hsl" ∷ sl ↦* ms ∗ "to" ∷ to_ptr ↦ t ∗ "promise" ∷ promise_ptr ↦ pv ∗
      "id" ∷ pp.[proposer, go!"id"] ↦ id ∗ "lastSeq" ∷ pp.[proposer, go!"lastSeq"] ↦ σ.ls ∗
      "value" ∷ pp.[proposer, go!"value"] ↦ σ.w ∗
      "acceptors" ∷ pp.[proposer, go!"acceptors"] ↦ am ∗
      "Ham2" ∷ am ↦${DFrac.own (1 : Qp).half} σ.M ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i < 2 ∧ ms.length = 2⌝ ∗
      "#Hms" ∷ ([∗list] m ∈ ms, outOK Γ m) ∗
      "HΦ" ∷ (∀ (s : GoSlice) (ms : List message),
        (pFields pp id nt am σ ∗ s ↦* ms ∗ [∗list] m ∈ ms, outOK Γ m) -∗ Φ #s) ∗
      "valueN" ∷ pp.[proposer, go!"valueN"] ↦ σ.vN ∗
      "nt" ∷ pp.[proposer, go!"nt"] ↦ ntIface nt ∗
      "res" ∷ «$res0_ptr» ↦ (Perennial.zero_val GoSlice)))) $$ Ham1
  iintro %keys %Hkeys
  isplitl [i Hsl to promise id lastSeq value acceptors Ham2 HΦ valueN nt «$res0»]
  · iexists _, _, _, _; iframe
    isplitl []
    · ipureintro; simp
    simp only [named]
    iapply BI.BigSepL.bigSepL_forall_elim
    iintro %k %x %hk
    have : x = Perennial.zero_val message := by
      rw [List.getElem?_replicate] at hk; split at hk <;> simp_all
    subst this; iexact Hz
  isplitr
  · imodintro
    iintro %j %key %x %Hkx Hinv
    iNamed Hinv
    have hkey : key ∈ accIds := (Hdom key).1 (by rw [Hkx.2]; rfl)
    obtain ⟨m, rfl, -⟩ := Hent key x Hkx.2
    wp_auto
    wp_apply message.wp_number
    wp_apply proposer.wp_n pp id σ.ls $$ [$id $lastSeq] as ⟨id, lastSeq⟩
    ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
    have hsl : sint.Z sl.len = 2 := by have h1 := Hlen.1; have h2 := Hi.2.2; word
    wp_if_destruct
    · ihave #Hpf := entry_pfW Γ σ.M key m Hkx.2 (by rw [Hif]; exact hn0) $$ Hents
      rw [Hif]
      wp_apply proposer.wp_n pp id σ.ls $$ [$id $lastSeq] as ⟨id, lastSeq⟩
      rw [if_pos (by omega)]
      wp_apply wp_store_slice_index $$ [Hsl] as Hsl
      · iframe; ipureintro; omega
      wp_apply proposer.wp_majority pp am σ.M _ Hdom $$ [$acceptors $Ham2] as ⟨acceptors, Ham2⟩
      ihave #Hm' : outOK Γ (propMsg id key (nOf σ.ls id) σ.w) $$ []
      · unfold outOK msgOK
        simp only [hkey, ↓reduceIte]
        isplitl []
        · iright
          isplitl []
          · ipureintro; trivial
          isplitl []
          · iexact Hprop
          iexists m.prevn', m.value'
          iexact Hpf
        · ipureintro; simp only [msgWf]; exact HvN.2
      ihave #Hms' : [∗list] m ∈ ms.set (sint.Z i).toNat (propMsg id key (nOf σ.ls id) σ.w),
        outOK Γ m $$ []
      · iapply outOK_set
        isplitl []
        · iexact Hms
        · iexact Hm'
      wp_if_destruct
      · unfold forMapPostcondition
        iright; iright; ileft
        isplitl []
        · ipureintro; rfl
        iintro Ham1
        ihave Ham := (ownMap_halves am σ.M).2 $$ [Ham1 Ham2]
        · iframe
        wp_auto
        iapply HΦ
        unfold pFields
        iframe
        iexact Hms'
      · unfold forMapPostcondition
        iright; ileft
        isplitl []
        · ipureintro; rfl
        iexists _, _, _, _
        iframe
        isplitl []
        · ipureintro; simp only [List.length_set]; refine ⟨by word, ?_, Hi.2.2⟩
          have h2 : i + W64 1 ≠ W64 2 := Hif
          have : sint.Z i < 1 ∨ sint.Z i = 1 := by omega
          rcases this with h | h
          · word
          · exfalso; apply h2; word
        iexact Hms'
    · wp_apply proposer.wp_majority pp am σ.M _ Hdom $$ [$acceptors $Ham2] as ⟨acceptors, Ham2⟩
      wp_if_destruct
      · exfalso; exact absurd Hi.2.1 (by decide)
      · unfold forMapPostcondition
        iright; ileft
        isplitl []
        · ipureintro; rfl
        iexists _, _, _, _
        iframe
        isplitl []
        · ipureintro; exact Hi
        iexact Hms
  iintro Hinv Ham1
  iNamed Hinv
  ihave Ham := (ownMap_halves am σ.M).2 $$ [Ham1 Ham2]
  · iframe
  wp_auto
  iapply HΦ
  unfold pFields
  iframe
  iexact Hms

theorem proposer.run.wp_proof (wp_send : tcpNetwork.send.spec (GF := GF) (hG := hG))
    (wp_recv : tcpNetwork.recv.spec (GF := GF) (hG := hG)) :
    proposer.run.spec (GF := GF) (hG := hG) := fun Γ pp id v c => by
  wp_start as ⟨Hown, Htok, #Hreg⟩
  unfold own_proposer
  icases Hown with ⟨%nt, %nd, %amap, %ids, %am, Henv, %Hpre, Hid, Hls, Hval, HvN, Hacc, Hnt, Ham⟩
  unfold agentEnv
  icases Henv with ⟨#Hpx, #Hnode, Hnet, %Hids⟩
  ihave #Hents0 := M0_entries (GF := GF) Γ
  ihave #Hinv0 : pInv Γ c v (PState.mk (W64 0) v (W64 0) M0) $$ []
  · iapply pInv_intro
    · exact M0_dom
    · exact M0_ents
    · show 0 ≤ sint.Z (W64 0) ∧ (v.length : Int) < 2 ^ 48
      exact ⟨by decide, Hpre.2⟩
    isplitl []
    · iexact Hents0
    unfold valOK
    simp only [↓reduceIte]
    isplitl []
    · iexact Hreg
    · ipureintro; trivial
  wp_auto
  ihave HI : (∃ (σ : PState) (ok : Bool) (mv : message),
      "Hf" ∷ pFields pp id nt am σ ∗ "#Hinv" ∷ pInv Γ c v σ ∗ "ok" ∷ ok_ptr ↦ ok ∗
      "m" ∷ m_ptr ↦ mv ∗ "Hnet" ∷ own_net nt (msgOK Γ) nd id : IProp GF)
    $$ [Hid Hls Hval HvN Hacc Hnt Ham ok m Hnet]
  · iexists PState.mk (W64 0) v (W64 0) M0, false, Perennial.zero_val message
    simp only [named]
    isplitl [Hid Hls Hval HvN Hacc Hnt Ham]
    · unfold pFields; iframe
    isplitl []
    · iexact Hinv0
    iframe
  iclear Hinv0 Hents0
  wp_for HI
  ihave %Hp := pInv_pure $$ Hinv
  wp_apply proposer.wp_majorityReached pp id nt am σ Hp.1 Hp.2.1 $$ [$Hf] as %b ⟨Hf, %Hb⟩
  cases b
  · simp only [Bool.not_false, decide_true, ↓reduceIte]
    wp_auto
    wp_join iprop(∃ σ' : PState, "Hf" ∷ pFields pp id nt am σ' ∗ "#Hinv" ∷ pInv Γ c v σ' ∗
        "Hnet" ∷ own_net nt (msgOK Γ) nd id ∗ "%Hls" ∷ ⌜σ'.M = σ.M⌝ ∗ "p" ∷ p_ptr ↦ pp)
      at next with [Hf Hnet p] as HR
    · cases ok
      · simp only [Bool.not_false]
        wp_auto
        wp_apply proposer.wp_prepare Γ pp id nt am σ Hpre.1 Hp.1 $$ [$Hf] as %s %ms ⟨Hf, Hs, #Hms⟩
        iNamed Hf
        rename_i iv_ptr
        irename : (iv_ptr ↦ Perennial.zero_val w64 : IProp GF) => Hiv
        ihave %Hlen := ownSlice_len _ _ _ $$ Hs
        ihave HI2 : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "Hiv" ∷ (∃ x : w64, iv_ptr ↦ x) ∗
            "Hnet" ∷ own_net nt (msgOK Γ) nd id ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i Hiv Hnet]
        · iexists W64 0; iframe
          isplitl [Hiv]
          · iexists _; iexact Hiv
          ipureintro; word
        wp_for HI2
        wp_if_destruct
        · icases Hiv with ⟨%x0, Hiv⟩
          rw [if_pos ⟨Hj.1, Hif⟩]
          list_elem ms (sint.nat j) as mm
          wp_apply wp_load_slice_index s (sint.Z j) ms _ mm Hj.1 $$ [Hs] as Hs
          · iframe; ipureintro; exact Hmm_lookup
          rw [if_pos ⟨Hj.1, Hif⟩]
          wp_apply wp_load_slice_index s (sint.Z j) ms _ mm Hj.1 $$ [Hs] as Hs
          · iframe; ipureintro; exact Hmm_lookup
          ihave #Hmm := BI.BigSepL.bigSepL_lookup Hmm_lookup $$ Hms
          unfold outOK
          icases Hmm with ⟨#Hok, %Hwf⟩
          wp_apply (wp_send (msgOK Γ) nt nd amap ids id mm) $$ [$Hnode $Hnet] as Hnet
          · isplitl []
            · iexact Hok
            · ipureintro; exact Hwf
          wp_for_post
          iframe
          iexists j + W64 1
          iframe
          isplitl [Hiv]
          · iexists _; iexact Hiv
          ipureintro; word
        · wp_join_done
          iexists { σ with ls := σ.ls + W64 1 }
          simp only [named]
          isplitl [id lastSeq value valueN acceptors nt Ham]
          · unfold pFields; iframe
          isplitl []
          · iapply pInv_ls_intro; iexact Hinv
          isplitl [Hnet]
          · iexact Hnet
          isplitl []
          · ipureintro; trivial
          iexact p
      · simp only [Bool.not_true]
        wp_auto
        wp_join_done
        iexists σ
        simp only [named]
        isplitl [Hf]
        · iexact Hf
        isplitl []
        · iexact Hinv
        isplitl [Hnet]
        · iexact Hnet
        isplitl []
        · ipureintro; trivial
        iexact p
    iNamed HR
    iNamed Hf
    wp_auto
    wp_apply (wp_recv (msgOK Γ) nt nd amap ids id _ Hids) $$ [$Hnode $Hnet] as %mm %okb ⟨Hnet, Hm⟩
    cases okb
    · simp only [Bool.not_false]
      wp_auto
      wp_for_post
      iframe
      iexists σ', false, mm
      simp only [named]
      isplitl [id lastSeq value valueN acceptors nt Ham]
      · unfold pFields; iframe
      isplitl []
      · iexact Hinv
      iframe
    · simp only [Bool.not_true, ↓reduceIte]
      unfold inboxP
      icases Hm with ⟨Hok, %Hto, %Hwf⟩
      icases msgOK_to_prop Γ mm (by rw [Hto]; exact Hpre.1) $$ Hok with ⟨%Htyp, #Hpf⟩
      wp_auto
      rw [_root_.decide_eq_true Htyp.1]
      wp_auto
      wp_apply proposer.wp_receivePromise Γ c v pp id nt am σ' mm Htyp.1 Htyp.2 Hwf
        $$ [id lastSeq value valueN acceptors nt Ham] as %σ'' ⟨Hf, #Hinv'', %Hls''⟩
      · isplitl []
        · iexact Hpx
        isplitl [id lastSeq value valueN acceptors nt Ham]
        · unfold pFields; iframe
        isplitl []
        · iexact Hinv
        iexact Hpf
      wp_for_post
      iframe
      iexists σ'', true, mm
      simp only [named]
      isplitl [Hf]
      · iexact Hf
      isplitl []
      · iexact Hinv''
      iframe
  · simp only [Bool.not_true]
    have hne : (#false : val) ≠ #true := fun h => Bool.false_ne_true (go.intoVal_inj h)
    rw [decide_eq_false hne]
    simp only [Bool.false_eq_true, ↓reduceIte]
    obtain ⟨a1, a2, m1, m2, h12, h1, h2, hn1, hn2⟩ := Hb rfl
    have hn0 := nOf_ne_zero σ.ls id Hpre.1
    ihave #Hinv0 := Hinv
    iNamed Hinv0
    ihave #Hpf1 : pfW Γ a1 (nOf σ.ls id) m1.prevn' m1.value' $$ []
    · rw [← hn1]; iapply entry_pfW Γ σ.M a1 m1 h1 (by rw [hn1]; exact hn0); iexact Hents
    ihave #Hpf2 : pfW Γ a2 (nOf σ.ls id) m2.prevn' m2.value' $$ []
    · rw [← hn2]; iapply entry_pfW Γ σ.M a2 m2 h2 (by rw [hn2]; exact hn0); iexact Hents
    have ha1 : a1 ∈ accIds := (Hdom a1).1 (by rw [h1]; rfl)
    have ha2 : a2 ∈ accIds := (Hdom a2).1 (by rw [h2]; rfl)
    have hk1 : sint.Z m1.prevn' ≤ sint.Z σ.vN := by
      obtain ⟨m', hm', hle⟩ := Hent a1 _ h1
      have := message_intoVal_inj (GF := GF) (hG := hG) ((interface_mkOk_inj _ _ _ _).1 hm').2
      subst this; exact hle
    have hk2 : sint.Z m2.prevn' ≤ sint.Z σ.vN := by
      obtain ⟨m', hm', hle⟩ := Hent a2 _ h2
      have := message_intoVal_inj (GF := GF) (hG := hG) ((interface_mkOk_inj _ _ _ _).1 hm').2
      subst this; exact hle
    ihave Hv' : (if σ.vN = W64 0 then ∃ c', regW Γ c' σ.w else propW Γ σ.vN σ.w) $$ []
    · iapply valOK_issue; iexact Hval
    try simp only [_root_.decide_true, ↓reduceIte]
    iapply fupd_wp
    imod (inv_issue Γ ⊤ id (nOf σ.ls id) σ.vN σ.w a1 a2 m1.prevn' m2.prevn' m1.value' m2.value'
      CoPset.subseteq_top ha1 ha2 h12 (lowId_nOf σ.ls id Hpre.1) hk1 hk2) $$ Hpx Htok Hpf1 Hpf2 Hv'
      with #Hprop
    imodintro
    iNamed Hf
    wp_auto
    wp_apply proposer.wp_n pp id σ.ls $$ [$id $lastSeq] as ⟨id, lastSeq⟩
    wp_apply proposer.wp_majority pp am σ.M _ Hdom $$ [$acceptors $Ham] as ⟨acceptors, Ham⟩
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
      [interface.mkOk go.int #id, interface.mkOk go.int #(nOf σ.ls id), interface.mkOk go.int #(W64 2)]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %args1 ⟨Hargs, -⟩
    have hpf1 : fmt.ArgsWf [interface.mkOk go.int #id, interface.mkOk go.int #(nOf σ.ls id),
        interface.mkOk go.int #(W64 2)] :=
      fmt.ArgsWf.cons_int _ _ _ (.int id) (fmt.ArgsWf.cons_int _ _ _ (.int _)
        (fmt.ArgsWf.cons_int _ _ _ (.int _) fmt.ArgsWf.nil))
    wp_apply log.wp_Printf _ _ _ _ hpf1 $$ [Hargs]
    · iframe
    iintro -
    wp_auto
    wp_apply proposer.wp_n pp id σ.ls $$ [$id $lastSeq] as ⟨id, lastSeq⟩
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType (go.InterfaceType [])))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := GoInterface) (t := go.InterfaceType [])
      [interface.mkOk go.int #id, interface.mkOk go.int #(nOf σ.ls id), interface.mkOk go.string #σ.w]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %args2 ⟨Hargs, -⟩
    have hpf2 : fmt.ArgsWf [interface.mkOk go.int #id, interface.mkOk go.int #(nOf σ.ls id),
        interface.mkOk go.string #σ.w] :=
      fmt.ArgsWf.cons_int _ _ _ (.int id) (fmt.ArgsWf.cons_int _ _ _ (.int _)
        (fmt.ArgsWf.cons_string _ _ fmt.ArgsWf.nil))
    wp_apply log.wp_Printf _ _ _ _ hpf2 $$ [Hargs]
    · iframe
    iintro -
    wp_auto
    wp_apply proposer.wp_propose Γ c v pp id nt am σ Hpre.1
      $$ [id lastSeq value valueN acceptors nt Ham] as %s %ms ⟨Hf, Hs, #Hms⟩
    · isplitl [id lastSeq value valueN acceptors nt Ham]
      · unfold pFields; iframe
      isplitl []
      · iexact Hinv
      iexact Hprop
    iNamed Hf
    rename_i iv_ptr
    irename : (iv_ptr ↦ Perennial.zero_val w64 : IProp GF) => Hiv
    ihave %Hlen := ownSlice_len _ _ _ $$ Hs
    ihave HI2 : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "Hiv" ∷ (∃ x : w64, iv_ptr ↦ x) ∗
        "Hnet" ∷ own_net nt (msgOK Γ) nd id ∗
        "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ sint.Z s.len⌝ : IProp GF) $$ [i Hiv Hnet]
    · iexists W64 0; iframe
      isplitl [Hiv]
      · iexists _; iexact Hiv
      ipureintro; word
    wp_for HI2
    wp_if_destruct
    · icases Hiv with ⟨%x0, Hiv⟩
      rw [if_pos ⟨Hj.1, Hif⟩]
      list_elem ms (sint.nat j) as mm
      wp_apply wp_load_slice_index s (sint.Z j) ms _ mm Hj.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hmm_lookup
      rw [if_pos ⟨Hj.1, Hif⟩]
      wp_apply wp_load_slice_index s (sint.Z j) ms _ mm Hj.1 $$ [Hs] as Hs
      · iframe; ipureintro; exact Hmm_lookup
      ihave #Hmm := BI.BigSepL.bigSepL_lookup Hmm_lookup $$ Hms
      unfold outOK
      icases Hmm with ⟨#Hok, %Hwf⟩
      wp_apply (wp_send (msgOK Γ) nt nd amap ids id mm) $$ [$Hnode $Hnet] as Hnet
      · isplitl []
        · iexact Hok
        · ipureintro; exact Hwf
      wp_for_post
      iframe
      iexists j + W64 1
      iframe
      isplitl [Hiv]
      · iexists _; iexact Hiv
      ipureintro; word
    · iapply HΦ; itrivial

end proofs

end github_com.xiang90.paxos

end Perennial
