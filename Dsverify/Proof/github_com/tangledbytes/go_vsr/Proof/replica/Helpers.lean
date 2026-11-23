/-
Ported from dsverify-lab examples/vr/proof/VsrProof/Proof/replica/Helpers.lean (lab master 915f964;
notes/dsv-vr.md): over any `GF`, on the net extension.
-/
/-
The replica's small internal methods: `primaryForView`, `potentialPrimary`, `recordRequest`,
`recordResult`, `setIsRunning`; and the client table's pure updates.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.replica
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.replica.Pure

@[expose] public section

noncomputable section

namespace Perennial.github_com.tangledbytes.go_vsr.pkg

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel


/-- `recordRequest`'s table: `q` of client `c` recorded in progress unless the table has it or
a later one. -/
def replica.recReq [GooseExts] (tbl : GMap w64 replica.ClientTableData) (c q : w64) :
    GMap w64 replica.ClientTableData :=
  match tbl !! c with
  | some e => if uint.Z q ≤ uint.Z e.RequestNumber' then tbl
      else <[c := ⟨[], q, false⟩]> tbl
  | none => <[c := ⟨[], q, false⟩]> tbl

/-- `recordResult`'s table: `q`'s result `res` recorded unless the table has a later request. -/
def replica.recRes [GooseExts] (tbl : GMap w64 replica.ClientTableData) (c q : w64)
    (res : GoString) : GMap w64 replica.ClientTableData :=
  match tbl !! c with
  | some e => if uint.Z q < uint.Z e.RequestNumber' then tbl
      else <[c := ⟨res, q, true⟩]> tbl
  | none => <[c := ⟨res, q, true⟩]> tbl

/-! ## The members' slice length -/

/-- The members' slice of length `N` (from `ownSlice_len`): its length word is `N`, below
`2^63`. -/
theorem replica.len_of_slice (len : w64) (N : Nat) (h : N = sint.nat len ∧ 0 ≤ sint.Z len) :
    len = W64 N ∧ N < 2 ^ 63 := by
  obtain ⟨h1, h2⟩ := h
  subst h1
  constructor <;> word

/-- `x % N` on words is the model's `primary N`. -/
theorem replica.umod_nat (x : w64) (N : Nat) (hN : N < 2 ^ 63) :
    uint.nat (x % W64 N) = uint.nat x % N := by
  have h1 : uint.nat (W64 N) = N := by word
  have h2 : uint.nat (x % W64 N) = uint.nat x % uint.nat (W64 N) := BitVec.toNat_umod
  rw [h2, h1]

theorem replica.primary_word (x : w64) (N : Nat) (hN : N < 2 ^ 63) :
    primary N (uint.nat x) = uint.nat (x % W64 N) := by
  rw [replica.umod_nat x N hN]; rfl

/-- Go's `len(x) > len(members)/2` (signed division of a non-negative length) is the model's
majority `N < 2 * m`. -/
theorem replica.sdiv2 (N : Nat) (h : N < 2 ^ 63) :
    sint.Z (BitVec.sdiv (W64 N) (W64 2)) = ((N / 2 : Nat) : Int) := by
  have hm : (W64 N).msb = false := by
    rw [BitVec.msb_eq_decide]; simp; word
  have hm2 : (W64 2).msb = false := by decide
  rw [BitVec.sdiv_eq, hm, hm2]
  simp only
  have : (W64 N).udiv (W64 2) = W64 (N / 2) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_udiv]; word
  rw [this]; word

theorem replica.maj_of_sdiv (N m : Nat) (hN : N < 2 ^ 63) (hm : m < 2 ^ 63)
    (h : sint.Z (BitVec.sdiv (W64 N) (W64 2)) < sint.Z (W64 m)) : N < 2 * m := by
  rw [replica.sdiv2 N hN] at h
  have : sint.Z (W64 m) = (m : Int) := by word
  omega

theorem replica.umod_lt (x : w64) (N : Nat) (hN : N < 2 ^ 63) (h0 : 0 < N) :
    uint.nat (x % W64 N) < N := by
  rw [replica.umod_nat x N hN]; exact Nat.mod_lt _ h0

/-! ## The client table's coverage under its updates -/

theorem replica.covers_append [GooseExts] (t : GMap w64 replica.ClientTableData) (l1 l2 : List Entry) :
    replica.Covers t (l1 ++ l2) ↔ replica.Covers t l1 ∧ replica.Covers t l2 := by
  unfold replica.Covers; simp only [List.mem_append]
  exact ⟨fun h => ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩,
    fun h e he => he.elim (h.1 e) (h.2 e)⟩

theorem replica.covers_prefix [GooseExts] (t : GMap w64 replica.ClientTableData) {l1 l2 : List Entry}
    (hp : l1 <+: l2) (h : replica.Covers t l2) : replica.Covers t l1 :=
  fun e he => h e (hp.subset he)

theorem replica.recRes_ge [GooseExts] (tbl : GMap w64 replica.ClientTableData) (c q : w64)
    (res : GoString) (k : w64) (d : replica.ClientTableData) (h : tbl !! k = some d) :
    ∃ d', replica.recRes tbl c q res !! k = some d' ∧
      uint.nat d.RequestNumber' ≤ uint.nat d'.RequestNumber' := by
  unfold replica.recRes
  by_cases hk : c = k
  · subst hk
    rw [h]; simp only
    split
    · exact ⟨d, h, Nat.le_refl _⟩
    · exact ⟨_, GMap.lookup_insert _ _ _, by simp only; word⟩
  · cases hc : tbl !! c with
    | none => exact ⟨d, by rw [GMap.lookup_insert_ne _ _ hk, h], Nat.le_refl _⟩
    | some e =>
      simp only
      split
      · exact ⟨d, h, Nat.le_refl _⟩
      · exact ⟨d, by rw [GMap.lookup_insert_ne _ _ hk, h], Nat.le_refl _⟩

theorem replica.recReq_ge [GooseExts] (tbl : GMap w64 replica.ClientTableData) (c q : w64)
    (k : w64) (d : replica.ClientTableData) (h : tbl !! k = some d) :
    ∃ d', replica.recReq tbl c q !! k = some d' ∧
      uint.nat d.RequestNumber' ≤ uint.nat d'.RequestNumber' := by
  unfold replica.recReq
  by_cases hk : c = k
  · subst hk
    rw [h]; simp only
    split
    · exact ⟨d, h, Nat.le_refl _⟩
    · exact ⟨_, GMap.lookup_insert _ _ _, by simp only; word⟩
  · cases hc : tbl !! c with
    | none => exact ⟨d, by rw [GMap.lookup_insert_ne _ _ hk, h], Nat.le_refl _⟩
    | some e =>
      simp only
      split
      · exact ⟨d, h, Nat.le_refl _⟩
      · exact ⟨d, by rw [GMap.lookup_insert_ne _ _ hk, h], Nat.le_refl _⟩

theorem replica.covers_recRes [GooseExts] (tbl : GMap w64 replica.ClientTableData) (l : List Entry)
    (e : Entry) (res : GoString) (hc : e.cid < 2 ^ 64) (hq : e.req < 2 ^ 64)
    (h : replica.Covers tbl l) :
    replica.Covers (replica.recRes tbl (W64 e.cid) (W64 e.req) res) (l ++ [e]) := by
  rw [replica.covers_append]
  refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
  · obtain ⟨d, hd, hle⟩ := h e' he'
    obtain ⟨d', hd', hle'⟩ := replica.recRes_ge tbl _ _ res _ d hd
    exact ⟨d', hd', Nat.le_trans hle hle'⟩
  · simp at he'; subst he'
    unfold replica.recRes
    cases hcc : tbl !! W64 e'.cid with
    | none => exact ⟨_, GMap.lookup_insert _ _ _, by simp only; word⟩
    | some d =>
      simp only
      split
      · rename_i hlt; exact ⟨d, hcc, by word⟩
      · exact ⟨_, GMap.lookup_insert _ _ _, by simp only; word⟩

theorem replica.covers_recReq [GooseExts] (tbl : GMap w64 replica.ClientTableData) (l : List Entry)
    (e : Entry) (hc : e.cid < 2 ^ 64) (hq : e.req < 2 ^ 64)
    (h : replica.Covers tbl l) :
    replica.Covers (replica.recReq tbl (W64 e.cid) (W64 e.req)) (l ++ [e]) := by
  rw [replica.covers_append]
  refine ⟨fun e' he' => ?_, fun e' he' => ?_⟩
  · obtain ⟨d, hd, hle⟩ := h e' he'
    obtain ⟨d', hd', hle'⟩ := replica.recReq_ge tbl _ _ _ d hd
    exact ⟨d', hd', Nat.le_trans hle hle'⟩
  · simp at he'; subst he'
    unfold replica.recReq
    cases hcc : tbl !! W64 e'.cid with
    | none => exact ⟨_, GMap.lookup_insert _ _ _, by simp only; word⟩
    | some d =>
      simp only
      split
      · rename_i hlt; exact ⟨d, hcc, by word⟩
      · exact ⟨_, GMap.lookup_insert _ _ _, by simp only; word⟩

/-- A map with at least two entries has two distinct keys. -/
theorem replica.two_keys {V : Type} (m : GMap w64 V) (h : 2 ≤ GMap.size m) :
    ∃ a b va vb, a ≠ b ∧ m !! a = some va ∧ m !! b = some vb := by
  obtain ⟨a, va, ha⟩ := (GMap.map_size_ne_0_lookup m).mp (by omega)
  have hs := GMap.map_size_delete_Some m a va ha
  obtain ⟨b, vb, hb⟩ := (GMap.map_size_ne_0_lookup (GMap.delete a m)).mp (by omega)
  have hab : a ≠ b := by
    intro e; subst e; rw [GMap.lookup_delete] at hb; cases hb
  rw [GMap.lookup_delete_ne _ hab] at hb
  exact ⟨a, b, va, vb, hab, ha, hb⟩

/-- A map's keys (distinct), as replica ids. -/
noncomputable def replica.keyIds {V : Type} (m : GMap w64 V) : List Nat :=
  (m.toList.map Prod.fst).map uint.nat

theorem replica.keyIds_nodup {V : Type} (m : GMap w64 V) : (replica.keyIds m).Nodup :=
  List.Pairwise.map uint.nat (fun a b hab h => hab (by word)) (GMap.toList_keys_nodup m)

theorem replica.keyIds_length {V : Type} (m : GMap w64 V) :
    (replica.keyIds m).length = GMap.size m := by
  simp [replica.keyIds, GMap.size]

section keys
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]

/-- The facts of a map's keys, as a list over its key ids. -/
theorem replica.keyIds_facts {V : Type} (m : GMap w64 V) (g : Nat → VsrModel.Fact)
    (γ : VsrGhost.Names) :
    ([∗map] j ↦ _u ∈ m, VsrGhost.fact (GF := GF) γ (g (uint.nat j))) ⊢
    [∗list] f ∈ (replica.keyIds m).map g, VsrGhost.fact γ f := by
  refine BI.BigSepM.bigSepM_toList.1.trans ?_
  unfold replica.keyIds
  rw [List.map_map, List.map_map, BI.BigSepL.bigSepL_map]
  exact .rfl

end keys

section tbl
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions] [net.FieldAssumptions] [π : NetProtoGS]
variable [encoding.json.DecoderRep GF]

theorem replica.tblOk_recRes (γ : VsrGhost.Names) (tbl : GMap w64 replica.ClientTableData)
    (c q : w64) (res : GoString) (w0 : Nat) :
    ([∗map] k ↦ d ∈ tbl, replica.tblOk (GF := GF) γ k d) ∗
      VsrGhost.fact γ (.msg (.reply (uint.nat q) (uint.nat c) w0 res)) ⊢
    [∗map] k ↦ d ∈ replica.recRes tbl c q res, replica.tblOk γ k d := by
  iintro ⟨Ht, #Hf⟩
  unfold replica.recRes
  cases tbl !! c with
  | none =>
    iapply (BI.BigSepM.bigSepM_insert_elim (PROP := IProp GF)) $$ [] Ht
    unfold replica.tblOk; simp only [↓reduceIte]; iexists w0; iexact Hf
  | some e =>
    simp only
    split
    · iexact Ht
    · iapply (BI.BigSepM.bigSepM_insert_elim (PROP := IProp GF)) $$ [] Ht
      unfold replica.tblOk; simp only [↓reduceIte]; iexists w0; iexact Hf

theorem replica.tblOk_recReq (γ : VsrGhost.Names) (tbl : GMap w64 replica.ClientTableData)
    (c q : w64) :
    ([∗map] k ↦ d ∈ tbl, replica.tblOk (GF := GF) γ k d) ⊢
    [∗map] k ↦ d ∈ replica.recReq tbl c q, replica.tblOk γ k d := by
  iintro Ht
  unfold replica.recReq
  cases tbl !! c with
  | none =>
    iapply (BI.BigSepM.bigSepM_insert_elim (PROP := IProp GF)) $$ [] Ht
    unfold replica.tblOk; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
  | some e =>
    simp only
    split
    · iexact Ht
    · iapply (BI.BigSepM.bigSepM_insert_elim (PROP := IProp GF)) $$ [] Ht
      unfold replica.tblOk; simp only [Bool.false_eq_true, ↓reduceIte]; itrivial

end tbl

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [package_sem : replica.Assumptions]

set_option goose.wp.extras true

theorem replica.wp_primaryForView (rp : Loc) (v : replica.Replica)
    (ms : List ipv4port.IPv4Port) (N : Nat) (hN : 0 < N) (n : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ v.state'.ClusterMembers' ↦*□ ms ∗ ⌜ms.length = N⌝ }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"primaryForView"))
        (Val #n))
    {{ RET #(n % W64 N); rp ↦ v }} := by
  wp_start as ⟨Hr, #Hm, %Hl⟩
  ihave %Hlen := ownSlice_len $$ Hm
  wp_auto
  have h3 := (replica.len_of_slice _ N (by rw [← Hl]; exact Hlen)).1
  have hN63 := (replica.len_of_slice _ N (by rw [← Hl]; exact Hlen)).2
  rw [h3, if_neg (by word)]
  wp_auto
  wp_end

theorem replica.wp_potentialPrimary (rp : Loc) (v : replica.Replica)
    (ms : List ipv4port.IPv4Port) (N : Nat) (hN : 0 < N) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ v.state'.ClusterMembers' ↦*□ ms ∗ ⌜ms.length = N⌝ }}
      (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"potentialPrimary"))
        (Val #()))
    {{ RET #(v.state'.ViewNumber' % W64 N); rp ↦ v }} := by
  wp_start as ⟨Hr, #Hm, %Hl⟩
  wp_auto
  wp_apply (replica.wp_primaryForView rp v ms N hN) $$ [Hr] as Hr
  · iframe Hr Hm; ipureintro; exact Hl
  wp_end

theorem replica.wp_recordRequest (rp : Loc) (v : replica.Replica)
    (tbl : GMap w64 replica.ClientTableData) (c q : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ v.state'.ClientTable' ↦$ tbl }}
      (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"recordRequest"))
        (Val #c)) (Val #q))
    {{ RET #(); rp ↦ v ∗ v.state'.ClientTable' ↦$ replica.recReq tbl c q }} := by
  wp_start as ⟨Hr, Ht⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Ht as Ht
  unfold replica.recReq
  cases h : tbl !! c with
  | none =>
    wp_auto
    wp_apply wp_mapInsert $$ Ht as Ht
    wp_end
  | some e =>
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    wp_if_destruct
    · wp_end; simp only [show uint.Z q ≤ uint.Z e.RequestNumber' by word, ↓reduceIte]; iframe
    · wp_apply wp_mapInsert $$ Ht as Ht
      wp_end; simp only [show ¬ uint.Z q ≤ uint.Z e.RequestNumber' by word, ↓reduceIte]; iframe

theorem replica.wp_recordResult (rp : Loc) (v : replica.Replica)
    (tbl : GMap w64 replica.ClientTableData) (c q : w64) (res : GoString) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.replica ∗
        rp ↦ v ∗ v.state'.ClientTable' ↦$ tbl }}
      (App (App (App (Val (rp @!! go.GoType.PointerType replica.Replica.ty @!! go!"recordResult"))
        (Val #c)) (Val #q)) (Val #res))
    {{ RET #(); rp ↦ v ∗ v.state'.ClientTable' ↦$ replica.recRes tbl c q res }} := by
  wp_start as ⟨Hr, Ht⟩
  wp_auto
  wp_apply wp_map_lookup2 $$ Ht as Ht
  unfold replica.recRes
  cases h : tbl !! c with
  | none =>
    wp_auto
    wp_apply wp_mapInsert $$ Ht as Ht
    wp_end
  | some e =>
    simp only [Option.isSome_some, Option.getD_some]
    wp_auto
    wp_if_destruct
    · wp_end; simp only [show uint.Z q < uint.Z e.RequestNumber' by word, ↓reduceIte]; iframe
    · wp_apply wp_mapInsert $$ Ht as Ht
      wp_end; simp only [show ¬ uint.Z q < uint.Z e.RequestNumber' by word, ↓reduceIte]; iframe

end proofs

end Perennial.github_com.tangledbytes.go_vsr.pkg
