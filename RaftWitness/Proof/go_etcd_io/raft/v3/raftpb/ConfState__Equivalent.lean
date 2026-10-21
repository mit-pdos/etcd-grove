/-
Proof of `Spec/go_etcd_io/raft/v3/raftpb/ConfState__Equivalent.lean`. Port of the old
`Proof/go_etcd_io/raft/v3/raftpb/ConfState__Equivalent.lean` to raft v3.7: `Equivalent` now
clones both sides (`proto.Clone`, the trust boundary), sorts the clones' four id slices in place
(the closure `s` calls `slices.Sort`), makes their `AutoLeave` explicit, and compares them with
`proto.Equal` (the trust boundary, replacing `reflect.DeepEqual`). The argument is the old one:
sorted permutations of each other are equal (`sorted_perm_eq`), so the sorted clones hold one
record; nil-ness of the slices no longer matters (`proto.Equal` treats a nil and an empty repeated
field alike), so the old proof's `append([]uint64(nil), s...)` lemmas are gone.
-/
module

public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfState__Equivalent
public import RaftWitness.Spec.go_etcd_io.raft.v3.raftpb.ConfState__GetAutoLeave
public import RaftWitness.Spec.slices.Sort
public import RaftWitness.Spec.google_golang_org.protobuf.proto.CloneConfState
public import RaftWitness.Spec.google_golang_org.protobuf.proto.EqualConfState

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section pure

/-- A conf state `c'` is `c` sorted, with its `AutoLeave` kept: each list of `c'` a sorted
permutation of `c`'s. -/
def SortedOf (c c' : ConfStateM) : Prop :=
  c.lists.Perm c'.lists ∧ SortedW64 c'.Voters' ∧ SortedW64 c'.Learners' ∧
    SortedW64 c'.VotersOutgoing' ∧ SortedW64 c'.LearnersNext' ∧ c'.AutoLeave' = c.AutoLeave' ∧
    c'.Witness' = c.Witness'

/-- Two sorted versions of conf states whose lists are permutations of each other, with equal
`AutoLeave`, are one record: what makes `proto.Equal` answer `true`. -/
theorem sortedOf_eq {c1 c2 c1' c2' : ConfStateM} (hp : c1.lists.Perm c2.lists)
    (ha : c1.AutoLeave' = c2.AutoLeave') (hw : c1.Witness' = c2.Witness')
    (h1 : SortedOf c1 c1') (h2 : SortedOf c2 c2') :
    c1' = c2' := by
  obtain ⟨⟨p1v, p1l, p1o, p1n⟩, s1v, s1l, s1o, s1n, a1, w1⟩ := h1
  obtain ⟨⟨p2v, p2l, p2o, p2n⟩, s2v, s2l, s2o, s2n, a2, w2⟩ := h2
  obtain ⟨pv, pl, po, pn⟩ := hp
  simp only [ConfStateM.lists] at p1v p1l p1o p1n p2v p2l p2o p2n pv pl po pn
  rw [sortedW64_iff_pairwise] at s1v s1l s1o s1n s2v s2l s2o s2n
  have ev := sorted_perm_eq _ _ (p1v.symm.trans (pv.trans p2v)) s1v s2v
  have el := sorted_perm_eq _ _ (p1l.symm.trans (pl.trans p2l)) s1l s2l
  have eo := sorted_perm_eq _ _ (p1o.symm.trans (po.trans p2o)) s1o s2o
  have en := sorted_perm_eq _ _ (p1n.symm.trans (pn.trans p2n)) s1n s2n
  have ea : c1'.AutoLeave' = c2'.AutoLeave' := by rw [a1, a2, ha]
  have ew : c1'.Witness' = c2'.Witness' := by rw [w1, w2, hw]
  cases c1'; cases c2'
  simp only at ev el eo en ea ew
  rw [ev, el, eo, en, ea, ew]

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.raft.v3.Assumptions]

/-- A clone in `Equivalent`'s loop: before its iteration, owned holding `c`; after, owned holding
a sorted `c'` with its `AutoLeave` set. -/
def csStage (p : Loc) (c : ConfStateM) (done : Bool) : IProp GF :=
  if done then iprop(∃ c', csPts p (DFrac.own 1) c' true ∗ ⌜SortedOf c c'⌝)
  else ownCSM p (DFrac.own 1) c

theorem raftpb.ConfState.Equivalent.wp_proof
    (wp_proto_CloneConfState : proto.CloneConfState.spec (GF := GF) (hG := hG))
    (wp_slices_Sort : slices.«Sort».spec (GF := GF) (hG := hG))
    (wp_ConfState_GetAutoLeave : raftpb.ConfState.GetAutoLeave.spec (GF := GF) (hG := hG))
    (wp_proto_EqualConfState : proto.EqualConfState.spec (GF := GF) (hG := hG)) :
    raftpb.ConfState.Equivalent.spec (GF := GF) (hG := hG) := by
  intro p q c1 c2 dq1 dq2 Hperm Hbd Hal Hwe
  wp_start as ⟨H1, H2⟩
  ihave %Hp := (show ownCSM (GF := GF) p dq1 c1 ⊢ ⌜p ≠ null⌝ by
    iintro H; iNamed H; ipureintro; exact Hnn) $$ H1
  ihave %Hq := (show ownCSM (GF := GF) q dq2 c2 ⊢ ⌜q ≠ null⌝ by
    iintro H; iNamed H; ipureintro; exact Hnn) $$ H2
  wp_auto
  wp_if_destruct
  · exact absurd rfl Hp
  wp_if_destruct
  · exact absurd rfl Hq
  wp_apply wp_proto_CloneConfState.1 p dq1 c1 $$ [$H1] as %p1 ⟨H1, Hc1⟩
  wp_apply wp_proto_CloneConfState.1 q dq2 c2 $$ [$H2] as %p2 ⟨H2, Hc2⟩
  wp_apply wp_slice_literal (V := Loc) [p1, p2]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  have hsz : ∀ a b, go.arrayLiteralSize [KeyedElement none a, KeyedElement none b] = 2 :=
    fun _ _ => rfl
  simp only [hsz]
  wp_auto
  ihave HI : (∃ (i : w64), "i" ∷ i_ptr ↦ i ∗ "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ 2⌝ ∗
      "S1" ∷ csStage p1 c1 (decide (1 ≤ sint.Z i)) ∗ "S2" ∷ csStage p2 c2 (decide (2 ≤ sint.Z i)) ∗
      "c" ∷ (∃ v : Loc, c_ptr ↦ v) : IProp GF) $$ [i Hc1 Hc2 c]
  · iexists (W64 0)
    have h1 : decide (1 ≤ sint.Z (W64 0)) = false := by decide
    have h2 : decide (2 ≤ sint.Z (W64 0)) = false := by decide
    simp only [h1, h2, csStage, Bool.false_eq_true, ↓reduceIte]
    iframe
    isplitr
    · ipureintro; decide
    iexists _; iframe
  have Hbd2 : c2.lists.Bounded := by
    obtain ⟨h1, h2, h3, h4⟩ := Hperm
    obtain ⟨b1, b2, b3, b4⟩ := Hbd
    exact ⟨h1.length_eq ▸ b1, h2.length_eq ▸ b2, h3.length_eq ▸ b3, h4.length_eq ▸ b4⟩
  wp_for HI
  wp_if_destruct
  · -- an iteration: the clone at index `i`
    have Hin : 0 ≤ sint.Z i ∧ sint.Z i < sint.Z (W64 2) := ⟨Hi.1, Hif⟩
    have Hi01 : i = W64 0 ∨ i = W64 1 := by
      rcases Hi with ⟨h0, h2⟩
      have h22 : sint.Z (W64 2) = 2 := by decide
      have : sint.Z i < 2 := by rw [h22] at Hif; exact Hif
      have : sint.Z i = 0 ∨ sint.Z i = 1 := by omega
      rcases this with h | h
      · left; word
      · right; word
    ihave Hsel : (∃ (pc : Loc) (cc : ConfStateM),
        ⌜[p1, p2][sint.nat i]? = some pc ∧ cc.lists.Bounded⌝ ∗ ownCSM pc (DFrac.own 1) cc ∗
        ((∃ c', csPts pc (DFrac.own 1) c' true ∗ ⌜SortedOf cc c'⌝) -∗
          csStage p1 c1 (decide (1 ≤ sint.Z (i + W64 1))) ∗
          csStage p2 c2 (decide (2 ≤ sint.Z (i + W64 1)))) : IProp GF) $$ [S1 S2]
    · rcases Hi01 with rfl | rfl
      · have e1 : decide (1 ≤ sint.Z (W64 0)) = false := by decide
        have e2 : decide (2 ≤ sint.Z (W64 0)) = false := by decide
        have e3 : decide (1 ≤ sint.Z (W64 0 + W64 1)) = true := by decide
        have e4 : decide (2 ≤ sint.Z (W64 0 + W64 1)) = false := by decide
        simp only [e1, e2, e3, e4, csStage, Bool.false_eq_true, ↓reduceIte]
        iexists p1, c1
        iframe S1
        isplitr
        · ipureintro; exact ⟨rfl, Hbd⟩
        iintro Hd
        iframe
      · have e1 : decide (1 ≤ sint.Z (W64 1)) = true := by decide
        have e2 : decide (2 ≤ sint.Z (W64 1)) = false := by decide
        have e3 : decide (1 ≤ sint.Z (W64 1 + W64 1)) = true := by decide
        have e4 : decide (2 ≤ sint.Z (W64 1 + W64 1)) = true := by decide
        simp only [e1, e2, e3, e4, csStage, Bool.false_eq_true, ↓reduceIte]
        iexists p2, c2
        iframe S2
        isplitr
        · ipureintro; exact ⟨rfl, Hbd2⟩
        iintro Hd
        iframe
    icases Hsel with ⟨%pc, %cc, ⟨%Hlk, %Hbdc⟩, Hcs, Hback⟩
    icases c with ⟨%cv, c⟩
    iapply wp_fupd
    rw [ite_eq_left Hin]
    wp_apply wp_load_slice_index _ _ [p1, p2] _ pc Hin.1 $$ [$Hsl] as Hsl
    · ipureintro; exact Hlk
    obtain ⟨b1, b2, b3, b4⟩ := Hbdc
    simp only [ConfStateM.lists] at b1 b2 b3 b4
    iNamed Hcs
    wp_auto
    wp_apply wp_slices_Sort sv cc.Voters' $$ [$Hv] as %xs1 ⟨Hv, %Hp1, %Hs1⟩
    · ipureintro; omega
    wp_apply wp_slices_Sort sl cc.Learners' $$ [$Hl] as %xs2 ⟨Hl, %Hp2, %Hs2⟩
    · ipureintro; omega
    wp_apply wp_slices_Sort so cc.VotersOutgoing' $$ [$Ho] as %xs3 ⟨Ho, %Hp3, %Hs3⟩
    · ipureintro; omega
    wp_apply wp_slices_Sort sn cc.LearnersNext' $$ [$Hn] as %xs4 ⟨Hn, %Hp4, %Hs4⟩
    · ipureintro; omega
    -- the sorted clone, closed for `GetAutoLeave`
    ihave Hc' : csOpt (GF := GF) pc (DFrac.own 1) (ConfStateM.mk xs1 xs2 xs3 xs4 cc.AutoLeave' cc.Witness')
        $$ [HV Hv HL Hl HO Ho HN Hn HA HW HWO]
    · iunfold csOpt
      iright
      simp only [ownCSM]
      iunfold csPts
      iexists sv, sl, so, sn, pa, pw, pwo
      isplitr
      · ipureintro; exact Hnn
      iframe
      iframe cA cW cWO Hpb
      ipureintro; exact Hal
    wp_apply wp_ConfState_GetAutoLeave pc (DFrac.own 1) _ $$ [$Hc'] as Hc'
    iunfold csOpt at Hc'
    icases Hc' with (⟨%Hpn, -⟩ | Hc')
    · exact absurd Hpn Hnn
    simp only [ownCSM]
    iNamedSuffix Hc' "'"
    wp_auto
    ihave %Hqn := typedPointsto_not_null $$ autoLeave
    imod cellRO_alloc _ _ $$ autoLeave with #cq
    imodintro
    wp_for_post
    ihave Hd := Hback $$ [HV' Hv' HL' Hl' HO' Ho' HN' Hn' HA' HW' HWO']
    · iexists (ConfStateM.mk xs1 xs2 xs3 xs4 cc.AutoLeave' cc.Witness')
      isplitl
      · iunfold csPts
        iexists sv, sl, so, sn, autoLeave_ptr, pw, pwo
        isplitr
        · ipureintro; exact Hnn
        iframe
        iframe cq cW' cWO' Hpb'
        ipureintro; intro _; exact Hqn
      · ipureintro; exact ⟨⟨Hp1, Hp2, Hp3, Hp4⟩, Hs1, Hs2, Hs3, Hs4, rfl, rfl⟩
    icases Hd with ⟨S1, S2⟩
    iframe
    iexists (i + W64 1)
    iframe
    isplitr
    · ipureintro; rcases Hi01 with rfl | rfl <;> decide
    iexists pc; iframe
  · -- the loop is done: both clones sorted
    have Hi2 : i = W64 2 := by
      have h22 : sint.Z (W64 2) = 2 := by decide
      rw [h22] at Hif
      have : sint.Z i = 2 := by omega
      word
    subst Hi2
    have e1 : decide (1 ≤ sint.Z (W64 2)) = true := by decide
    have e2 : decide (2 ≤ sint.Z (W64 2)) = true := by decide
    rw [e1, e2]
    simp only [csStage, ↓reduceIte]
    icases S1 with ⟨%c1', S1, %Hs1⟩
    icases S2 with ⟨%c2', S2, %Hs2⟩
    wp_apply wp_proto_EqualConfState p1 p2 _ _ c1' c2' $$ [$S1 $S2] as %b ⟨S1, S2, %Hb⟩
    have Hbt : b = true := Hb.2 (sortedOf_eq Hperm Hal Hwe Hs1 Hs2)
    subst Hbt
    wp_auto
    iapply HΦ
    iframe

end proof

end EtcdGrove
end Perennial
