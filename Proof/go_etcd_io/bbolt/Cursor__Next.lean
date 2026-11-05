/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__Next.lean` (U6h, U6i, `notes/bbolt-proof-plan.md`):
split on `T.rw`. A reader (`wp_reader`): `next` (`Cursor.next_r`, or `Cursor.next_r0` unpositioned
or on the empty root leaf); its result at the position's target is the public `curAt`
(`rCurKV_pub`), the cursor at the next entry, or unchanged past the last (`next_r`'s post). A
writer (`wp_writer`): U6w's.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__Next
public import Spec.go_etcd_io.bbolt.Cursor__next_r0
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Read.PubR
public import Proof.go_etcd_io.bbolt.Read.PubWNext
public import Proof.go_etcd_io.bbolt.Bucket__Get
public import Proof.go_etcd_io.bbolt.Txn.RdInit
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A reader's `Next`.** -/
theorem Cursor.Next.wp_reader [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hnx : Cursor.next_r.spec (GF := GF) (hG := hG))
    (hnx0 : Cursor.next_r0.spec (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c T es none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some i => iprop(boltCur tx γ c T es (some (if i + 1 < es.length then i + 1 else i)) ∗
           curAt tx γ es (i + 1) k v)) }} := by
  wp_start as ⟨Ht, Hc⟩
  unfold boltTx boltCur
  icases rdCur_open _ _ tx c q T es pos hro $$ [Ht Hc] with
    ⟨%K, %v, %r, %b, %stk, %els, %bv, %ibp, %pp, Hk, #Hb, Hc, Hs, Hcap, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨-, hfacts, hpos⟩ := Hf
  have hlen : es.length = (rEnts v bv).length := by rw [hfacts.2.2.1, rEnts_length]
  ihave #Hpkg := (rdTxK_pkgInit _ tx .loan q T v) $$ Hk
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases rdTxK_flags_acc K tx .loan q T v $$ Hk with ⟨Hmg, Hdb, Hw, -, %Hdbn, Hkcl⟩
  unfold rBktP
  icases Hb with ⟨#HIB, #Htx, #Hbks, #Hpage, #Hroot, #Hnodes, #Hhdr, #Hil⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  simp only [Bool.not_false]
  wp_apply hA
  try wp_auto
  ihave Hk := Hkcl $$ Hmg Hdb Hw
  cases pos with
  | none =>
    have hel : els = [] := hpos
    wp_apply hnx0 K tx .loan q T v b DFrac.discard bv ibp pp c stk els hfacts.2.1 (Or.inl hel)
      $$ [Hk Hc Hs Hcap] as ⟨Hk, -, Hc, Hs, Hcap⟩
    · iframe; unfold rBktP; iframe #
    try wp_auto
    try rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
    try simp only [Bool.not_true]
    try wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk %els %none Hk Hc Hs Hcap
    ihave Hfin := Hfin $$ []
    · ipureintro; exact hel
    icases Hfin with ⟨Ht, Hc⟩
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  | some i =>
    rcases hpos with ⟨s, hp, hsi⟩ | ⟨hi0, hemp⟩
    · wp_apply hnx K tx .loan q T v b DFrac.discard bv ibp pp c stk els i s hfacts.2.1 hp
        $$ [Hk Hc Hs Hcap] as %k %vl %fl ⟨%stk', %els', Hk, -, Hc, Hs, Hcap, Hcur, -, %Hsame⟩
      · iframe; unfold rBktP; iframe #
      icases rCurKV_pub γ tx r v bv pp els' s k vl fl es hfacts $$ [Hcur] with ⟨#Hca, %Hfp⟩
      · iframe #; iexact Hcur
      obtain ⟨hfl, hp'⟩ := Hfp
      try wp_auto
      rw [decide_eq_true hfl]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      rcases rPosAt_s hp with hs | hs
      · -- past the last entry: unchanged
        subst hs
        have hle := hsi rfl
        have he := Hsame hle
        subst he
        have hif : ¬ s + 1 < es.length := by omega
        simp only [hif, ite_false]
        ihave Hfin := Hcl $$ %stk' %els' %(some s) Hk Hc Hs Hcap
        ihave Hfin := Hfin $$ []
        · ipureintro; exact Or.inl ⟨s, hp, hsi⟩
        icases Hfin with ⟨Ht, Hc⟩
        iframe
        iapply curAt_past γ tx es s (s + 1) k vl (by omega) (by omega)
        iexact Hca
      · subst hs
        by_cases hlt : i + 1 < es.length
        · simp only [hlt, ite_true]
          have hp2 : rPosAt v bv pp els' (i + 1) (i + 1 + 1) := by
            rcases hp' with h | ⟨h, -⟩
            · exact h
            · omega
          ihave Hfin := Hcl $$ %stk' %els' %(some (i + 1)) Hk Hc Hs Hcap
          ihave Hfin := Hfin $$ []
          · ipureintro; exact Or.inl ⟨_, hp2, fun h => by omega⟩
          icases Hfin with ⟨Ht, Hc⟩
          iframe; iframe #
        · simp only [hlt, ite_false]
          have he := Hsame (by omega)
          subst he
          ihave Hfin := Hcl $$ %stk' %els' %(some i) Hk Hc Hs Hcap
          ihave Hfin := Hfin $$ []
          · ipureintro; exact Or.inl ⟨_, hp, hsi⟩
          icases Hfin with ⟨Ht, Hc⟩
          iframe; iframe #
    · subst hi0
      have hes0 : es.length = 0 := by rw [hlen, hemp.1]; rfl
      wp_apply hnx0 K tx .loan q T v b DFrac.discard bv ibp pp c stk els hfacts.2.1 (Or.inr hemp)
        $$ [Hk Hc Hs Hcap] as ⟨Hk, -, Hc, Hs, Hcap⟩
      · iframe; unfold rBktP; iframe #
      try wp_auto
      try rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
      try simp only [Bool.not_true]
      try wp_auto
      iapply HΦ
      have hif : ¬ 0 + 1 < es.length := by omega
      simp only [hif, ite_false]
      ihave Hfin := Hcl $$ %stk %els %(some 0) Hk Hc Hs Hcap
      ihave Hfin := Hfin $$ []
      · ipureintro; exact Or.inr ⟨rfl, hemp⟩
      icases Hfin with ⟨Ht, Hc⟩
      iframe
      unfold curAt
      rw [List.getElem?_eq_none (by omega)]
      ipureintro; exact ⟨rfl, rfl⟩

/-- **A writer's `Next`** (U6z): `Read/PubWNext`'s, over `next_w`/`next_we`; `gensOK`'s third
clause by `gensOK_handle_bktLoc` and the cursor's writer facts by `wrCurFacts_of` (both OPEN). -/
theorem Cursor.Next.wp_writer [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hnxw : Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hnxe : Cursor.next_we.specQ (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c T es none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some i => iprop(boltCur tx γ c T es (some (if i + 1 < es.length then i + 1 else i)) ∗
           curAt tx γ es (i + 1) k v)) }} :=
  Cursor.Next.wp_writerW hA hnxw hnxe tx c γ q T es pos hrw (gensOK_handle_bktLoc T)
    (fun X hok hg hwr hcur hbase => wrCurFacts_of T X hok hg hwr hcur hbase)

theorem Cursor.Next.wp_proof
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hnx : ∀ [HasExt osFsExt], Cursor.next_r.spec (GF := GF) (hG := hG))
    (hnx0 : ∀ [HasExt osFsExt], Cursor.next_r0.spec (GF := GF) (hG := hG))
    (hnxw : ∀ [HasExt osFsExt], Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hnxe : ∀ [HasExt osFsExt], Cursor.next_we.specQ (GF := GF) (hG := hG)) :
    Cursor.Next.spec (GF := GF) (hG := hG) := by
  intro _ tx c γ q T es pos
  by_cases hrw : T.rw = true
  · exact Cursor.Next.wp_writer hA hnxw hnxe tx c γ q T es pos hrw
  · exact Cursor.Next.wp_reader hA hnx hnx0 tx c γ q T es pos (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
