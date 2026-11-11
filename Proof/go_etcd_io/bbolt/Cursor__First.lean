/-
The proof of `Spec/go_etcd_io/bbolt/Cursor__First.lean` (U6h, `notes/bbolt-proof-plan.md`).
A reader (`wp_reader`): `first` (`Cursor.first_r`); its result at entry `0` is the cursor's
position (`rCurKV_first_pos`'s reasoning) and the public `curAt` (`rCurKV_pub`; a top-level
bucket's entries are plain). A writer (`wp_writer`): U6w's.
-/
module

public import Spec.go_etcd_io.bbolt.Cursor__First
public import Spec.go_etcd_io.bbolt.Cursor__first_r
public import Spec.go_etcd_io.bbolt.internal.common.Assert
public import Proof.go_etcd_io.bbolt.Read.PubR
public import Proof.go_etcd_io.bbolt.Read.PubWFirst
public import Proof.go_etcd_io.bbolt.Bucket__Get
public import Proof.go_etcd_io.bbolt.Txn.RdInit
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Cursor.First.wp_reader [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hfirst : Cursor.first_r.spec (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"First")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      boltCur tx γ c T es (some 0) ∗ curAt tx γ es 0 k v }} := by
  wp_start as ⟨Ht, Hc⟩
  unfold boltTx boltCur
  icases rdCur_open _ _ tx c q T es pos hro $$ [Ht Hc] with
    ⟨%K, %v, %r, %b, %stk, %els, %bv, %ibp, %pp, Hk, #Hb, Hc, Hs, Hcap, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨-, hfacts, -⟩ := Hf
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
  wp_apply hfirst K tx .loan q T v b DFrac.discard bv ibp pp c stk els hfacts.2.1
    $$ [Hk Hc Hs Hcap] as %k %vl %fl ⟨%stk', %els', %vl', Hk, -, Hc, Hs, Hcap, Hcur, %Hvl⟩
  · iframe; unfold rBktP; iframe #
  icases rCurKV_pub γ tx r v bv pp els' 0 k vl' fl es hfacts $$ [Hcur] with ⟨#Hca, %Hfp⟩
  · iframe #; iexact Hcur
  obtain ⟨hfl, hp⟩ := Hfp
  have hvl := Hvl hfl
  subst hvl
  have hcp : rCurPos v bv pp els' (some 0) := by
    rcases hp with h | ⟨hl, i, hi⟩
    · exact Or.inl ⟨1, h, fun h => by omega⟩
    · rcases rPosAt_s hi with h | h
      · subst h; exact Or.inl ⟨0, hi, fun _ => by omega⟩
      · omega
  try wp_auto
  rw [decide_eq_true hfl]
  simp only [Bool.not_true]
  wp_auto
  iapply HΦ
  ihave Hfin := Hcl $$ Hk Hc Hs Hcap
  ihave Hfin := Hfin $$ []
  · ipureintro; exact hcp
  icases Hfin with ⟨Ht, Hc⟩
  iframe; iframe #

/-- **A writer's `First`** (U6z): `Read/PubWFirst`'s, over `first_w`; `gensOK`'s third clause by
`gensOK_handle_bktLoc` (the cursor's writer facts are `wtxFrac`'s). -/
theorem Cursor.First.wp_writer [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hfw : Cursor.first_w.specQ (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"First")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      boltCur tx γ c T es (some 0) ∗ curAt tx γ es 0 k v }} :=
  Cursor.First.wp_writerW hA hfw tx c γ q T es pos hrw (gensOK_handle_bktLoc T)

theorem Cursor.First.wp_proof
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hfirst : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Cursor.first_r.spec (GF := GF) (hG := hG))
    (hfw : ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt], Cursor.first_w.specQ (GF := GF) (hG := hG)) :
    Cursor.First.spec (GF := GF) (hG := hG) := by
  intro _ tx c γ q T es pos
  by_cases hrw : T.rw = true
  · exact Cursor.First.wp_writer hA hfw tx c γ q T es pos hrw
  · exact Cursor.First.wp_reader hA hfirst tx c γ q T es pos (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
