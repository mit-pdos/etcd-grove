/-
A writer's `Cursor.First` at any fraction (U6z, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): `wrCur_open`, `Assert` on the transaction's database, `first` (`first_w`: the cursor at
entry `0`), its result as `curAt` (`wEntKV_curAt`), and the cursor closed at entry `0`.
-/
module

public import Proof.go_etcd_io.bbolt.Read.PubWCur
public import Spec.go_etcd_io.bbolt.Cursor__first_w
public import Spec.go_etcd_io.bbolt.internal.common.Assert
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pubWFirst
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A writer's `First`** at any fraction, over `first_w` (`hD1`: `gensOK`'s third clause). -/
theorem Cursor.First.wp_writerW [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hfirst : Cursor.first_w.specQ (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hrw : T.rw = true)
    (hD1 : ∀ X : WX, gensOK T X →
      ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b)
 :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"First")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      boltCur tx γ c T es (some 0) ∗ curAt tx γ es 0 k v }} := by
  wp_start as ⟨Ht, Hc⟩
  unfold boltTx boltCur
  icases wrCur_open _ _ tx c q T es pos hrw hD1 $$ [Ht Hc] with
    ⟨%K, %r, %X, %n, %b, %stk, %els, %nl, %ipg, Hw, Hc, Hs, Hcap, #Hown, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨hctx, hes, hbrl, -⟩ := Hf
  icases wtxWQ_pkgInit K tx r true q X $$ Hw with ⟨Hw, #Hpkg⟩
  ihave #Hcom : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.internal.common $$ []
  · iPkgInit
  icases wtxWQ_heapOK K tx r true q X $$ Hw with ⟨Hw, %Hhok⟩
  obtain ⟨C, hC⟩ := PubW.bktLoc_rec X hctx.1 n b hctx.2.1
  icases wtxWQ_child_tx K tx r true q X b C hC hbrl Hhok $$ Hw with ⟨Hw, #Hbtx⟩
  icases wtxWQ_db_acc K tx r true q X $$ Hw with ⟨Hdb, %Hdbn, Hwdb⟩
  wp_auto
  rw [decide_eq_false Hdbn]
  simp only [Bool.not_false]
  wp_apply hA
  try wp_auto
  ihave Hw := Hwdb $$ Hdb
  have hand : ∀ f : w32, ¬ isBktFlag f → f &&& W32 1 = W32 0 := by
    intro f h; unfold isBktFlag at h; exact Classical.not_not.1 h
  wp_apply hfirst K tx r true q X n b (wRoot X.v T n) c stk els hctx $$ [Hw Hc Hs Hcap]
    as %k %vl %fl ⟨%stk', %els', %nl', %ipg', Hw, Hc, Hs, Hcap, #Hown', %Hcur, #Hkv⟩
  · iframe
  rw [← hes] at Hcur
  rw [← hes]
  icases wEntKV_curAt γ tx r X es 0 k vl fl $$ [Hkv] with ⟨#Hca, %Hfl⟩
  · iframe #
  try wp_auto
  rw [decide_eq_true (hand fl Hfl)]
  simp only [Bool.not_true]
  wp_auto
  iapply HΦ
  ihave Hfin := Hcl $$ %stk' %els' %nl' %ipg' %(some 0) Hw Hc Hs Hcap Hown'
  ihave Hfin := Hfin $$ []
  · ipureintro; exact Hcur
  icases Hfin with ⟨Ht, Hc⟩
  iframe; iframe #

end pubWFirst

end bbolt
end EtcdGrove
end Perennial
