/-
A writer's `Cursor.Next` at any fraction (U6z, `notes/bbolt-proof-plan.md`, "Writer reads at a
fraction"): `wrCur_open`, `Assert` on the transaction's database, then `next` (`next_w` on an entry,
`next_we` unpositioned or at the end), its result as `curAt` (`wEntKV_curAt`), and the cursor closed
at the position the frozen triple names.
-/
module

public import Proof.go_etcd_io.bbolt.Read.PubWCur
public import Spec.go_etcd_io.bbolt.Cursor__next_w
public import Spec.go_etcd_io.bbolt.internal.common.Assert
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section pubWNext
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- **A writer's `Next`** at any fraction, over `next_w`/`next_we` (`hD1`: `gensOK`'s third clause;). -/
theorem Cursor.Next.wp_writerW [HasExt osFsExt]
    (hA : internal.common.Assert.spec (GF := GF) (hG := hG))
    (hnx : Cursor.next_w.specQ (GF := GF) (hG := hG))
    (hnxe : Cursor.next_we.specQ (GF := GF) (hG := hG))
    (tx c : Loc) (γ : BoltName) (q : Qp) (T : TxView) (es : List BoltEnt) (pos : Option Nat)
    (hrw : T.rw = true)
    (hD1 : ∀ X : WX, gensOK T X →
      ∀ b n, X.handles !! b = some (n, T.gen n) → bktLoc X n = some b)
 :
  {{ boltTx (GF := GF) tx γ q T ∗ boltCur tx γ c T es pos }}
    (App (Val (c @!! go.GoType.PointerType Cursor.ty @!! go!"Next")) (Val #()))
  {{ (k v : GoSlice), RET (PairV #k #v); boltTx tx γ q T ∗
      (match pos with
       | none => iprop(boltCur tx γ c T es none ∗ ⌜k = slice.nil ∧ v = slice.nil⌝)
       | some i => iprop(boltCur tx γ c T es (some (if i + 1 < es.length then i + 1 else i)) ∗
           curAt tx γ es (i + 1) k v)) }} := by
  wp_start as ⟨Ht, Hc⟩
  unfold boltTx boltCur
  icases wrCur_open _ _ tx c q T es pos hrw hD1 $$ [Ht Hc] with
    ⟨%K, %r, %X, %n, %b, %stk, %els, %nl, %ipg, Hw, Hc, Hs, Hcap, #Hown, #Hreg, #Hvo, %Hf, Hcl⟩
  · iframe
  obtain ⟨hctx, hes, hbrl, hpos⟩ := Hf
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
  cases pos with
  | none =>
    have hel : els = [] := hpos
    wp_apply hnxe K tx r true q X n b (wRoot X.v T n) ipg nl c stk els [] hctx (Or.inl hel)
      $$ [Hw Hc Hs] as ⟨Hw, Hc, Hs, -⟩
    · iframe; iframe #
    try wp_auto
    try rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
    try simp only [Bool.not_true]
    try wp_auto
    iapply HΦ
    ihave Hfin := Hcl $$ %stk %els %nl %ipg %none Hw Hc Hs Hcap Hown
    ihave Hfin := Hfin $$ []
    · ipureintro; exact hel
    icases Hfin with ⟨Ht, Hc⟩
    iframe
    ipureintro; exact ⟨rfl, rfl⟩
  | some i =>
    obtain ⟨pids, hp, hlf, hst⟩ := hpos
    rcases hst with ⟨hli, hi⟩ | ⟨hend, hie⟩
    · -- on an entry: `next` to `i + 1`
      have hlt := stackPos_lt X.v es pids els hli
      have hstk : wStk nl X.v (wEs X n) b (wRoot X.v T n) ipg els pids := by
        rw [← hes]; exact ⟨hp, hlf, Nat.le_of_lt hli⟩
      have hto : wNextTo X.v (wEs X n) pids els = i + 1 := by
        unfold wNextTo; rw [← hes, if_pos hli, hi]
      wp_apply hnx K tx r true q X n b (wRoot X.v T n) ipg nl c stk els pids hctx hstk
        $$ [Hw Hc Hs Hcap] as %k %vl %fl ⟨%stk', %els', %nl', Hw, Hc, Hs, Hcap, #Hown', %Hpost, #Hkv⟩
      · iframe; iframe #
      rw [hto, ← hes] at Hpost
      rw [hto, ← hes]
      icases wEntKV_curAt γ tx r X es (i + 1) k vl fl $$ [Hkv] with ⟨#Hca, %Hfl⟩
      · iframe #
      try wp_auto
      rw [decide_eq_true (hand fl Hfl)]
      simp only [Bool.not_true]
      wp_auto
      iapply HΦ
      obtain ⟨pids', hp', hlf', hcase⟩ := Hpost
      rcases hcase with ⟨hlt', hli', hst'⟩ | ⟨hge, hcase⟩
      · simp only [hlt', ite_true]
        ihave Hfin := Hcl $$ %stk' %els' %nl' %ipg %(some (i + 1)) Hw Hc Hs Hcap Hown'
        ihave Hfin := Hfin $$ []
        · ipureintro; exact ⟨pids', hp', hlf', Or.inl ⟨hli', hst'.symm⟩⟩
        icases Hfin with ⟨Ht, Hc⟩
        iframe; iframe #
      · have hnlt : ¬ i + 1 < es.length := by omega
        simp only [hnlt, ite_false]
        ihave Hfin := Hcl $$ %stk' %els' %nl' %ipg %(some i) Hw Hc Hs Hcap Hown'
        ihave Hfin := Hfin $$ []
        · ipureintro
          rcases hcase with ⟨he1, he2, -⟩ | hend'
          · subst he1 he2; exact ⟨_, hp', hlf', Or.inl ⟨hli, hi⟩⟩
          · exact ⟨pids', hp', hlf', Or.inr ⟨hend', Or.inr (by omega)⟩⟩
        icases Hfin with ⟨Ht, Hc⟩
        iframe; iframe #
    · -- at the end: nothing moves
      have hend' : wEndAt X.v (wEs X n) pids els := by rw [← hes]; exact hend
      have hlf2 : sLeafOK X.v ipg (wEs X n) pids els := by rw [← hes]; exact hlf
      wp_apply hnxe K tx r true q X n b (wRoot X.v T n) ipg nl c stk els pids hctx
        (Or.inr ⟨hp, hlf2, hend'⟩) $$ [Hw Hc Hs] as ⟨Hw, Hc, Hs, -⟩
      · iframe; iframe #
      try wp_auto
      try rw [decide_eq_true (show (W32 0 : w32) &&& W32 1 = W32 0 by decide)]
      try simp only [Bool.not_true]
      try wp_auto
      iapply HΦ
      have hnlt : ¬ i + 1 < es.length := by omega
      simp only [hnlt, ite_false]
      ihave Hfin := Hcl $$ %stk %els %nl %ipg %(some i) Hw Hc Hs Hcap Hown
      ihave Hfin := Hfin $$ []
      · ipureintro; exact ⟨pids, hp, hlf, Or.inr ⟨hend, hie⟩⟩
      icases Hfin with ⟨Ht, Hc⟩
      iframe
      unfold curAt
      rw [List.getElem?_eq_none (by omega)]
      ipureintro; exact ⟨rfl, rfl⟩

end pubWNext

end bbolt
end EtcdGrove
end Perennial
