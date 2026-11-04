/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Bucket.lean` (U6g, `notes/bbolt-proof-plan.md`).
A reader (`wp_reader`): half of its `rdTxK` beside half of its root bucket (`rdTxK_root_split`),
`tx.root.Bucket(name)` by `Bucket.Bucket_r.specK` (the name caller-owned); a miss is no bucket of
the view's data (`rd_root_lookup_none`), a hit is one (`rd_root_lookup_some`) whose handle is the
opened child, over `RdHandleMint` (the handle's registry fragment; OPEN, reported). A writer
(`wp_writer`): OPEN, `Bucket.Bucket_w.spec` takes the name as `srcOwn` (persistent) and gives no
handle fragment.
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Bucket
public import Proof.go_etcd_io.bbolt.Bucket__Bucket_r
public import Proof.go_etcd_io.bbolt.Read.Pub
public import Proof.go_etcd_io.bbolt.Read.GetFacts
public import Proof.go_etcd_io.bbolt.Commit.CheckSplit
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

theorem Tx.Bucket.wp_reader [HasExt osFsExt] (hmint : RdHandleMint (GF := GF))
    (hBr : Bucket.Bucket_r.specK (GF := GF) (hG := hG))
    (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (name : GoSlice) (n : GoString) (dq : DFrac)
    (hro : T.rw = false) :
  {{ boltTx (GF := GF) tx γ q T ∗ name ↦*{dq} n ∗ ⌜T.rw = true → q = 1⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; boltTx tx γ q T ∗ name ↦*{dq} n ∗
      ((⌜T.cur.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜T.cur.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ boltBkt tx γ b n (T.gen n))) }} := by
  wp_start as ⟨Ht, Hname, -⟩
  unfold boltTx boltBkt at *
  ihave Ht := (boltTx_rdTx _ _ tx q T hro).1 $$ Ht
  icases Ht with ⟨%db, Hr, #Hdb⟩
  ihave Hr := (rdTx_rdTxK _ _ tx .loan q T).1 $$ Hr
  icases Hr with ⟨%K, %v, %HK, Hk⟩
  obtain ⟨KB, KN, Kdb, Kp, Ksp, Kt0⟩ := K
  obtain ⟨hKB, hKN⟩ := HK
  simp only at hKB hKN
  subst hKB hKN
  icases (persistent_entails_left (rdTxK_view _ tx .loan q T v)) $$ Hk with ⟨Hk, %Hvw⟩
  obtain ⟨hT, hvwf⟩ := Hvw
  icases rdTxK_cur_acc _ tx .loan q T v $$ Hk with ⟨%r, #Hcore, #Hreg, #Hvo, %Hro, Hst, Hkb⟩
  ihave Hk := Hkb $$ Hst
  icases rdTxK_root_split _ tx .loan q T v $$ Hk with ⟨%ibp, %pp, Hk, Hrb, Hback⟩
  wp_auto
  rw [show tx.[Tx, go!"root"] = txRoot (GF := GF) tx from rfl]
  wp_apply hBr _ tx .loan q.half T v (txRoot (GF := GF) tx) (DFrac.own q.half) (rootVal v) ibp pp
    name (KeyR.heap dq) n (Or.inl rfl) $$ [Hk Hrb Hname] as %c ⟨Hk, Hrb, Hname, Hres⟩
  · unfold keyR; iframe
  ihave Hk := Hback $$ Hk Hrb
  simp only [keyR]
  icases Hres with (⟨%hc0, %hnn⟩ | ⟨%cv, ⟨%hcn, %hbe⟩, #Hcb⟩)
  · iapply HΦ
    isplitl [Hk]
    · iapply (boltTx_rdTx _ _ tx q T hro).2
      iexists db; iframe #
      iapply (rdTx_rdTxK _ _ tx .loan q T).2
      iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
    iframe Hname
    ileft; ipureintro
    exact ⟨by rw [hT]; exact rd_root_lookup_none v hvwf n hnn, hc0⟩
  · ihave Hh := hmint _ _ db tx c r n Hro $$ [Hdb Hreg]
    · iframe #
    iapply HΦ
    isplitl [Hk]
    · iapply (boltTx_rdTx _ _ tx q T hro).2
      iexists db; iframe #
      iapply (rdTx_rdTxK _ _ tx .loan q T).2
      iexists _, v; iframe; ipureintro; exact ⟨rfl, rfl⟩
    iframe Hname
    iright
    isplitr
    · ipureintro
      exact ⟨by rw [hT]; exact rd_root_lookup_some v hvwf n cv hbe, hcn⟩
    unfold boltBktDef
    iexists r
    iframe #
    have hg : T.gen n = 0 := by rw [hT]; rfl
    rw [hg]
    iframe #
    iframe Hh
    isplitr
    · unfold rBkt; icases Hcb with ⟨%ibp', %pp', #HIB, #Htx, -⟩; iexact Htx
    simp only [Hro, Bool.false_eq_true, ite_false]
    iexists v, cv
    iframe #
    ipureintro; exact hbe

/-- **A writer's `Tx.Bucket`** (all of the transaction): OPEN. `Bucket.Bucket_w.spec` takes the
name as `srcOwn X.v name ks nb` (persistent bytes or the view's), and the caller's name is
`name ↦*{dq} n`; and its post gives no persistent handle fragment `c ↪[r.n.bk]□ (n, g)`, which
`boltBktDef` needs (for a cached child, nothing in `wtxW` keeps the existing handles' fragments). -/
theorem Tx.Bucket.wp_writer [HasExt osFsExt]
    (tx : Loc) (γ : BoltName) (q : Qp) (T : TxView) (name : GoSlice) (n : GoString) (dq : DFrac)
    (hrw : T.rw = true) :
  {{ boltTx (GF := GF) tx γ q T ∗ name ↦*{dq} n ∗ ⌜T.rw = true → q = 1⌝ }}
    (App (Val (tx @!! go.GoType.PointerType Tx.ty @!! go!"Bucket")) (Val #name))
  {{ (b : Loc), RET #b; boltTx tx γ q T ∗ name ↦*{dq} n ∗
      ((⌜T.cur.lookup n = none ∧ b = Loc.null⌝) ∨
       (⌜T.cur.lookup n ≠ none ∧ b ≠ Loc.null⌝ ∗ boltBkt tx γ b n (T.gen n))) }} := by
  sorry

theorem Tx.Bucket.wp_proof (hBr : ∀ [HasExt osFsExt], Bucket.Bucket_r.specK (GF := GF) (hG := hG)) :
    Tx.Bucket.spec (GF := GF) (hG := hG) := by
  intro _ tx γ q T name n dq
  by_cases hrw : T.rw = true
  · exact Tx.Bucket.wp_writer tx γ q T name n dq hrw
  · exact Tx.Bucket.wp_reader rdHandleMint_holds hBr tx γ q T name n dq (Bool.eq_false_iff.2 hrw)

end proof

end bbolt
end EtcdGrove
end Perennial
