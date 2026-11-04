/-
The proof of `Spec/go_etcd_io/bbolt/Bucket__Cursor.lean` (U6g, `notes/bbolt-proof-plan.md`): the
internal `Bucket.Cursor_i` with the statistics token of the transaction's fraction (its `ex` share)
and the handle's `tx` field (`boltBkt`'s); the new cursor's empty stack is unpositioned, over the
handle's registration and the transaction's view (a writer's `wtxFrac`, a reader's `rdTxK`).
-/
module

public import Spec.go_etcd_io.bbolt.Bucket__Cursor
public import Spec.go_etcd_io.bbolt.Bucket__Cursor_i
public import Proof.go_etcd_io.bbolt.Read.Pub
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

theorem Bucket.Cursor.wp_proof (hcur : ∀ [HasExt osFsExt], Bucket.Cursor_i.spec (GF := GF) (hG := hG)) :
    Bucket.Cursor.spec (GF := GF) (hG := hG) := by
  intro _ tx γ q T b n m
  iintro %Φ ⟨Ht, #Hb, %Hm⟩ HΦ
  unfold boltTx boltBkt boltCur boltTxDef boltBktDef boltCurDef at *
  icases Hb with ⟨%r', #Hreg', #Hbtx, #Hh, Hrb⟩
  split
  · rename_i hrw
    icases Ht with ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #HbP, Hv, Hex, Hw⟩
    iunfold reg at Hreg Hreg'
    icombine Hreg Hreg' gives %hr
    obtain ⟨-, rfl⟩ := hr
    ihave #Hcore : BC.core (GF := GF) ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ $$ []
    · unfold BC.core; unfold isBoltP; icases HbP with ⟨$, -⟩
    iapply hcur ⟨bnsOf γ.gs, γ.ns, db, p, sp, t0⟩ tx r true q b DFrac.discard $$ [Hex]
    · unfold statsTok; simp only [ite_true]; iframe; iframe #; unfold reg; iframe #
    inext
    iintro %cur ⟨%stk, Hc, Hs, Hcap, Hex, -⟩
    unfold wtxFrac
    icases Hw with ⟨Hh0, Hf, Hvc, Hst, Hbk, Hnl, Hdb, Hmf, #Hvo, %Hfacts⟩
    iapply HΦ
    unfold statsTok
    simp only [ite_true]
    isplitl [Hv Hex Hh0 Hf Hvc Hst Hbk Hnl Hdb Hmf]
    · iexists db, p, sp, t0, r, c, X
      unfold reg
      iframe; iframe #
      ipureintro; exact ⟨Hc, Hfacts⟩
    iexists r, b, n, (T.gen n), stk, [], X.v
    unfold reg
    iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [Hm]; rfl, rfl⟩
    simp only [Hc.2.2, ite_true]
    iexists (fun _ => none)
    isplitr
    · iempintro
    ipureintro; trivial
  · rename_i hrw
    icases Ht with ⟨%db, Hr, #Hdb⟩
    ihave Hr := (rdTx_rdTxK _ _ tx .loan q T).1 $$ Hr
    icases Hr with ⟨%K, %v, %HK, Hk⟩
    obtain ⟨KB, KN, Kdb, Kp, Ksp, Kt0⟩ := K
    obtain ⟨hKB, hKN⟩ := HK
    simp only at hKB hKN
    subst hKB hKN
    icases rdTxK_cur_acc _ tx .loan q T v $$ Hk with ⟨%r, #Hcore, #Hreg, #Hvo, %Hro, Hst, Hkb⟩
    iunfold reg at Hreg Hreg'
    icombine Hreg Hreg' gives %hr
    obtain ⟨-, rfl⟩ := hr
    iapply hcur _ tx r true q b DFrac.discard $$ [Hst]
    · iframe; iframe #; unfold reg; iframe #
    inext
    iintro %cur ⟨%stk, Hc, Hs, Hcap, Hst, -⟩
    ihave Hk := Hkb $$ Hst
    iapply HΦ
    isplitl [Hk]
    · iexists db
      iframe; iframe #
      iapply (rdTx_rdTxK _ _ tx .loan q T).2
      iexists _, v
      iframe
      ipureintro; exact ⟨rfl, rfl⟩
    iexists r, b, n, (T.gen n), stk, [], v
    unfold reg
    iframe; iframe #
    isplitr
    · ipureintro; exact ⟨by rw [Hm]; rfl, rfl⟩
    simp only [Hro, Bool.false_eq_true, ite_false]
    ipureintro
    exact ⟨trivial, fun e he => by simp at he⟩

end proof

end bbolt
end EtcdGrove
end Perennial
