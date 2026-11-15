/-
The proof of `Spec/go_etcd_io/bbolt/Tx__Writable.lean`: a live transaction holds a share of its
`writable` field, `true` for the writer (`txClean`, through `wOK`), `false` for a reader (`rtxFrac`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__Writable
public import Proof.go_etcd_io.bbolt.Inv.Tx
import all Spec.go_etcd_io.bbolt.Api

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Fs

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

private instance reg_persistent_w (tx : Loc) (B : BNs) (r : TxReg) :
    Persistent (reg (GF := GF) tx B r) := by
  unfold reg; infer_instance

private instance isBoltP_persistent_w [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt] (B : BNs)
    (N : Namespace) (db : Loc) (p : BFile) (sp : Loc) (t0 : Nat) :
    Persistent (isBoltP (GF := GF) B N db p sp t0) := by
  unfold isBoltP; infer_instance

theorem Tx.Writable.wp_proof : Tx.Writable.spec (GF := GF) (hG := hG) := by
  intro _ _ _ tx γ q T
  wp_start as Ht
  unfold boltTx boltTxDef
  split
  · rename_i hrw
    icases Ht with ⟨%db, %p, %sp, %t0, %r, %c, %X, %Hc, #Hreg, #Hb, Hv, Hex, Hw⟩
    unfold wtxFrac wtxHeap txFields
    icases Hw with ⟨⟨%Hho, ⟨Hwr, Hf⟩, Hh⟩, Hrest⟩
    wp_auto
    icases Hrest with ⟨Hfl, Hvc, Hst, Hha, Hnl, Hdb, Hmf, Hvw, %Hok⟩
    have hw : X.t.t.writable' = T.rw := by rw [hrw]; exact Hok.1.1.1
    rw [hw]
    iapply HΦ
    iexists db, p, sp, t0, r, c, X
    iframe Hreg Hb Hv Hex
    isplitr
    · ipureintro; exact Hc
    try rw [hw]
    iframe Hfl Hvc Hst Hha Hnl Hdb Hmf Hvw Hwr Hf Hh
    ipureintro; exact ⟨Hho, Hok⟩
  · rename_i hrw
    have hf : T.rw = false := by simpa using hrw
    icases Ht with ⟨%db', Hr, #Hb'⟩
    unfold rdTx rtxFrac
    icases Hr with ⟨%db, %p, %sp, %t0, %r, %c, %v, %mv, %k, %Hc, #Hreg, #Hcore, Hv, Hex,
      ⟨%t, Hw, Hrest⟩, Hpool⟩
    wp_auto
    rw [hf]
    iapply HΦ
    iexists db'
    iframe Hb'
    iexists db, p, sp, t0, r, c, v, mv, k
    iframe Hreg Hcore Hv Hex Hpool
    isplitr
    · ipureintro; exact Hc
    iexists t
    iframe Hw Hrest

end proof

end bbolt
end EtcdGrove
end Perennial
