/-
The proof of `Spec/go_etcd_io/bbolt/Tx__page_r.lean` (U6, `notes/bbolt-proof-plan.md`): U4's
`Tx.page` over the reader's fields (`tx.pages` nil, `tx.db` and the mapping at `QpMul q ½`), its
view's cells and the view's page facts (`Read.viewWF_page`).
-/
module

public import Spec.go_etcd_io.bbolt.Tx__page_r
public import Spec.go_etcd_io.bbolt.Tx__page
public import Proof.go_etcd_io.bbolt.Read.Base
public import Proof.go_etcd_io.bbolt.Read.TreeFacts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt go_etcd_io.bbolt.internal.common

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable [hos : HasExt osFsExt]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- PENDING a shared fix: the mapping's base is not null (`DB.page` indexes `db.data`).
`mapFields`' mapped case does not say it yet (`notes/bbolt-proof-plan.md`). -/
private theorem mapFields_base_nonnull (db : Loc) (dq : DFrac) (b : Loc) (l : Nat) :
    mapFields (GF := GF) db dq (some (b, l)) ⊢ ⌜b ≠ null⌝ := by
  sorry

theorem Tx.page_r.wp_proof (hpage : Tx.page.spec (GF := GF) (hG := hG)) :
    Tx.page_r.spec (GF := GF) (hG := hG) := by
  intro K tx src q T v id pg hpg
  unfold rdTxK rtxFrac BC.core
  iintro %Φ ⟨%r, %c, %mv, %k, %Hc, #Hreg, #Hpk, #Hcore, Hv, Hex,
    ⟨%t, Hw, Hm, Hmeta, Hroot, Hfill, Hpages, Hch, Hwf, Hdb, Hmv, Hcells,
      ⟨%l, Hmap, Hmf, %Hl⟩, #Hvo, %Hf⟩, Hpool⟩ HΦ
  obtain ⟨hT, hvwf, hmv, hpn⟩ := Hf
  obtain ⟨h2, hid, hlen, hfl⟩ := Read.viewWF_page v hvwf id.toNat pg hpg
  have hbound := Hl id.toNat pg hpg
  ihave #Hps := isBoltCoreP_pageSize _ _ _ _ _ _ $$ Hcore
  ihave %Hnn := mapFields_base_nonnull _ _ _ _ $$ Hmf
  simp only [mapFields]
  icases Hmf with ⟨Hdref, Hdata, Hm0, Hm1, %Hlen⟩
  icases viewCells_page_acc _ v id.toNat pg hpg $$ Hcells with ⟨Hpg, Hcells⟩
  have Hsp := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"pages"]) t.pages'
    (QpMul q (1 : Qp).half) (QpMul q (1 : Qp).half)
  rw [qpMul_half_add] at Hsp
  icases Hsp.1 $$ Hpages with ⟨Hp1, Hp2⟩
  have Hsd := typedPointsto_frac_add (GF := GF) (tx.[Tx, go!"db"]) r.db
    (QpMul q (1 : Qp).half) (QpMul q (1 : Qp).half.half)
  rw [← txDbQ_eq] at Hsd
  icases Hsd.1 $$ Hdb with ⟨Hd1, Hd2⟩
  rw [hpn] at Hsp ⊢
  rw [Hc.2.1] at Hsd ⊢
  wp_apply (hpage tx K.db null ∅ v.base id (pageLoc v id.toNat) pg
    (DFrac.own (QpMul q (1 : Qp).half)) (DFrac.own 1)
    (DFrac.own (QpMul q sync.rfrac).half) (DFrac.own (QpMul q rq))
    (Or.inr ⟨rfl, Hnn, by omega, rfl⟩) (by omega) hid (by rcases hfl with h | h <;> simp [h]))
    $$ [Hp1 Hd1 Hdata Hpg] as ⟨Hp1, -, Hd1, Hdata, Hpg⟩
  · iframe; iframe #; simp only [↓reduceIte]; ipureintro; trivial
  iapply HΦ
  iexists r, c, mv, k
  isplitr
  · ipureintro; exact Hc
  iframe; iframe #
  rw [hpn, Hc.2.1]
  isplitl [Hp1 Hp2]
  · iapply Hsp.2; iframe
  isplitl [Hd1 Hd2]
  · iapply Hsd.2; iframe
  isplitl [Hcells Hpg]
  · iapply Hcells; iframe
  iframe
  ipureintro
  exact ⟨⟨Hlen, Hl⟩, hT, hvwf, hmv, rfl⟩

end proof

end bbolt
end EtcdGrove
end Perennial
