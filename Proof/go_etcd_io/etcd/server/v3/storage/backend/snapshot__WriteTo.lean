/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/snapshot__WriteTo.lean` (S4b, 2026-11-18;
until then a trust-boundary axiom, D22 S-f): `snapshot.WriteTo` is bbolt's `Tx.WriteTo`, promoted
(`s.Tx.WriteTo(w)`), over the snapshot's read transaction (`snapOpenQ`'s `txLive`); bbolt's
`boltImage` is the backend's. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__WriteTo
public import Spec.go_etcd_io.bbolt.Tx__WriteTo

@[expose] public section

set_option linter.iris.dupNamespace false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.backend backend

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.backend.Assumptions]
variable [go_etcd_io.bbolt.Assumptions]

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt backend Fs in
/-- bbolt's `Tx.WriteTo` in the backend's vocabulary, at `theFs`. -/
private theorem bbolt.kvGlue_TxWriteTo (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.WriteTo.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (D : backend.Data) (w : GoInterfaceOk)
    (Wr : Bool → List w8 → IProp GF) (c : Bool) (bs₀ : List w8),
  io.writerPlain w →
  {{ txLive (GF := GF) tx γ q (bbolt.TxView.ro D) ∗ writerOk w Wr ∗ Wr c bs₀ }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"WriteTo")) (Val #(GoInterface.ok w)))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      ∃ bs : List w8, txLive tx γ q (bbolt.TxView.ro D) ∗ Wr true (bs₀ ++ bs) ∗
        ⌜err = GoInterface.nil → backend.boltImage bs D⌝ }} := by
  intro tx γ q D w Wr c bs₀ hw
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, fax, fsax, nex⟩
  · simp only [backend.txLive, onFs_none hfs]
    iintro %Φ ⟨H, -⟩ HΦ
    iexfalso; iexact H
  · simp only [backend.txLive, onFs_some hfs]
    iintro %Φ ⟨Hl, #Hw, HW⟩ HΦ
    wp_apply (h tx γ q D w Wr c bs₀ hw) $$ [$Hl $Hw $HW] as %n %err ⟨%bs, Hl, HW, Hr⟩
    iapply HΦ
    iexists bs
    iframe Hl HW
    icases Hr with (⟨%He, -⟩ | %He)
    · ipureintro; intro _; exact He.2
    · ipureintro; intro h0; exact absurd h0 He

/-- `s.WriteTo(w)`: `s.Tx.WriteTo(w)` of the snapshot's read transaction. -/
theorem backend.snapshot.WriteTo.wp_proof
    (hWT : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.WriteTo.spec (GF := GF) (hG := hG)) :
    backend.snapshot.WriteTo.spec (GF := GF) (hG := hG) := by
  replace hWT := bbolt.kvGlue_TxWriteTo hWT
  intro sp D γ q w Wr c bs₀ hw
  wp_start as ⟨Hs, #Hw, HW⟩
  iunfold snapOpenQ at Hs
  icases Hs with ⟨%tx, %γd, #Ha, Hg, Hl⟩
  ihave #Ha' := Ha
  iunfold snapAt at Ha'
  icases Ha' with ⟨%sc, %dc, %γsc, %γdc, #Htx, -, -, -, -, -⟩
  wp_auto
  wp_apply (hWT tx γd q D w Wr c bs₀ hw) $$ [$Hl $Hw $HW] as %n %err ⟨%bs, Hl, HW, %Himg⟩
  iapply HΦ
  iexists bs
  iframe HW %Himg
  unfold snapOpenQ
  iexists tx, γd
  iframe Ha Hg Hl

end proof

end EtcdGrove
end Perennial
