/-
Proof of `Spec/go_etcd_io/etcd/server/v3/storage/backend/snapshot__Size.lean` (S4b, 2026-11-18;
until then a trust-boundary axiom, D22 S-h): `snapshot.Size` is bbolt's `Tx.Size`, promoted
(`s.Tx.Size()`), over the snapshot's read transaction (`snapOpenQ`'s `txLive`), whose result bbolt
bounds for a read transaction. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.backend.snapshot__Size
public import Spec.go_etcd_io.bbolt.Tx__Size

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
/-- bbolt's `Tx.Size` of a read transaction in the backend's vocabulary, at `theFs`. -/
private theorem bbolt.kvGlue_TxSize_ro (h : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Size.spec (GF := GF) (hG := hG)) :
  ∀ (tx : Loc) (γ : DBNames) (q : Qp) (D : backend.Data),
  {{ txLive (GF := GF) tx γ q (bbolt.TxView.ro D) }}
    (App (Val (tx @!! go.GoType.PointerType go_etcd_io.bbolt.Tx.ty @!! go!"Size")) (Val #()))
  {{ (n : w64), RET #n; txLive tx γ q (bbolt.TxView.ro D) ∗ ⌜0 ≤ sint.Z n ∧ sint.Z n < 2 ^ 62⌝ }} := by
  intro tx γ q D
  rcases hfs : theFs GF with _ | ⟨Sx, okx, hasx, nex⟩
  · simp only [backend.txLive, onFs_none hfs]
    iintro %Φ H HΦ
    iexfalso; iexact H
  · simp only [backend.txLive, onFs_some hfs]
    iintro %Φ Hl HΦ
    wp_apply (h tx γ q (TxView.ro D)) $$ [$Hl] as %n ⟨Hl, %Hn⟩
    iapply HΦ; iframe Hl; ipureintro; exact Hn rfl

/-- `s.Size()`: `s.Tx.Size()` of the snapshot's read transaction. -/
theorem backend.snapshot.Size.wp_proof
    (hSize : ∀ [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
, bbolt.Tx.Size.spec (GF := GF) (hG := hG)) :
    backend.snapshot.Size.spec (GF := GF) (hG := hG) := by
  replace hSize := bbolt.kvGlue_TxSize_ro hSize
  intro sp D γ q
  wp_start as Hs
  iunfold snapOpenQ at Hs
  icases Hs with ⟨%tx, %γd, #Ha, Hg, Hl⟩
  ihave #Ha' := Ha
  iunfold snapAt at Ha'
  icases Ha' with ⟨%sc, %dc, %γsc, %γdc, #Htx, -, -, -, -, -⟩
  wp_auto
  wp_apply (hSize tx γd q D) $$ [$Hl] as %n ⟨Hl, %Hn⟩
  iapply HΦ
  iframe %Hn
  unfold snapOpenQ
  iexists tx, γd
  iframe Ha Hg Hl

end proof

end EtcdGrove
end Perennial
