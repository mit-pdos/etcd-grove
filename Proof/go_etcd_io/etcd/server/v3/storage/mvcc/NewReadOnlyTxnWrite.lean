/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.NewReadOnlyTxnWrite
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ApiLemmas


@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.NewReadOnlyTxnWrite.wp_proof :
    mvcc.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG) := by
  intro trace mw s γ log rev crev Z
  wp_start as Htx
  (try wp_auto)
  wp_alloc trw as Htrw
  (try wp_auto)
  iStructNamedPrefix Htrw "W"
  iapply HΦ
  iunfold mvcc.isRoTxnWrite
  iexists mw
  iframe

/-- **The candidate `NewReadOnlyTxnWrite`** (`specC`): `spec`'s, at the state. -/
theorem mvcc.NewReadOnlyTxnWrite.wp_proofC (hO : mvcc.NewReadOnlyTxnWrite.spec (GF := GF) (hG := hG)) :
    mvcc.NewReadOnlyTxnWrite.specC (GF := GF) (hG := hG) := by
  intro mw γ trace σ
  iintro %Φ ⟨#Hpkg, Htx⟩ HΦ
  icases (mvcc.mvccTxn_read_eq mw γ trace σ).1 $$ Htx with ⟨%s, %Hl, #Hs, Hrd, Hloan⟩
  iapply (hO trace mw s γ.st σ.log (W64 (σ.rev : Int)) σ.crev iprop(True)) $$ %Φ [Hrd]
  · iframe Hpkg Hrd
  inext
  iintro %trw Hro
  iapply HΦ
  iapply (mvcc.mvccTxn_ro_eq trw γ trace σ).2
  iexists s; iframe Hs Hro Hloan; ipureintro; exact Hl

end proof

end EtcdGrove
end Perennial
