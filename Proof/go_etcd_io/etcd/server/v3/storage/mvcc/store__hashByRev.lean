/-
Proof of `Spec/.../mvcc/store__hashByRev.lean` (etcd-io/etcd#21202, pr-verify/etcd-21202): the
refactor, `hashByRevWithCompactRev(rev, 0)`. Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__hashByRev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.store__hashByRevWithCompactRev

@[expose] public section

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

/-- With `compactRev = 0`, the hash's compaction revision is the store's. -/
theorem mvcc.hashCrev_zero (cm : Int) : mvcc.hashCrev (W64 0) cm = W64 cm := by
  unfold mvcc.hashCrev
  exact if_pos (by decide)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.store.hashByRev.wp_proof
    (hW : mvcc.store.hashByRevWithCompactRev.spec (GF := GF) (hG := hG)) :
    mvcc.store.hashByRev.spec (GF := GF) (hG := hG) := by
  intro s γ rev Hcmp Hrev0
  wp_start as ⟨#Hhist, #Hs, Hrd⟩
  ihave Hcok : mvcc.hashCrevOk γ (W64 0) $$ []
  · iunfold mvcc.hashCrevOk; ileft; ipureintro; decide
  (try wp_auto)
  wp_apply (hW s γ rev (W64 0) Hcmp Hrev0) $$ [$Hhist $Hs $Hrd $Hcok]
    as %h %cur %err ⟨Hrd, -, %log, %cm, #Hcert, #Hlb, %Hlg, Hcase⟩
  (try wp_auto)
  ihave #Hc2 := Hcert
  iunfold mvcc.idxCert at Hc2
  icases Hc2 with ⟨-, -, %Hlwf, -⟩
  have Hz : sint.Z (W64 cm : w64) = cm := by
    have h1 := Hlg.2.1
    have h2 := Hlg.2.2
    have h3 := Hlwf.2.1
    unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  iapply HΦ
  iframe Hrd
  iexists log, cm
  iframe #
  isplitr
  · ipureintro; exact Hlg
  rw [mvcc.hashCrev_zero]
  icases Hcase with (%Hok | ⟨%Hce, Hec⟩ | ⟨%Hfe, Hef⟩)
  · ileft
    ipureintro
    obtain ⟨H1, H2, H3, -, H5, H6, H7⟩ := Hok
    exact ⟨H1, H2, H3, H5, H6, H7⟩
  · iright; ileft
    isplitr
    · ipureintro; rw [Hz] at Hce; exact Hce
    iexact Hec
  · iright; iright
    isplitr
    · ipureintro; rw [Hz] at Hfe; exact Hfe
    iexact Hef

end proof

end EtcdGrove
end Perennial
