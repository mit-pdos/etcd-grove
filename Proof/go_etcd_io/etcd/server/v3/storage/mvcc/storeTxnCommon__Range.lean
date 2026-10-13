/-
Proof of `Spec/.../mvcc/storeTxnCommon__Range.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Range
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__Rev
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnCommon__rangeKeys

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnCommon.Range.wp_proof (hRev : mvcc.storeTxnCommon.Rev.spec (GF := GF) (hG := hG))
    (hKeys : mvcc.storeTxnCommon.rangeKeys.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnCommon.Range.spec (GF := GF) (hG := hG) := by
  intro tr s trace ti rt γ log rev ctx cd todo key endk k e ro
  wp_start as ⟨#Hs, #Htr, Hrd, #Hidx, Hti, #Hctx, #Hkey, #Hend⟩
  iunfold mvcc.txReader at Hrd
  icases Hrd with ⟨%m, %Rd, %L, %Tok, Hrd⟩
  iNamed Hrd
  ihave #Htr0 : mvcc.storeTxnReadIs tr s rt trace γ log rev $$ []
  · iexact Htr
  iunfold mvcc.storeTxnReadIs at Htr
  iNamedSuffix Htr "T"
  (try wp_auto)
  wp_apply (hRev (mvcc.txCommon tr) rev) $$ [$HrevT]
  (try wp_auto)
  -- what `rangeKeys` uses: the snapshot as a reader, the certificate as the index's knowledge
  ihave #Hrdr := mvcc.keyReadSnap_reader rt m Rd L Tok $$ Hsnap
  ihave #Hcert0 : mvcc.idxCert γ.idx log $$ []
  · iexact HcertT
  iunfold mvcc.idxCert at HcertT
  icases HcertT with ⟨-, -, %Hcwf, -⟩
  have hpos : 0 < log.length := List.length_pos_iff.2 HneT
  have hrv : 0 ≤ sint.Z rev ∧ sint.Z rev < log.length := by
    rw [HrevT]; unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide) (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
    omega
  ihave Hkn : mvcc.idxKnows γ.idx (.cert log) $$ []
  · rw [mvcc.idxKnows_cert]; iexact Hcert0
  wp_apply (hKeys (mvcc.txCommon tr) s trace ti rt DFrac.discard m Tok γ (.cert log) log rev
      ctx cd todo key endk k e ro (by assumption))
    $$ [$Hs $HsT $HtxcT $HtraceT $Hrdr $Htok $Hkn $Hidx $Hti $Hctx $Hkey $Hend]
    as %r %err ⟨%Htodo, -, -, -, Htok, -, Hti, Hout⟩
  · ipureintro; exact ⟨Hsub, rfl, HneT, hrv⟩
  (try wp_auto)
  iapply HΦ
  iframe Hti Hout
  isplitl []
  · ipureintro; exact Htodo
  iunfold mvcc.txReader
  iexists m, Rd, L, Tok
  simp only [named]
  iframe Htok Hsnap
  ipureintro; exact Hsub

end proof

end EtcdGrove
end Perennial
