/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Range
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
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

theorem mvcc.storeTxnWrite.Range.wp_proof
    (hKeys : mvcc.storeTxnCommon.rangeKeys.spec (GF := GF) (hG := hG)) :
    mvcc.storeTxnWrite.Range.spec (GF := GF) (hG := hG) := by
  intro tw s γ ilog pend ctx cd key endk k e ro
  wp_start as ⟨Htw, #Hctx, #Hkey, #Hend⟩
  iunfold mvcc.storeTxnWriteIs at Htw
  iNamed Htw
  -- the writer's log and the number of changes
  ihave %Hchl := ownSlice_len chs (DFrac.own 1) ps $$ Hchs
  have hcl : chs.len = W64 (pend.length : Int) := by
    rw [← Hps, Hchl.1]; exact (mvcc.W64_sint_nat chs.len Hchl.2).symm
  ihave %Hwf := mvcc.idxWriter_wf γ.idx ilog pend $$ Hw
  obtain ⟨Hwf', Hlen, Hplen, Hcs⟩ := Hwf
  have hpos : 0 < ilog.length := List.length_pos_iff.2 Hne
  have hrev : (W64 ((ilog.length : Int) - 1) : w64) + W64 1 = W64 (ilog.length : Int) := by
    rw [← mvcc.W64_add_one]; simp
  have hwrZ : sint.Z (W64 ((mvcc.writeRev ilog pend : Nat) : Int) : w64) = mvcc.writeRev ilog pend := by
    have := mvcc.writeRev_lt ilog pend Hne
    simp only [List.length_append, List.length_singleton] at this
    unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  -- the `storeTxnCommon`'s fields, for `rangeKeys`
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Htw
  iStructNamedPrefix Htw "W"
  ihave %Hnnc := typedPointsto_not_null _ _ _ $$ WstoreTxnCommon
  iStructNamedPrefix WstoreTxnCommon "C"
  have hpZ : sint.Z (W64 (pend.length : Int) : w64) = pend.length := by
    unfold sint.Z W64
    rw [BitVec.toInt_ofInt_eq_self (by decide)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)
      (by rw [show (64 - 1 : Nat) = 63 from rfl]; omega)]
  have h0Z : sint.Z (W64 0 : w64) = 0 := by decide
  (try wp_auto)
  -- `rev := tw.beginRev; if len(tw.changes) > 0 { rev++ }`: the transaction's revision
  wp_if_destruct
  -- a change: the pending revision; no change: the committed log's last revision (`hwr` turns
  -- the code's revision into `writeRev`, and back after the call)
  all_goals first
    | (have hpend : pend ≠ [] := by
         intro h; subst h
         rw [hcl] at Hif
         first | (simp at Hif) | exact absurd Hif (by decide)
       (try wp_auto)
       have hwr : (W64 ((mvcc.writeRev ilog pend : Nat) : Int) : w64) = W64 (ilog.length : Int) := by
         unfold mvcc.writeRev; rw [if_neg hpend]
       rw [hrev, ← hwr])
    | (have hpend : pend = [] := by
         apply List.length_eq_zero_iff.1
         have h := Hif
         first | (rw [hcl, hpZ, h0Z] at h; omega) | (simp only [hcl, hpZ, h0Z] at h; omega)
       have hwr : (W64 ((mvcc.writeRev ilog pend : Nat) : Int) : w64) =
           W64 ((ilog.length : Int) - 1) := by
         unfold mvcc.writeRev; rw [if_pos hpend]; congr 1; omega
       (try wp_auto)
       rw [← hwr])
  -- `tw.rangeKeys(ctx, key, end, rev, ro)`: the promoted method, `storeTxnCommon`'s
  all_goals
    rw [method_unfold (t := go.GoType.PointerType storeTxnWrite.ty) (m := go!"rangeKeys")]
    wp_call
    (try wp_auto)
    -- the bucket through the batch transaction (its own puts), the index by the writer
    ihave #Hrdr := mvcc.batchTx_reader bt (mvcc.bucketView γ) (mvcc.writerRes s γ) Locked
      (mvcc.pendPuts ilog pend) (1 : Qp).half (mvcc.bucketMap ilog) $$ Hbt
    ihave HR : iprop(Locked (mvcc.pendPuts ilog pend) ∗
        mvcc.bucketView γ (1 : Qp).half (mvcc.bucketMap ilog)) $$ [Hlocked Hbv]
    · iframe Hlocked Hbv
    ihave Hkn : mvcc.idxKnows γ.idx (.writer ilog pend) $$ [Hw]
    · rw [mvcc.idxKnows_writer]; iexact Hw
    wp_apply (hKeys (mvcc.txCommonW tw) s trace ti bt (DFrac.own 1)
        ((mvcc.pendPuts ilog pend).foldl (fun m p => GMap.insert p.1 p.2 m) (mvcc.bucketMap ilog))
        iprop(Locked (mvcc.pendPuts ilog pend) ∗ mvcc.bucketView γ (1 : Qp).half (mvcc.bucketMap ilog))
        γ (.writer ilog pend) (ilog ++ [pend]) (W64 ((mvcc.writeRev ilog pend : Nat) : Int))
        ctx cd key endk k e ro)
      $$ [$Hs $Cs $Ctx $Ctrace $Hrdr $HR $Hkn $Hidx $Hti $Hctx $Hkey $Hend]
      as %r %err ⟨Cs, Ctx, Ctrace, ⟨Hlocked, Hbv⟩, Hw, Hti, Hout⟩
    · ipureintro
      refine ⟨?_, rfl, by simp, ?_⟩
      · rw [mvcc.bucketMap_append ilog pend Hne]; exact fun _ _ h => h
      · rw [hwrZ]; have := mvcc.writeRev_lt ilog pend Hne; omega
    rw [mvcc.idxKnows_writer]
    (try wp_auto)
    -- the transaction back: the `storeTxnCommon`, then the `storeTxnWrite`
    ihave Hc : (mvcc.txCommonW tw ↦ ({ s' := s, tx' := GoInterface.ok bt, firstRev' := W64 0, rev' := W64 0, trace' := trace } : storeTxnCommon) : IProp GF)
      $$ [Cs Ctx CfirstRev Crev Ctrace]
    · iapply typedPointsto_combine _ _ _ Hnnc
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    rw [hwr]
    ihave Htw : (tw ↦ ({ storeTxnCommon' := { s' := s, tx' := GoInterface.ok bt, firstRev' := W64 0, rev' := W64 0, trace' := trace }, tx' := GoInterface.ok bt, beginRev' := W64 ((ilog.length : Int) - 1), changes' := chs } : storeTxnWrite) : IProp GF)
      $$ [Hc Wtx WbeginRev Wchanges]
    · iapply typedPointsto_combine _ _ _ Hnn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    iapply HΦ
    iframe Hout
    iunfold mvcc.storeTxnWriteIs
    iexists trace, ti, bt, Locked, chs, ps, ntok
    simp only [named]
    iframe Htoks Htok Htw Hchs Hcap Hkvs Hlocked Hw Hclog Hcur Hbv Hmu HrevMu Hti
    iframe #
    ipureintro; exact ⟨Hbudget, Hps, Hne⟩

end proof

end EtcdGrove
end Perennial
