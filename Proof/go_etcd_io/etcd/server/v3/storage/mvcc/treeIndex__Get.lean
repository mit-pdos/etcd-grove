/-
Proof of `Spec/.../mvcc/treeIndex__Get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__Get
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.ReadLemmas
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.treeIndex__unsafeGet
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


theorem mvcc.treeIndex.Get.wp_proof
    (hUnsafe : mvcc.treeIndex.unsafeGet.spec (GF := GF) (hG := hG)) :
    mvcc.treeIndex.Get.spec (GF := GF) (hG := hG) := by
  intro ti γ kn key k atRev e
  generalize hlog : kn.log = log at *
  wp_start as ⟨#Hti, Hrd, Hkn, %Hrev, #Hkey, #Herr⟩
  iunfold mvcc.isTreeIndex at Hti
  iNamed Hti
  iunfold mvcc.idxReader at Hrd
  icases Hrd with ⟨%t', #Htree', Hrd⟩
  icombine Htree Htree' gives %Ht'
  subst Ht'
  wp_apply wp_with_defer
  iintro %defer Hdefer
  (try wp_auto)
  -- `ti.RLock()`: the promoted method
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RLock")]
  wp_call
  (try wp_auto)
  wp_apply +noauto sync.RWMutex.wp_RLock $$ [$Hrd] as ⟨Hrl, HP⟩
  wp_auto_lc 1
  imod (lc_fupd_elim_later (E := ⊤) (P := mvcc.idxLockInv t γ sync.rfrac)) $$ Hlc1 HP with HP
  iunfold mvcc.idxLockInv at HP
  icases HP with ⟨%ilog, %pend, %L, HP⟩
  iNamedSuffix HP "L"
  obtain ⟨HwfL, HlenL, HpendL, HcsL⟩ := HwfL
  (try wp_auto)
  -- `ti.unsafeGet(key, atRev)`
  wp_apply (hUnsafe ti t lg L sync.rfrac key k atRev e) $$ [$HtreeL] as ⟨HtreeL, -⟩
  · iframe #
    ipureintro
    exact entries_not_empty L _ HLL
  -- the answer is the certified log's
  icases mvcc.idxKnows_facts γ kn log hlog ilog pend sync.rfrac $$ Hkn HhistL HnevL with ⟨%Hfacts, Hkn, HnevL⟩
  obtain ⟨Hcmp, Hcnt', Hwf0, Hlen0, Hcs0⟩ := Hfacts
  obtain ⟨r, hr, hrz⟩ : ∃ r : Nat, atRev = W64 r ∧ sint.Z atRev = r :=
    ⟨(sint.Z atRev).toNat, by
      have h := Int.toNat_of_nonneg Hrev.1
      rw [show (((sint.Z atRev).toNat : Nat) : Int) = sint.Z atRev from h]
      exact BitVec.ofInt_toInt.symm, (Int.toNat_of_nonneg Hrev.1).symm⟩
  have hrlt : r < log.length := by omega
  have hans : (mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty =
      mvcc.kiOfKey (mvcc.evsOf (ilog ++ [pend])) k := by
    rw [HLL]; exact (mvcc.indexOf_rep _).2 k
  have hstab := mvcc.reader_answer log ilog pend Hcmp Hcnt' (by omega) Hwf0 Hcs0 k r hrlt
  have hval : mvcc.kiGetVal ((mvcc.idxGet (mvcc.idxOfEntries L) k).getD mvcc.kiEmpty) atRev
      (GoInterface.ok e) = mvcc.kiGetVal (mvcc.kiOfKey (mvcc.evsOf log) k) atRev (GoInterface.ok e) := by
    unfold mvcc.kiGetVal; rw [hans, hr, hstab]
  rw [hval]
  obtain ⟨m, c, v, i, hp⟩ := kiGetVal_pairs (mvcc.kiOfKey (mvcc.evsOf log) k) atRev (GoInterface.ok e)
  rw [hp]
  wp_auto
  -- the deferred `ti.RUnlock()`
  rw [method_unfold (t := go.GoType.PointerType treeIndex.ty) (m := go!"RUnlock")]
  wp_call
  (try wp_auto)
  wp_apply sync.RWMutex.wp_RUnlock $$ [$Hrl HnevL HtreeL] as Hrd
  · inext
    iunfold mvcc.idxLockInv
    iexists ilog, pend, L
    simp only [named]
    iframe HnevL HtreeL
    iframe #
    ipureintro
    exact ⟨HLL, HwfL, HlenL, HpendL, HcsL⟩
  (try wp_auto)
  rw [← hp]
  iapply HΦ
  iframe Hkn
  iframe #
  iunfold mvcc.idxReader
  iexists t
  iframe Hrd
  iexact Htree

end proof

end EtcdGrove
end Perennial
