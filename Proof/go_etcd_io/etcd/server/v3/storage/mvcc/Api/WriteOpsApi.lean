/-
**`Txn.Put.contract` and `Txn.DeleteRange.contract` at `*metricsTxnWrite`** (M4, track B, 2026-11-06).
Lean-first (no Rocq counterpart). Over the sealed definitions of `Api.lean` (imported with `import
all`).

`metricsTxnWrite_PutT`: `metricsTxnWrite.Put`'s proof with the trace lent at its emptiness `te` (as
`RangeApi`'s `metricsTxnWrite_RangeT`). `DeleteRange` is `metricsTxnWrite.DeleteRange.spec` at the
API's trace part (`True`); its log facts are the write transaction's after the deletes
(`RangeApi.isTxnWriteT_small`: the index writer's `IdxWf`).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
import all Spec.go_etcd_io.etcd.server.v3.storage.mvcc.Api
public import Proof.go_etcd_io.etcd.server.v3.storage.mvcc.Api.RangeApi
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.storeTxnWrite__Put
public import Spec.go_etcd_io.etcd.server.v3.storage.mvcc.metricsTxnWrite__DeleteRange

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvcc
namespace api

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.storage.mvcc

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.storage.mvcc.Assumptions]

local notation "pkgInit" => isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.mvcc

/-- **`metricsTxnWrite.Put` with the trace lent at its emptiness** (see the header). -/
theorem metricsTxnWrite_PutT (hPut : mvcc.storeTxnWrite.Put.spec (GF := GF) (hG := hG)) :
    ∀ (trace : Loc) (mw s : Loc) (γ : StoreNames) (ilog : Log) (pend : List Change)
      (puts deletes putSize : w64) (key value : GoSlice) (k v : GoString) (leaseID : w64)
      (L : List w64) (crev : Int) (te : Bool),
    {{ pkgInit ∗ isTxnWriteT mw s γ trace ilog pend puts deletes putSize crev iprop(True) false
          iprop(True) ∗ traceutil.ownTrace trace te ∗ key ↦*□ k ∗ value ↦*□ v ∗
        ⌜(k.length : Int) < 2 ^ 63 - 1⌝ ∗
        lease.leaseOwn γ.leases L (pendItems ilog pend) ∗ ⌜leaseID = W64 0 ∨ leaseID ∈ L⌝ }}
      (App (App (App (Val (mw @!! go.GoType.PointerType metricsTxnWrite.ty @!! go!"Put")) (Val #key))
        (Val #value)) (Val #leaseID))
    {{ RET #(W64 (ilog.length : Int) : w64);
        isTxnWriteT mw s γ trace ilog (pend ++ [.put k v leaseID]) (puts + W64 1) deletes
          (putSize + (key.len + value.len)) crev iprop(True) false iprop(True) ∗
        traceutil.ownTrace trace te ∗
        lease.leaseOwn γ.leases L (pendItems ilog (pend ++ [.put k v leaseID])) }} := by
  intro trace mw s γ ilog pend puts deletes putSize key value k v leaseID L crev te
  wp_start as ⟨Htx, Hte, #Hkey, #Hval, %Hklen, Hown, %Hlease⟩
  iunfold isTxnWriteT at Htx
  iNamed Htx
  (try wp_auto)
  wp_apply (hPut trace tw s γ ilog pend key value k v leaseID L te crev iprop(True))
    $$ [$Htw $Hkey $Hval $Hown $Hte] as ⟨Htw, Hown, Hte⟩
  · ipureintro; exact ⟨Hklen, Hlease⟩
  (try wp_auto)
  iapply HΦ
  iframe Hown Hte
  iunfold isTxnWriteT
  iexists tw, ranges
  iframe Htw Hmw

/-- **`Txn.Put.contract` at `*metricsTxnWrite`.** -/
theorem metricsTxnWrite.Put.wp_api (hPut : mvcc.storeTxnWrite.Put.spec (GF := GF) (hG := hG)) :
    metricsTxnWrite.Put.spec (GF := GF) := by
  intro t0 (γ : mvcc.StoreNames) trace te σ pend key value k vv leaseID L
  iintro %Φ ⟨#Hpkg, Htx, Hte, #Hkey, #Hval, %Hklen, Hown, %Hlease⟩ HΦ
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
  ihave %Hw := wrWrap_pm t0 _ s mw σ.log $$ Hwrap
  obtain ⟨hm, Hwq⟩ := Hw
  subst hm
  have hl : mvccLeases γ = (γ.withPhys p).leases := rfl
  rw [hl]
  iapply (metricsTxnWrite_PutT hPut trace t0 s (γ.withPhys p) σ.log pend puts deletes putSize key value
      k vv leaseID L σ.crev te) $$ [Htx Hte Hown] [HΦ Hback]
  · iframe Hpkg Htx Hte Hkey Hval Hown
    ipureintro; exact ⟨Hklen, Hlease⟩
  inext
  iintro ⟨Htx, Hte, Hown⟩
  iapply HΦ
  iframe Hte Hown
  iunfold mvccTxn
  simp only [mvccTxnI]
  iexists t0, s, p, (puts + W64 1), deletes, (putSize + (key.len + value.len))
  iframe Htx Hback Hfree
  isplitr
  · ipureintro; exact Hk0
  iunfold wrWrap; ileft; ipureintro; exact ⟨rfl, Hwq⟩

/-- **`Txn.DeleteRange.contract` at `*metricsTxnWrite`.** -/
theorem metricsTxnWrite.DeleteRange.wp_api
    (hDel : mvcc.metricsTxnWrite.DeleteRange.spec (GF := GF) (hG := hG)) :
    ∀ t : Loc, Txn.DeleteRange.contract (GF := GF) (go.GoType.PointerType metricsTxnWrite.ty) #t := by
  intro t0 (γ : mvcc.StoreNames) trace σ pend key endk k e L
  iintro %Φ ⟨#Hpkg, Htx, #Hkey, #Hend, Hown⟩ HΦ
  iunfold mvccTxn at Htx
  simp only [mvccTxnI]
  icases Htx with ⟨%mw, %s, %p, %puts, %deletes, %putSize, %Hk0, Htx, Hback, #Hfree, Hwrap⟩
  ihave %Hw := wrWrap_pm t0 _ s mw σ.log $$ Hwrap
  obtain ⟨hm, Hwq⟩ := Hw
  subst hm
  have hl : mvccLeases γ = (γ.withPhys p).leases := rfl
  rw [hl]
  iapply (hDel trace t0 s (γ.withPhys p) σ.log pend puts deletes putSize key endk k e L σ.crev
      iprop(True) iprop(True)) $$ [Htx Hown] [HΦ Hback]
  · iframe Hpkg Htx Hkey Hend Hown
  inext
  iintro %n %rev ⟨Htx, Hown, %Hnr⟩
  ihave %Hsm := isTxnWriteT_small _ _ _ _ _ _ _ _ _ _ _ _ _ $$ [$Htx]
  iapply HΦ
  iframe Hown
  isplitl
  · iunfold mvccTxn
    simp only [mvccTxnI]
    iexists t0, s, p, puts, (deletes + W64 1), putSize
    iframe Htx Hback Hfree
    isplitr
    · ipureintro; exact Hk0
    iunfold wrWrap; ileft; ipureintro; exact ⟨rfl, Hwq⟩
  ipureintro
  exact ⟨by rw [List.length_map]; exact Hnr, Hsm.1, Hsm.2.2.1⟩

end proof

end api
end mvcc
end EtcdGrove
end Perennial
