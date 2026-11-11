/-
Proof of the spec of the same name. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Count
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.txn.Range

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver go_etcd_io.etcd.server.v3.etcdserver.txn
  go_etcd_io.etcd.api.v3
open mvcc.api (MvccState MTxn MvccName)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.txn.Assumptions]

theorem txn.Count.wp_proof
    (hRange : txn.Range.spec (GF := GF) (hG := hG)) :
    txn.Count.spec (GF := GF) (hG := hG) := by
  intro ctx cd lg kv γ key rangeEnd k e revision ot te Q
  wp_start as ⟨Hkv, Hrd, #Hk, #He, #Hctx, #Hct, Hto, #Hlg, %Hklen, Hau⟩
  wp_auto
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ «$a3»
  iStructNamed «$a3»
  ipersist Key; ipersist RangeEnd; ipersist Limit; ipersist Revision; ipersist SortOrder
  ipersist SortTarget; ipersist Serializable; ipersist KeysOnly; ipersist CountOnly
  ipersist MinModRevision; ipersist MaxModRevision; ipersist MinCreateRevision; ipersist MaxCreateRevision
  ihave #Hreq : txn.rangeRequestIs «$a3_ptr» (txn.countOp k (txn.rangeEndOf rangeEnd e) revision) $$ []
  · iunfold txn.rangeRequestIs
    isplitr
    · ipureintro; exact Hnn
    iexists key, rangeEnd, k, e, revision, (0 : w64), (0 : w32), (0 : w32), false, false, true,
      (0 : w64), (0 : w64), (0 : w64), (0 : w64)
    iframe #
    ipureintro; exact ⟨rfl, Hklen⟩
  have heff : (txn.countOp k (txn.rangeEndOf rangeEnd e) revision).effSortOrder = W64 0 := by
    simp [txn.countOp, txn.rangeOpOf, OpFull.effSortOrder]
  wp_apply (hRange ctx cd false lg kv γ «$a3_ptr» _ false ot te Q)
      $$ [$Hkv $Hrd $Hreq $Hctx $Hct $Hto $Hau]
    as %resp %tr %err ⟨Hrd, %Htr, -, -, %σ, HQ, %Hreachσ, #Hres, -, -⟩
  · isplitr
    · simp only [Bool.false_eq_true, ↓reduceIte]; itrivial
    isplitr
    · iexact Hlg
    ipureintro; unfold txn.validSortTarget; simp [txn.countOp, txn.rangeOpOf]
  have hrz : sint.Z (W64 (σ.rev : Int)) = (σ.rev : Int) := by
    have := Hreachσ.2; unfold mvcc.api.MvccState.rev; word
  have hrevo : (txn.countOp k (txn.rangeEndOf rangeEnd e) revision).base.rev = revision := rfl
  iunfold txn.rangeResult at Hres
  icases Hres with (⟨%Hf, %ef, #Hef, %Herr⟩ | ⟨%Hce, -⟩ | ⟨%Hok, %kvs, %more, #Hresp, %Hsrv⟩ |
    ⟨%Hcmp, %ec, #Hec, %Herr⟩)
  · subst Herr
    wp_auto
    iapply HΦ
    iframe Hrd
    iexists σ
    iframe HQ
    isplitr
    · ipureintro; exact Hreachσ
    iright; ileft
    iframe Hef
    ipureintro
    rw [hrevo, hrz] at Hf
    exact ⟨⟨Hf.1, rfl⟩, rfl⟩
  · exfalso
    have := Hce.2.1
    simp [txn.countOp, txn.rangeOpOf] at this
  · obtain ⟨hle, rfl, -⟩ := Hok
    rw [hrevo] at hle
    iunfold txn.rangeResponseIs at Hresp
    icases Hresp with ⟨%Hrnn, %h, %sl, %ps, #Hh, %Hhnn, #Hhr, #Hkvs, #Hsl, #Hkvsis, #Hmore, #Hcount⟩
    wp_auto
    iapply HΦ
    iframe Hrd
    iexists σ
    iframe HQ
    isplitr
    · ipureintro; exact Hreachσ
    ileft
    ipureintro
    refine ⟨rfl, hrz ▸ hle, ?_⟩
    simp [txn.srvCount, txn.countOp, txn.rangeOpOf]
  · -- (M2, S1) below the compaction revision: `ErrCompacted`, `0`
    subst Herr
    wp_auto
    iapply HΦ
    iframe Hrd
    iexists σ
    iframe HQ
    isplitr
    · ipureintro; exact Hreachσ
    iright; iright
    iframe Hec
    ipureintro
    rw [hrevo] at Hcmp
    exact ⟨⟨hrz ▸ Hcmp.1, Hcmp.2.1, rfl⟩, rfl⟩

end proof

end EtcdGrove
end Perennial
