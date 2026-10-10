/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/evalCmp.lean`. `evalCmp` tests the operand's
wrapper (`tv != nil`): `cmpSetAt` says it is not nil. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.evalCmp
public import Spec.go_etcd_io.etcd.client.v3.leasing.compareInt64
public import Spec.go_etcd_io.etcd.client.v3.Cmp__GetCompare
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Compare__GetTarget
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Compare__GetTargetUnion
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Compare__GetResult
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseEvalLemmas

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [AllG GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem evalCmp.wp_proof (hcmp64 : compareInt64.spec (GF := GF) (hG := hG))
    (hGC : Cmp.GetCompare.spec (GF := GF) (hG := hG))
    (hTgt : Compare.GetTarget.spec (GF := GF) (hG := hG))
    (hTU : Compare.GetTargetUnion.spec (GF := GF) (hG := hG))
    (hRes : Compare.GetResult.spec (GF := GF) (hG := hG)) :
    _root_.Perennial.EtcdGrove.leasing.evalCmp.spec (GF := GF) (hG := hG) := by
  intro e dq c m
  wp_start as ⟨Hresp, #Hc⟩
  rw [respOwn_def]
  icases Hresp with ⟨%Hrnn, Hhd, #Hehd, Hkvs, Hsl, Hcap, Hkv, Hmore, Hcount⟩
  unfold cmpSetAt
  icases Hc with ⟨%Hcnn, %ksl, %esl, %u, #HR, #HT, #HK, #HKs, #HE, #HEs, #HU, #HUa, %Hunn, %Hwn⟩
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hsl
  wp_join iprop(∃ r : w64, result_ptr ↦ r ∗ ⌜sint.Z r = leaseCmpSign m e.kv⌝ ∗ tcmp_ptr ↦ c ∗
      resp_ptr ↦ e.resp ∗
      structFieldRef etcdserverpb.RangeResponse go!"Kvs" e.resp ↦{dq} e.kvsSl ∗
      e.kvsSl ↦*{dq} (e.kvs.map CachedKv.p) ∗ ([∗list] c ∈ e.kvs, cachedKvOwn c dq))
    with [result tcmp resp Hkvs Hsl Hkv] as ⟨%r, result, %Hr, tcmp, resp, Hkvs, Hsl, Hkv⟩
  · have hkvs : e.kvs = [] := by
      have h0 := Hlen.1; rw [Hif, List.length_map] at h0
      exact List.length_eq_zero_iff.mp (by rw [h0]; rfl)
    iexists (W64 0)
    iframe
    ipureintro
    simp [LeaseEntry.kv, hkvs, leaseCmpSign]
  · obtain ⟨c0, cs, hc⟩ : ∃ c0 cs, e.kvs = c0 :: cs := by
      cases h1 : e.kvs with
      | nil => rw [h1] at Hlen; exfalso; apply Hif; have := Hlen.1; simp at this; word
      | cons c0 cs => exact ⟨c0, cs, rfl⟩
    have hb : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z e.kvsSl.len := by
      have := Hlen.1; rw [hc] at this; simp only [List.map_cons, List.length_cons] at this; word
    simp only [hb, _root_.and_self, ↓reduceIte]
    rw [hc]
    wp_apply wp_load_slice_index _ (sint.Z (W64 0)) _ _ c0.p (by word) $$ [Hsl] as Hsl
    · iframe; ipureintro; rfl
    wp_apply hGC $$ [$tcmp] as tcmp
    · iframe %
    wp_apply hTgt $$ [$HT]
    · iframe %
    icases Hkv with ⟨Hc0, Hcs⟩
    rw [cachedKvOwn_def c0]
    icases Hc0 with ⟨%Hpnn, HcK, #HcKb, HcC, HcM, HcV, HcVal, #HcValb, HcL⟩
    unfold compareUnionAt at *
    cases ht : m.target
    case version =>
      simp only [CmpTarget.code]
      icases HUa with (%Hn | ⟨%w, %Hu, #Hw⟩)
      · exact absurd Hn.1 Hunn
      wp_auto
      wp_apply hTU $$ [$HU]
      · iframe %
      rw [Hu]
      wp_auto
      rw [decide_eq_false (Hwn _ w Hu)]
      wp_auto
      wp_apply hcmp64
      isplitr
      · ipureintro; rfl
      iexists (compareInt64M c0.kv.version m.num)
      iframe
      rw [cachedKvOwn_def c0]
      iframe
      iframe #
      ipureintro
      refine ⟨?_, Hpnn⟩
      simp [LeaseEntry.kv, hc, leaseCmpSign, ht, sint_compareInt64M]
    case create =>
      simp only [CmpTarget.code]
      icases HUa with (%Hn | ⟨%w, %Hu, #Hw⟩)
      · exact absurd Hn.1 Hunn
      wp_auto
      wp_apply hTU $$ [$HU]
      · iframe %
      rw [Hu]
      wp_auto
      rw [decide_eq_false (Hwn _ w Hu)]
      wp_auto
      wp_apply hcmp64
      isplitr
      · ipureintro; rfl
      iexists (compareInt64M c0.kv.createRev m.num)
      iframe
      rw [cachedKvOwn_def c0]
      iframe
      iframe #
      ipureintro
      refine ⟨?_, Hpnn⟩
      simp [LeaseEntry.kv, hc, leaseCmpSign, ht, sint_compareInt64M]
    case mod =>
      simp only [CmpTarget.code]
      icases HUa with (%Hn | ⟨%w, %Hu, #Hw⟩)
      · exact absurd Hn.1 Hunn
      wp_auto
      wp_apply hTU $$ [$HU]
      · iframe %
      rw [Hu]
      wp_auto
      rw [decide_eq_false (Hwn _ w Hu)]
      wp_auto
      wp_apply hcmp64
      isplitr
      · ipureintro; rfl
      iexists (compareInt64M c0.kv.modRev m.num)
      iframe
      rw [cachedKvOwn_def c0]
      iframe
      iframe #
      ipureintro
      refine ⟨?_, Hpnn⟩
      simp [LeaseEntry.kv, hc, leaseCmpSign, ht, sint_compareInt64M]
    case value =>
      simp only [CmpTarget.code]
      icases HUa with (%Hn | ⟨%w, %vsl, %Hu, #Hw, #Hvs⟩)
      · exact absurd Hn.1 Hunn
      wp_auto
      wp_apply hTU $$ [$HU]
      · iframe %
      rw [Hu]
      wp_auto
      rw [decide_eq_false (Hwn _ w Hu)]
      wp_auto
      wp_apply bytes.wp_Compare c0.valSl vsl DFrac.discard DFrac.discard c0.kv.value m.val $$ [] as ⟨-, -⟩
      · iframe #
      isplitr
      · ipureintro; rfl
      iexists (bytes.compareResult c0.kv.value m.val)
      iframe
      rw [cachedKvOwn_def c0]
      iframe
      iframe #
      ipureintro
      refine ⟨?_, Hpnn⟩
      simp only [LeaseEntry.kv, hc, leaseCmpSign, ht, List.head?_cons, Option.map_some]
      unfold bytes.compareResult bytesCmp cmpSign
      split <;> (try split) <;> simp_all
    case lease =>
      simp only [CmpTarget.code]
      wp_auto
      isplitr
      · ipureintro; rfl
      iexists (W64 0)
      iframe
      rw [cachedKvOwn_def c0]
      iframe
      iframe #
      ipureintro
      refine ⟨?_, Hpnn⟩
      simp [LeaseEntry.kv, hc, leaseCmpSign, ht]
  wp_apply hGC $$ [$tcmp] as tcmp
  · iframe %
  wp_apply hRes $$ [$HR]
  · iframe %
  ihave HΦ := HΦ $$ [Hhd Hkvs Hsl Hcap Hkv Hmore Hcount]
  · iframe; iframe #; ipureintro; exact Hrnn
  unfold leaseCmpHolds
  rw [← Hr]
  cases ho : m.op <;> simp only [CmpOp.code] <;> wp_auto
  · have : decide (r = W64 0) = CmpOp.eq.holds (sint.Z r) := by
      simp only [CmpOp.holds]; exact decide_w64_eq_zero r
    rw [this]; iexact HΦ
  · have : decide (sint.Z (W64 0) < sint.Z r) = CmpOp.gt.holds (sint.Z r) := by
      simp [CmpOp.holds]
    rw [this]; iexact HΦ
  · have : decide (sint.Z r < sint.Z (W64 0)) = CmpOp.lt.holds (sint.Z r) := by
      simp [CmpOp.holds]
    rw [this]; iexact HΦ
  · have : (!decide (r = W64 0)) = CmpOp.neq.holds (sint.Z r) := by
      simp only [CmpOp.holds, decide_w64_eq_zero r]; rfl
    rw [this]; iexact HΦ

end proof

end leasing
end EtcdGrove
end Perennial
