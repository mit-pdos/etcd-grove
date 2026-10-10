/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/txnLeasing__revokeFallback.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.txnLeasing__revokeFallback
public import Spec.go_etcd_io.etcd.client.v3.leasing.leasingKV__revokeLeaseKvs
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.ResponseOp__GetResponseRange

@[expose] public section

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

instance rangeKvsRO_persistent (p : Loc) (kvs : List EtcdKv) :
    Persistent (rangeKvsRO (GF := GF) p kvs) := by
  unfold rangeKvsRO; infer_instance

theorem txnLeasing.revokeFallback.wp_proof
    (hGRR : EtcdGrove.ResponseOp.GetResponseRange.spec (GF := GF) (hG := hG))
    (hRLK : leasingKV.revokeLeaseKvs.spec (GF := GF) (hG := hG)) :
    txnLeasing.revokeFallback.spec (GF := GF) (hG := hG) := by
  intro txn lkv γ pfx ctx cs dq sl ps kvss
  wp_start as ⟨Hl, Hc, #Hlkv, Hrd, #Hsr, #Hctx, #Hcc, #Hsl, %Hlen, #Hall⟩
  ihave %Hslen := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64) (p0 : Loc),
      "i" ∷ i_ptr ↦ n ∗ "resp" ∷ resp_ptr ↦ p0 ∗ "Hl" ∷ structFieldRef txnLeasing go!"lkv" txn ↦{dq} lkv ∗
      "Hc" ∷ structFieldRef txnLeasing go!"ctx" txn ↦{dq} GoInterface.ok ctx ∗ "Hrd" ∷ lkvReader lkv γ pfx ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (ps.length : Int)⌝) $$ [i resp Hl Hc Hrd]
  · iexists W64 0, _
    simp only [named]
    iframe
    ipureintro; constructor <;> word
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < ps.length := by word
    obtain ⟨p, Hpi⟩ : ∃ p, ps[sint.nat n]? = some p := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) ps DFrac.discard p Hn.1 $$ [Hsl] as -
    · iframe Hsl; ipureintro; exact Hpi
    ihave ⟨%kvs, %Hk, #Hro⟩ := (BigSepL.bigSepL_lookup (Φ := fun i p => iprop(∃ kvs, ⌜kvss[i]? = some kvs⌝ ∗ rangeKvsRO (GF := GF) p kvs)) Hpi) $$ Hall
    iunfold rangeKvsRO at Hro
    icases Hro with ⟨%w, %rr, %ksl, %kps, %Hnn, #Hu, #Hw, #Hk, #Hkps, #Hkv⟩
    ihave #Hpbi : isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.api.v3.etcdserverpb $$ []
    · iPkgInit
    wp_apply hGRR p w rr $$ [$Hpbi $Hu $Hw]
    · ipureintro; exact Hnn.1
    wp_apply hRLK $$ [$Hlkv $Hrd $Hsr $Hctx $Hcc $Hkps $Hkv] as %mr %err ⟨Hrd, %Herr⟩
    cases err with
    | nil =>
      wp_auto
      wp_for_post
      iframe
      iexists n + W64 1, p
      simp only [named]
      iframe
      ipureintro; constructor <;> word
    | ok e =>
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
  · iapply HΦ
    iframe

end proof

end leasing
end EtcdGrove
end Perennial
