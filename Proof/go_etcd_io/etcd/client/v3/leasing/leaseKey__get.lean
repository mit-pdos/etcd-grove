/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseKey__get.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseKey__get
public import Spec.go_etcd_io.etcd.client.v3.leasing.copyKeyValue
public import Spec.go_etcd_io.etcd.client.v3.leasing.copyGetResponseMetadataOnly
public import Spec.go_etcd_io.etcd.client.v3.Op__IsCountOnly
public import Spec.go_etcd_io.etcd.client.v3.Op__MinModRev
public import Spec.go_etcd_io.etcd.client.v3.Op__MaxModRev
public import Spec.go_etcd_io.etcd.client.v3.Op__MinCreateRev
public import Spec.go_etcd_io.etcd.client.v3.Op__MaxCreateRev
public import Spec.go_etcd_io.etcd.client.v3.Op__IsKeysOnly

@[expose] public section

set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace leasing

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.client.v3.leasing go_etcd_io.etcd.api.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [EM : EtcdModel GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.client.v3.leasing.Assumptions]

theorem leaseKey.get.wp_proof
    (hcount : Op.IsCountOnly.spec (GF := GF) (hG := hG))
    (hminm : Op.MinModRev.spec (GF := GF) (hG := hG))
    (hmaxm : Op.MaxModRev.spec (GF := GF) (hG := hG))
    (hminc : Op.MinCreateRev.spec (GF := GF) (hG := hG))
    (hmaxc : Op.MaxCreateRev.spec (GF := GF) (hG := hG))
    (hkeys : Op.IsKeysOnly.spec (GF := GF) (hG := hG))
    (hmeta : copyGetResponseMetadataOnly.spec (GF := GF) (hG := hG))
    (hkv : copyKeyValue.spec (GF := GF) (hG := hG)) :
    leaseKey.get.spec (GF := GF) (hG := hG) := by
  intro lkp e dq1 dq2 opv o
  wp_start as ⟨Hlk, Hresp, Hop⟩
  ihave %Hlknn := typedPointsto_not_null $$ Hlk
  iStructNamed Hlk
  unfold opFullAt
  icases Hop with ⟨#Hat, #Hkey, %Hf, #Hval, #Hsort⟩
  unfold respOwn
  icases Hresp with ⟨%Hrnn, HH, #Hhdr, HK, HKs, Hcap, Hkvs, HM, HC⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ HKs
  simp only [LeaseEntry.lk]
  wp_auto
  cases hk : e.kvs with
  | nil =>
    rw [hk] at Hlen
    have : e.kvsSl.len = W64 0 := by simp at Hlen; word
    rw [decide_eq_true this]
    wp_auto
    wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
      as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
    · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
    iapply HΦ
    (try unfold cachedKvOwn)
    isplitl [response rev waitc]
    · iapply typedPointsto_combine _ _ _ Hlknn
      simp only [TypedPointsto.typedPointstoDef]
      iframe
    isplitl [Hresp]
    · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iexact Hresp
    unfold freshGetResp
    isplitr
    · ipureintro; exact Hrnn'
    iexists h, slice.nil, []
    simp only [List.map_nil]
    iframe
    iframe #
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    isplitl []
    · iapply BigSepL.bigSepL_nil.2; iempintro
    ipureintro
    simp [getResult, getEmpty, *]
  | cons c cs =>
    have hne : e.kvsSl.len ≠ W64 0 := by
      intro h0; have := Hlen.1; rw [hk, h0, show sint.nat (W64 0) = 0 from rfl] at this; simp at this
    rw [decide_eq_false hne]
    have hb0 : 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z e.kvsSl.len := by
      have := Hlen.1; rw [hk] at this; simp at this; constructor <;> word
    icases Hkvs with ⟨Hc, Hcs⟩
    unfold cachedKvOwn
    icases Hc with ⟨%Hcpnn, HcK, #HcKs, HcC, HcM, HcV, HcVal, #HcVs, HcL⟩
    wp_auto
    wp_apply hcount $$ [$op $Hat] as op
    cases hco : o.base.countOnly
    · wp_auto
      wp_apply hminm $$ [$op $Hat] as op
      simp only [hb0, _root_.and_self, ↓reduceIte]
      wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
        hb0.1 $$ [HKs] as HKs
      · iframe; ipureintro; rfl
      wp_if_destruct
      · ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
        · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
        wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
          as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
        · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
        iapply HΦ
        (try unfold cachedKvOwn)
        isplitl [response rev waitc]
        · iapply typedPointsto_combine _ _ _ Hlknn
          simp only [TypedPointsto.typedPointstoDef]
          iframe
        isplitl [Hresp]
        · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iexact Hresp
        unfold freshGetResp
        isplitr
        · ipureintro; exact Hrnn'
        iexists h, slice.nil, []
        simp only [List.map_nil]
        iframe
        iframe #
        isplitl []
        · iapply ownSlice_nil
        isplitl []
        · iapply ownSliceCap_nil
        isplitl []
        · iapply BigSepL.bigSepL_nil.2; iempintro
        ipureintro
        clear hmeta hkv hcount hminm hmaxm hminc hmaxc hkeys
        simp_all [getResult, getEmpty]
        all_goals (simp only [Int.lt_iff_add_one_le] at *; split <;> first | rfl | (exfalso; omega) | skip)
      · wp_apply hmaxm $$ [$op $Hat] as op
        by_cases hz : o.base.maxModRev = W64 0
        · rw [decide_eq_true hz]
          wp_auto
          wp_apply hminc $$ [$op $Hat] as op
          simp only [hb0, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
            hb0.1 $$ [HKs] as HKs
          · iframe; ipureintro; rfl
          wp_if_destruct
          · ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
            · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
            wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
              as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
            · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
            iapply HΦ
            (try unfold cachedKvOwn)
            isplitl [response rev waitc]
            · iapply typedPointsto_combine _ _ _ Hlknn
              simp only [TypedPointsto.typedPointstoDef]
              iframe
            isplitl [Hresp]
            · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iexact Hresp
            unfold freshGetResp
            isplitr
            · ipureintro; exact Hrnn'
            iexists h, slice.nil, []
            simp only [List.map_nil]
            iframe
            iframe #
            isplitl []
            · iapply ownSlice_nil
            isplitl []
            · iapply ownSliceCap_nil
            isplitl []
            · iapply BigSepL.bigSepL_nil.2; iempintro
            ipureintro
            clear hmeta hkv hcount hminm hmaxm hminc hmaxc hkeys
            simp_all [getResult, getEmpty]
            all_goals (simp only [Int.lt_iff_add_one_le] at *; split <;> first | rfl | (exfalso; omega) | skip)
          · wp_apply hmaxc $$ [$op $Hat] as op
            by_cases hz2 : o.base.maxCreateRev = W64 0
            · rw [decide_eq_true hz2]
              wp_auto
              ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
              · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
              wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
                as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
              · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
              unfold respOwn
              rw [hk]
              icases Hresp with ⟨%Hrnn, HH, #Hhdr, HK, HKs, Hcap, Hkvs, HM, HC⟩
              icases Hkvs with ⟨Hc, Hcs⟩
              wp_auto
              simp only [hb0, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
                hb0.1 $$ [HKs] as HKs
              · iframe; ipureintro; rfl
              wp_apply hkeys $$ [$op] as op
              · unfold opFullAt; iframe #; ipureintro; exact Hf
              wp_apply (hkv c dq2 o.keysOnly) $$ [$Hc] as %p' ⟨Hc, %c', %Hc', Hc'⟩
              wp_apply wp_slice_literal (l := [p'])
              isplitr
              · ipureintro; rfl
              iintro %zsl ⟨Hz, Hzcap⟩
              wp_auto
              iapply HΦ
              (try unfold cachedKvOwn)
              isplitl [response rev waitc]
              · iapply typedPointsto_combine _ _ _ Hlknn
                simp only [TypedPointsto.typedPointstoDef]
                iframe
              isplitl [HH HK HKs Hcap Hc Hcs HM HC]
              · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
              unfold freshGetResp
              isplitr
              · ipureintro; exact Hrnn'
              iexists h, _, [c']
              simp only [List.map_cons, List.map_nil]
              rw [Hc'.1]
              iframe
              iframe #
              iframe
              isplitl [Hc']
              · iapply (BigSepL.bigSepL_singleton).2; unfold cachedKvOwn; rw [Hc'.1]; iframe
              ipureintro
              have hge : ¬ getEmpty o.base (c :: cs) = true := by
                simp only [getEmpty, decide_eq_true_eq, not_or, not_and, Int.not_lt]
                refine ⟨by simp [hco], by omega, ?_, by omega, ?_⟩ <;>
                  first | (intro hh; exact absurd hz hh) | (intro hh; exact absurd hz2 hh) |
                    (intro hh; omega)
              rw [show getResult o e = some (if o.keysOnly then { c.kv with value := [] } else c.kv) by
                unfold getResult; rw [hk, ite_eq_right hge]; rfl]
              simp only [List.map_cons, List.map_nil, Hc'.2, Option.toList_some]
            · rw [decide_eq_false hz2]
              wp_auto
              wp_apply hmaxc $$ [$op $Hat] as op
              simp only [hb0, _root_.and_self, ↓reduceIte]
              wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
                hb0.1 $$ [HKs] as HKs
              · iframe; ipureintro; rfl
              ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
              · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
              wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
                as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
              · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
              unfold respOwn
              rw [hk]
              icases Hresp with ⟨%Hrnn, HH, #Hhdr, HK, HKs, Hcap, Hkvs, HM, HC⟩
              icases Hkvs with ⟨Hc, Hcs⟩
              wp_if_destruct
              · ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [Hc Hcs]
                · iframe
                iapply HΦ
                (try unfold cachedKvOwn)
                isplitl [response rev waitc]
                · iapply typedPointsto_combine _ _ _ Hlknn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
                isplitl [HH HK HKs Hcap Hkvs HM HC]
                · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
                unfold freshGetResp
                isplitr
                · ipureintro; exact Hrnn'
                iexists h, slice.nil, []
                simp only [List.map_nil]
                iframe
                iframe #
                isplitl []
                · iapply ownSlice_nil
                isplitl []
                · iapply ownSliceCap_nil
                isplitl []
                · iapply BigSepL.bigSepL_nil.2; iempintro
                ipureintro
                clear hmeta hkv hcount hminm hmaxm hminc hmaxc hkeys
                simp_all [getResult, getEmpty]
                all_goals (simp only [Int.lt_iff_add_one_le] at *; split <;> first | rfl | (exfalso; omega) | skip)
              · simp only [hb0, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
                  hb0.1 $$ [HKs] as HKs
                · iframe; ipureintro; rfl
                wp_apply hkeys $$ [$op] as op
                · unfold opFullAt; iframe #; ipureintro; exact Hf
                wp_apply (hkv c dq2 o.keysOnly) $$ [$Hc] as %p' ⟨Hc, %c', %Hc', Hc'⟩
                wp_apply wp_slice_literal (l := [p'])
                isplitr
                · ipureintro; rfl
                iintro %zsl ⟨Hz, Hzcap⟩
                wp_auto
                iapply HΦ
                (try unfold cachedKvOwn)
                isplitl [response rev waitc]
                · iapply typedPointsto_combine _ _ _ Hlknn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
                isplitl [HH HK HKs Hcap Hc Hcs HM HC]
                · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
                unfold freshGetResp
                isplitr
                · ipureintro; exact Hrnn'
                iexists h, _, [c']
                simp only [List.map_cons, List.map_nil]
                rw [Hc'.1]
                iframe
                iframe #
                iframe
                isplitl [Hc']
                · iapply (BigSepL.bigSepL_singleton).2; unfold cachedKvOwn; rw [Hc'.1]; iframe
                ipureintro
                have hge : ¬ getEmpty o.base (c :: cs) = true := by
                  simp only [getEmpty, decide_eq_true_eq, not_or, not_and, Int.not_lt]
                  refine ⟨by simp [hco], by omega, ?_, by omega, ?_⟩ <;>
                    first | (intro hh; exact absurd hz hh) | (intro hh; exact absurd hz2 hh) |
                      (intro hh; omega)
                rw [show getResult o e = some (if o.keysOnly then { c.kv with value := [] } else c.kv) by
                  unfold getResult; rw [hk, ite_eq_right hge]; rfl]
                simp only [List.map_cons, List.map_nil, Hc'.2, Option.toList_some]
        · rw [decide_eq_false hz]
          wp_auto
          wp_apply hmaxm $$ [$op $Hat] as op
          simp only [hb0, _root_.and_self, ↓reduceIte]
          wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
            hb0.1 $$ [HKs] as HKs
          · iframe; ipureintro; rfl
          wp_if_destruct
          · ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
            · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
            wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
              as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
            · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
            iapply HΦ
            (try unfold cachedKvOwn)
            isplitl [response rev waitc]
            · iapply typedPointsto_combine _ _ _ Hlknn
              simp only [TypedPointsto.typedPointstoDef]
              iframe
            isplitl [Hresp]
            · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iexact Hresp
            unfold freshGetResp
            isplitr
            · ipureintro; exact Hrnn'
            iexists h, slice.nil, []
            simp only [List.map_nil]
            iframe
            iframe #
            isplitl []
            · iapply ownSlice_nil
            isplitl []
            · iapply ownSliceCap_nil
            isplitl []
            · iapply BigSepL.bigSepL_nil.2; iempintro
            ipureintro
            clear hmeta hkv hcount hminm hmaxm hminc hmaxc hkeys
            simp_all [getResult, getEmpty]
            all_goals (simp only [Int.lt_iff_add_one_le] at *; split <;> first | rfl | (exfalso; omega) | skip)
          · wp_apply hminc $$ [$op $Hat] as op
            simp only [hb0, _root_.and_self, ↓reduceIte]
            wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
              hb0.1 $$ [HKs] as HKs
            · iframe; ipureintro; rfl
            wp_if_destruct
            · ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
              · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
              wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
                as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
              · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
              iapply HΦ
              (try unfold cachedKvOwn)
              isplitl [response rev waitc]
              · iapply typedPointsto_combine _ _ _ Hlknn
                simp only [TypedPointsto.typedPointstoDef]
                iframe
              isplitl [Hresp]
              · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iexact Hresp
              unfold freshGetResp
              isplitr
              · ipureintro; exact Hrnn'
              iexists h, slice.nil, []
              simp only [List.map_nil]
              iframe
              iframe #
              isplitl []
              · iapply ownSlice_nil
              isplitl []
              · iapply ownSliceCap_nil
              isplitl []
              · iapply BigSepL.bigSepL_nil.2; iempintro
              ipureintro
              clear hmeta hkv hcount hminm hmaxm hminc hmaxc hkeys
              simp_all [getResult, getEmpty]
              all_goals (simp only [Int.lt_iff_add_one_le] at *; split <;> first | rfl | (exfalso; omega) | skip)
            · wp_apply hmaxc $$ [$op $Hat] as op
              by_cases hz2 : o.base.maxCreateRev = W64 0
              · rw [decide_eq_true hz2]
                wp_auto
                ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
                · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
                wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
                  as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
                · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
                unfold respOwn
                rw [hk]
                icases Hresp with ⟨%Hrnn, HH, #Hhdr, HK, HKs, Hcap, Hkvs, HM, HC⟩
                icases Hkvs with ⟨Hc, Hcs⟩
                wp_auto
                simp only [hb0, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
                  hb0.1 $$ [HKs] as HKs
                · iframe; ipureintro; rfl
                wp_apply hkeys $$ [$op] as op
                · unfold opFullAt; iframe #; ipureintro; exact Hf
                wp_apply (hkv c dq2 o.keysOnly) $$ [$Hc] as %p' ⟨Hc, %c', %Hc', Hc'⟩
                wp_apply wp_slice_literal (l := [p'])
                isplitr
                · ipureintro; rfl
                iintro %zsl ⟨Hz, Hzcap⟩
                wp_auto
                iapply HΦ
                (try unfold cachedKvOwn)
                isplitl [response rev waitc]
                · iapply typedPointsto_combine _ _ _ Hlknn
                  simp only [TypedPointsto.typedPointstoDef]
                  iframe
                isplitl [HH HK HKs Hcap Hc Hcs HM HC]
                · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
                unfold freshGetResp
                isplitr
                · ipureintro; exact Hrnn'
                iexists h, _, [c']
                simp only [List.map_cons, List.map_nil]
                rw [Hc'.1]
                iframe
                iframe #
                iframe
                isplitl [Hc']
                · iapply (BigSepL.bigSepL_singleton).2; unfold cachedKvOwn; rw [Hc'.1]; iframe
                ipureintro
                have hge : ¬ getEmpty o.base (c :: cs) = true := by
                  simp only [getEmpty, decide_eq_true_eq, not_or, not_and, Int.not_lt]
                  refine ⟨by simp [hco], by omega, ?_, by omega, ?_⟩ <;>
                    first | (intro hh; exact absurd hz hh) | (intro hh; exact absurd hz2 hh) |
                      (intro hh; omega)
                rw [show getResult o e = some (if o.keysOnly then { c.kv with value := [] } else c.kv) by
                  unfold getResult; rw [hk, ite_eq_right hge]; rfl]
                simp only [List.map_cons, List.map_nil, Hc'.2, Option.toList_some]
              · rw [decide_eq_false hz2]
                wp_auto
                wp_apply hmaxc $$ [$op $Hat] as op
                simp only [hb0, _root_.and_self, ↓reduceIte]
                wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
                  hb0.1 $$ [HKs] as HKs
                · iframe; ipureintro; rfl
                ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
                · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
                wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
                  as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
                · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
                unfold respOwn
                rw [hk]
                icases Hresp with ⟨%Hrnn, HH, #Hhdr, HK, HKs, Hcap, Hkvs, HM, HC⟩
                icases Hkvs with ⟨Hc, Hcs⟩
                wp_if_destruct
                · ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [Hc Hcs]
                  · iframe
                  iapply HΦ
                  (try unfold cachedKvOwn)
                  isplitl [response rev waitc]
                  · iapply typedPointsto_combine _ _ _ Hlknn
                    simp only [TypedPointsto.typedPointstoDef]
                    iframe
                  isplitl [HH HK HKs Hcap Hkvs HM HC]
                  · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
                  unfold freshGetResp
                  isplitr
                  · ipureintro; exact Hrnn'
                  iexists h, slice.nil, []
                  simp only [List.map_nil]
                  iframe
                  iframe #
                  isplitl []
                  · iapply ownSlice_nil
                  isplitl []
                  · iapply ownSliceCap_nil
                  isplitl []
                  · iapply BigSepL.bigSepL_nil.2; iempintro
                  ipureintro
                  clear hmeta hkv hcount hminm hmaxm hminc hmaxc hkeys
                  simp_all [getResult, getEmpty]
                  all_goals (simp only [Int.lt_iff_add_one_le] at *; split <;> first | rfl | (exfalso; omega) | skip)
                · simp only [hb0, _root_.and_self, ↓reduceIte]
                  wp_apply wp_load_slice_index e.kvsSl (sint.Z (W64 0)) ((c :: cs).map CachedKv.p) dq2 c.p
                    hb0.1 $$ [HKs] as HKs
                  · iframe; ipureintro; rfl
                  wp_apply hkeys $$ [$op] as op
                  · unfold opFullAt; iframe #; ipureintro; exact Hf
                  wp_apply (hkv c dq2 o.keysOnly) $$ [$Hc] as %p' ⟨Hc, %c', %Hc', Hc'⟩
                  wp_apply wp_slice_literal (l := [p'])
                  isplitr
                  · ipureintro; rfl
                  iintro %zsl ⟨Hz, Hzcap⟩
                  wp_auto
                  iapply HΦ
                  (try unfold cachedKvOwn)
                  isplitl [response rev waitc]
                  · iapply typedPointsto_combine _ _ _ Hlknn
                    simp only [TypedPointsto.typedPointstoDef]
                    iframe
                  isplitl [HH HK HKs Hcap Hc Hcs HM HC]
                  · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
                  unfold freshGetResp
                  isplitr
                  · ipureintro; exact Hrnn'
                  iexists h, _, [c']
                  simp only [List.map_cons, List.map_nil]
                  rw [Hc'.1]
                  iframe
                  iframe #
                  iframe
                  isplitl [Hc']
                  · iapply (BigSepL.bigSepL_singleton).2; unfold cachedKvOwn; rw [Hc'.1]; iframe
                  ipureintro
                  have hge : ¬ getEmpty o.base (c :: cs) = true := by
                    simp only [getEmpty, decide_eq_true_eq, not_or, not_and, Int.not_lt]
                    refine ⟨by simp [hco], by omega, ?_, by omega, ?_⟩ <;>
                      first | (intro hh; exact absurd hz hh) | (intro hh; exact absurd hz2 hh) |
                        (intro hh; omega)
                  rw [show getResult o e = some (if o.keysOnly then { c.kv with value := [] } else c.kv) by
                    unfold getResult; rw [hk, ite_eq_right hge]; rfl]
                  simp only [List.map_cons, List.map_nil, Hc'.2, Option.toList_some]
    · wp_auto
      ihave Hkvs : ([∗list] c ∈ c :: cs, cachedKvOwn c dq2) $$ [HcK HcC HcM HcV HcVal HcL Hcs]
      · iframe; unfold cachedKvOwn; iframe; iframe #; (try (ipureintro; exact Hcpnn))
      wp_apply (hmeta e dq2) $$ [HH Hhdr HK HKs Hcap Hkvs HM HC]
        as %r ⟨Hresp, %Hrnn', %h, HrH, #Hrh, HrK, HrM, HrC⟩
      · (try unfold respOwn); (try rw [hk]); iframe; iframe #; (try (ipureintro; first | exact Hrnn | exact ⟨Hrnn, Hcpnn⟩))
      iapply HΦ
      (try unfold cachedKvOwn)
      isplitl [response rev waitc]
      · iapply typedPointsto_combine _ _ _ Hlknn
        simp only [TypedPointsto.typedPointstoDef]
        iframe
      isplitl [Hresp]
      · unfold respOwn; rw [hk]; (try unfold cachedKvOwn); iexact Hresp
      unfold freshGetResp
      isplitr
      · ipureintro; exact Hrnn'
      iexists h, slice.nil, []
      simp only [List.map_nil]
      iframe
      iframe #
      isplitl []
      · iapply ownSlice_nil
      isplitl []
      · iapply ownSliceCap_nil
      isplitl []
      · iapply BigSepL.bigSepL_nil.2; iempintro
      ipureintro
      clear hmeta hkv hcount hminm hmaxm hminc hmaxc hkeys
      simp_all [getResult, getEmpty]
      all_goals (simp only [Int.lt_iff_add_one_le] at *; split <;> first | rfl | (exfalso; omega) | skip)

end proof

end leasing
end EtcdGrove
end Perennial
