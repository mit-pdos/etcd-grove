/-
Proof of `Spec/go_etcd_io/etcd/client/v3/leasing/leaseCache__evalCmp.lean`. Lean-first (no Rocq
counterpart).
-/
module

public import Spec.go_etcd_io.etcd.client.v3.leasing.leaseCache__evalCmp
public import Spec.go_etcd_io.etcd.client.v3.leasing.evalCmp
public import Spec.go_etcd_io.etcd.client.v3.Cmp__GetCompare
public import Spec.go_etcd_io.etcd.client.v3.Cmp__KeyBytes
public import Spec.go_etcd_io.etcd.api.v3.etcdserverpb.Compare__GetRangeEnd
public import Proof.go_etcd_io.etcd.client.v3.leasing.InvLeaseCacheLemmas

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

theorem leaseCache.evalCmp.wp_proof
    (hGC : Cmp.GetCompare.spec (GF := GF) (hG := hG))
    (hRE : Compare.GetRangeEnd.spec (GF := GF) (hG := hG))
    (hKB : Cmp.KeyBytes.spec (GF := GF) (hG := hG))
    (hEval : _root_.Perennial.EtcdGrove.leasing.evalCmp.spec (GF := GF) (hG := hG)) :
    leaseCache.evalCmp.spec (GF := GF) (hG := hG) := by
  intro lc st dq sl ms
  wp_start as ⟨Hown, %Hwf, #Hcs⟩
  unfold cmpsSetAt
  icases Hcs with ⟨%cs, #Hsl, %Hlen, #Hall⟩
  ihave %Hsll := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  ihave IH : iprop(∃ (n : w64),
      "i" ∷ i_ptr ↦ n ∗ "Hown" ∷ lcOwn lc st dq ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (cs.length : Int)⌝ ∗
      "%Hev" ∷ ⌜leaseEvalCmps st ms = leaseEvalCmps st (ms.drop (sint.nat n))⌝) $$ [i Hown]
  · iexists W64 0
    simp only [named]
    iframe
    ipureintro; constructor
    · constructor <;> word
    · rfl
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.nat n < cs.length := by word
    obtain ⟨c, Hci⟩ : ∃ c, cs[sint.nat n]? = some c := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have Hltm : sint.nat n < ms.length := by rw [← Hlen]; exact Hlt
    obtain ⟨m, Hmi⟩ : ∃ m, ms[sint.nat n]? = some m := ⟨_, List.getElem?_eq_getElem Hltm⟩
    have Hdrop : ms.drop (sint.nat n) = m :: ms.drop (sint.nat n + 1) := by
      rw [List.drop_eq_getElem_cons Hltm]
      rw [List.getElem?_eq_getElem Hltm] at Hmi
      cases Hmi; rfl
    have Hbnd : 0 ≤ sint.Z n ∧ sint.Z n < sint.Z sl.len := ⟨Hn.1, by word⟩
    simp only [Hbnd, _root_.and_self, ↓reduceIte]
    wp_apply wp_load_slice_index sl (sint.Z n) cs DFrac.discard c Hn.1 $$ [Hsl] as -
    · iframe #; ipureintro; exact Hci
    ihave #Hat := Hall $$ %(sint.nat n) %c %m %Hci %Hmi
    ihave #HatC := Hat
    iunfold cmpSetAt at Hat
    icases Hat with ⟨%Hcnn, %ksl, %esl, %u, #HR, #HT, #HK, #HKs, #HE, #HEs, #HU, #HUa, %Hunn⟩
    wp_apply hGC $$ [$cmp] as cmp
    · iframe %
    wp_apply hRE $$ [$HE]
    · iframe %
    ihave %Helen := ownSlice_len _ _ _ $$ HEs
    wp_if_destruct
    · have hre : m.rangeEnd ≠ [] := by
        intro h; rw [h] at Helen; simp at Helen; word
      wp_for_post
      iapply HΦ
      iframe
      ipureintro
      rw [Hev, Hdrop]
      simp [leaseEvalCmps, hre]
    have hre : m.rangeEnd = [] := by
      apply List.eq_nil_of_length_eq_zero; have := Helen.1; word
    wp_apply hKB $$ [$cmp $HK] as cmp
    · iframe %
    wp_apply wp_bytes_to_string ksl m.key DFrac.discard $$ [$HKs] as -
    rw [lcOwn_def]
    icases Hown with ⟨Hentries, Hemap, Hrv, Hrmap, Hhdr, #HhdrOk, Hents, #Hfrozen⟩
    wp_auto
    wp_apply wp_entries_lookup st _ m.key Hwf $$ [$Hemap] as Hemap
    cases hk : st.entries !! m.key with
    | none =>
      simp only [Option.map_none, Option.getD_none]
      wp_auto
      wp_for_post
      iapply HΦ
      iframe
      iframe #
      ipureintro
      rw [Hev, Hdrop]
      simp [leaseEvalCmps, hre, hk]
    | some e =>
      have hli : e.li ≠ null := Hwf.li_ne m.key e hk
      simp only [Option.map_some, Option.getD_some]
      icases (BigSepM.bigSepM_lookup_acc hk).1 $$ Hents with ⟨He, Hents⟩
      rw [entryOwn_def]
      icases He with ⟨%-, Hr, Hrev, Hwc, Hresp, #Hw⟩
      rw [decide_eq_false hli]
      wp_auto
      wp_apply hEval e dq c m $$ [$Hresp $HatC] as Hresp
      ihave Hents := Hents $$ [Hr Hrev Hwc Hresp]
      · iframe; iframe #; ipureintro; exact hli
      have Hev' : leaseEvalCmps st (ms.drop (sint.nat n)) =
          if leaseCmpHolds m e.kv then leaseEvalCmps st (ms.drop (sint.nat n + 1))
          else (false, true) := by
        rw [Hdrop]; simp [leaseEvalCmps, hre, hk]
      cases Hif : leaseCmpHolds m e.kv
      · wp_auto
        wp_for_post
        iapply HΦ
        iframe
        iframe #
        ipureintro
        rw [Hev, Hev']; simp [Hif]
      · wp_auto
        wp_for_post
        iframe
        iexists (n + W64 1)
        simp only [named]
        iframe
        iframe #
        ipureintro
        refine ⟨by constructor <;> word, ?_⟩
        rw [Hev, Hev']
        simp only [Hif, ↓reduceIte]
        congr 2; have := Hbnd.2; word
  · have hn : sint.nat n = ms.length := by rw [← Hlen]; word
    rw [hn, List.drop_length] at Hev
    iapply HΦ
    iframe
    ipureintro; rw [Hev]; rfl

end proof

end leasing
end EtcdGrove
end Perennial
