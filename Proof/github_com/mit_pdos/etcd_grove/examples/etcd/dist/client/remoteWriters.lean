/-
Proof of `remoteWriters.spec`. Lean-first (no Rocq counterpart); #50 N10a.

Writer `c`'s input `tried[c*nops:(c+1)*nops]` is a subslice of the read-only Puts (`writerPuts`),
so it describes `(n, writerPuts trs nops c)` at the writers' wire (`writerWire`: its encoding fits,
`kvsBytes_length_le`), and the adapter's invariant, the start's changes seen and the Puts' facts are
the service's `wP`. `reportAll` at the writer service (`writerSvc`: the share's `svcAddr` at the
global part is the machine's, `svcAddr_writerSvc`), each writer's continuation its `wQ`; then the
answering writers' logs are appended, each record with its `okFactK`.
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.remoteWriters
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.reportAll
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerCodec
public import Spec.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.writerAttempt
public import Proof.github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.RemoteWritersDefs

@[expose] public section

set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_dist_client

open Iris Iris.BI Iris.ProofMode Net client
open github_com.mit_pdos.etcd_grove.examples.lib.remote
open etcd_dist etcdstart

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt idIssueExt] [HasExt netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.dist.client.Assumptions]

/-- Writer `c`'s answer, as `reportAll` returns it at the writer service. -/
def wrRes (Γ : DistView) (n : WN) (ps : Nat → List wkv) (outs oks : GoSlice) (c : Nat) : IProp GF :=
  iprop(∃ (v : GoInterface) (ok : Bool),
    typedPointsto (sliceIndexRef GoInterface ((c : Nat) : Int) outs) v (DFrac.own 1) ∗
    typedPointsto (sliceIndexRef Bool ((c : Nat) : Int) oks) ok (DFrac.own 1) ∗
    (⌜ok = false⌝ ∨ (⌜ok = true⌝ ∗ ((∃ o, (∃ sl : GoSlice, ⌜v = interface.mkOk
        (go.GoType.SliceType github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.PutRec.ty) #sl ∧
        (recsBytes o).length < 2 ^ 63⌝ ∗ sl ↦*□ o) ∗
      wQ (Gg := hG.goose_globalGS) Γ (n, ps c) o) ∨ False))))


theorem remoteWriters.wp_proof
    (wp_reportAll : reportAll.spec (GF := GF) (hG := hG))
    (wp_writerCodec : writerCodec.spec (GF := GF) (hG := hG))
    (wp_writerAttempt : writerAttempt.spec (GF := GF) (hG := hG)) :
    remoteWriters.spec (GF := GF) (hG := hG) := by
  intro π ρ nodes tsl ns trs nops Γ n Htb Hn0 Hn56 Hlen Hps
  wp_start as ⟨Htok, #Hns, #Htr, Hws, #Hkm, #Hlb⟩
  ihave %Hnl := ownSlice_len _ _ _ $$ Hns
  ihave %Htl := ownSlice_len _ _ _ $$ Htr
  ihave %Htwf := ownSlice_wf _ _ _ $$ Htr
  have hmZ : ((sint.nat nops : Nat) : Int) = sint.Z nops := by word
  have hNZ : (ns.length : Int) = sint.Z nodes.len := by rw [Hnl.1]; have := Hnl.2; word
  have htrs : (trs.length : Int) = ns.length * (sint.nat nops) := by rw [Hlen, hmZ]
  have htlen : (trs.length : Int) = sint.Z tsl.len := by rw [Htl.1]; word
  (try wp_auto)
  wp_apply (wp_slice_make2 (V := GoInterface) nodes.len) as %insl ⟨Hins, -⟩
  · ipureintro; exact Hnl.2
  (try wp_auto)
  -- the inputs: `ins[c] = tried[c*nops : (c+1)*nops]`
  ihave IH : (∃ (k cv : w64) (xsL : List GoInterface),
      "i" ∷ i_ptr ↦ k ∗ "c" ∷ c_ptr ↦ cv ∗ "Hins" ∷ insl ↦* xsL ∗
      "#Hx" ∷ (□ ∀ j : Nat, ⌜j < sint.nat k⌝ -∗ ∃ x, ⌜xsL[j]? = some x⌝ ∗
        (writerWire (GF := GF) WN).ivAt x (n, writerPuts trs (sint.nat nops) j)) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z nodes.len ∧ xsL.length = ns.length⌝ : IProp GF)
    $$ [i c Hins]
  · iexists W64 0, _, _
    iframe
    isplitr
    · iintro !> %j %hj
      exfalso; have : sint.nat (W64 0) = 0 := rfl; omega
    ipureintro
    refine ⟨by decide, Hnl.2, ?_⟩
    simp only [List.length_replicate]; exact Hnl.1.symm
  wp_for IH
  wp_if_destruct
  · have Hlt : sint.Z k < sint.Z nodes.len := by simpa using Hif
    have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    have hkN : sint.nat k < ns.length := by omega
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z nodes.len := ⟨Hk.1, Hlt⟩
    obtain ⟨a, ha⟩ : ∃ a, ns[sint.nat k]? = some a := ⟨_, List.getElem?_eq_getElem hkN⟩
    simp only [hb, _root_.and_self, ↓reduceIte]
    wp_apply (wp_load_slice_index nodes (sint.Z k) ns DFrac.discard a Hk.1) $$ [] as -
    · iframe #; ipureintro; exact ha
    (try wp_auto)
    have hNm : (ns.length : Int) * sint.Z nops < 2 ^ 63 := by
      rw [← hmZ, ← htrs, htlen]; have := Htwf.2; word
    obtain ⟨hlo, hhi, e1, e2, h1⟩ := writer_bounds k nops ns.length Hk.1 (by omega) Hn0 hNm
    have h0 : 0 ≤ sint.Z k * sint.Z nops := Int.mul_nonneg Hk.1 Hn0
    have hsl : 0 ≤ sint.Z (k * nops) ∧ sint.Z (k * nops) ≤ sint.Z ((k + W64 1) * nops) ∧
        sint.Z ((k + W64 1) * nops) ≤ sint.Z tsl.cap := by
      refine ⟨by omega, by omega, ?_⟩
      have : sint.Z ((k + W64 1) * nops) ≤ sint.Z tsl.len := by
        rw [hhi, ← htlen, htrs, hmZ]; omega
      omega
    simp only [hsl, _root_.and_self, ↓reduceIte]
    (try wp_auto)
    ihave %Hil := ownSlice_len _ _ _ $$ Hins
    have hil : sint.Z insl.len = (ns.length : Int) := by have := Hil.1; rw [Hk.2.2] at this; word
    have hbi : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z insl.len := ⟨Hk.1, by omega⟩
    simp only [hbi, _root_.and_self, ↓reduceIte]
    wp_apply (wp_store_slice_index insl (sint.Z k) xsL _) $$ [Hins] as Hins
    · iframe; ipureintro; exact ⟨Hk.1, by omega⟩
    wp_for_post
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    have hlen' : sint.Z ((k + W64 1) * nops) ≤ sint.Z tsl.len := by
      rw [hhi, ← htlen, htrs, hmZ]; omega
    ihave Hsub := (ownSlice_slice (k * nops) ((k + W64 1) * nops) tsl DFrac.discard trs
      ⟨hsl.1, hsl.2.1, hlen'⟩).1 $$ Htr
    icases Hsub with ⟨-, #Hsub, -⟩
    iframe
    iexists (k + W64 1), k, _
    iframe
    isplitr
    · iintro !> %j %hj
      rw [hk1] at hj
      by_cases hjk : j = sint.nat k
      · subst hjk
        iexists _
        isplitr
        · ipureintro
          rw [show (sint.Z k).toNat = sint.nat k from rfl, List.getElem?_set_self (by omega)]
        rw [writerWire_ivAt]
        iexists _
        isplitr
        · ipureintro
          refine ⟨rfl, ?_⟩
          have := kvsBytes_length_le (writerPuts trs (sint.nat nops) (sint.nat k))
            (fun p hp => (Hps p (mem_writerPuts hp)).2)
          have := writerPuts_length_le trs (sint.nat nops) (sint.nat k)
          have hm56 : sint.nat nops < 2 ^ 56 := by omega
          simp only
          omega
        rw [e1, e2]
        simp only [writerPuts]
        iexact Hsub
      · ihave Hj := Hx $$ %j []
        · ipureintro; omega
        icases Hj with ⟨%x, %hx, #Hj⟩
        iexists x
        iframe Hj
        ipureintro
        rw [List.getElem?_set]
        have : ¬ (sint.Z k).toNat = j := by
          show ¬ sint.nat k = j; omega
        simp only [this, ↓reduceIte]
        exact hx
    ipureintro
    refine ⟨by word, by word, by rw [List.length_set]; exact Hk.2.2⟩
  -- the inputs done
  have Hkn : sint.nat k = ns.length := by
    have : ¬ sint.Z k < sint.Z nodes.len := by simpa using Hif
    have : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    omega
  try iclear i
  try iclear c
  imod ownSlice_persist _ _ _ $$ Hins with #Hins
  (try wp_auto)
  wp_apply (wp_writerCodec WN (wP (Gg := hG.goose_globalGS) Γ) (wQ (Gg := hG.goose_globalGS) Γ))
    as %cd #Hcd
  (try wp_auto)
  wp_apply (wp_writerAttempt nops) as %d -
  (try wp_auto)
  iunfold writersShare at Hws
  icases Hws with ⟨#Hmap, Hl⟩
  ihave Hl := bigSepL_range_of ns (fun _ a => iprop(svcAddr (Gg := hG.goose_globalGS)
    (writerSvcG (Gg := hG.goose_globalGS) Γ) a ∗ budUnit (Gg := hG.goose_globalGS) a)) $$ Hl
  wp_apply (wp_reportAll (writerSvc Γ) nodes insl ns xsL (fun c => (n, writerPuts trs (sint.nat nops) c))
      (fun c => wQ (Gg := hG.goose_globalGS) Γ (n, writerPuts trs (sint.nat nops) c)) cd d Htb Hk.2.2)
      $$ [Htok Hl] as %outs %oks ⟨Htok', %Hlo, Hres⟩
  · iframe #
    iframe Htok
    iapply (BigSepL.bigSepL_impl (PROP := IProp GF)) $$ Hl
    iintro !> %j %c %hc ⟨%a, %ha, #Ha, Hbud⟩
    have hcN : c < ns.length := List.mem_range.1 (List.mem_of_getElem? hc)
    ihave Hj := Hx $$ %c []
    · ipureintro; omega
    icases Hj with ⟨%x, %hx, #Hj⟩
    iexists a, x
    isplitr
    · ipureintro; exact ⟨ha, hx⟩
    rw [← svcAddr_writerSvc]
    iframe Ha Hbud Hj
    isplitr
    · iunfold wP
      simp only [← kmInv_eq_G]
      iframe Hkm Hlb
      ipureintro
      exact ⟨fun p hp => Hps p (mem_writerPuts hp),
        by have := writerPuts_length_le trs (sint.nat nops) c; omega⟩
    · iintro %o Ho
      iexact Ho
  -- the answering writers' logs: `all = append(all, outs[c].([]etcdstart.PutRec)...)`
  (try wp_auto)
  have H00 : sint.nat (W64 0) = 0 := rfl
  ihave Hres : ([∗list] c ∈ List.range' (sint.nat (W64 0)) (ns.length - sint.nat (W64 0)),
      wrRes Γ n (writerPuts trs (sint.nat nops)) outs oks c : IProp GF) $$ [Hres]
  · rw [H00, Nat.sub_zero, ← List.range_eq_range']
    unfold wrRes
    iexact Hres
  ihave Hnil := ownSlice_nil (V := wrec) (GF := GF) (DFrac.own 1)
  ihave Hncap := ownSliceCap_nil (V := wrec) (GF := GF)
  ihave IH2 : (∃ (k cv : w64) (asl : GoSlice) (acc : List wrec),
      "i" ∷ i_ptr ↦ k ∗ "c" ∷ c_ptr ↦ cv ∗ "all" ∷ all_ptr ↦ asl ∗ "Hacc" ∷ asl ↦* acc ∗
      "Hcap" ∷ ownSliceCap wrec asl (DFrac.own 1) ∗
      "#Hoks" ∷ (□ [∗list] p ∈ acc, etcd_partition.okFactK (kmOf Γ n) p) ∗
      "Hres" ∷ ([∗list] c ∈ List.range' (sint.nat k) (ns.length - sint.nat k),
        wrRes Γ n (writerPuts trs (sint.nat nops)) outs oks c) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ sint.Z nodes.len⌝ : IProp GF)
    $$ [i c all Hnil Hncap Hres]
  · iexists W64 0, _, slice.nil, []
    iframe i c all
    unfold named
    isplitl [Hnil]
    · iexact Hnil
    isplitl [Hncap]
    · iexact Hncap
    isplitr
    · iintro !>
      iapply (BigSepL.bigSepL_nil (PROP := IProp GF)).2
      iempintro
    isplitl [Hres]
    · iexact Hres
    ipureintro
    exact ⟨by decide, Hnl.2⟩
  wp_for IH2
  wp_if_destruct
  · have Hlt : sint.Z k < sint.Z nodes.len := by simpa [intoVal_eq_iff] using Hif
    have hkk : ((sint.nat k : Nat) : Int) = sint.Z k := by word
    have hkN : sint.nat k < ns.length := by omega
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z nodes.len := ⟨Hk.1, Hlt⟩
    obtain ⟨a, ha⟩ : ∃ a, ns[sint.nat k]? = some a := ⟨_, List.getElem?_eq_getElem hkN⟩
    (try simp only [hb, _root_.and_self, ↓reduceIte])
    wp_apply (wp_load_slice_index nodes (sint.Z k) ns DFrac.discard a Hk.1) $$ [] as -
    · iframe #; ipureintro; exact ha
    (try wp_auto)
    rw [show ns.length - sint.nat k = (ns.length - (sint.nat k + 1)) + 1 by omega, List.range'_succ]
    icases (BigSepL.bigSepL_cons (PROP := IProp GF)).1 $$ Hres with ⟨Hc, Hres⟩
    iunfold wrRes at Hc
    icases Hc with ⟨%v, %ok, Hv, Hok, Hq⟩
    rw [hkk]
    have hbo : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z oks.len := ⟨Hk.1, by rw [Hlo.2]; omega⟩
    have hbu : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z outs.len := ⟨Hk.1, by rw [Hlo.1]; omega⟩
    simp only [hbo, _root_.and_self, ↓reduceIte]
    (try wp_auto)
    have hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    icases Hq with (%Hf | ⟨%Ht, (⟨%o, Ho, HQ⟩ | %Hu)⟩)
    · -- no answer
      subst Hf
      (try wp_auto)
      wp_for_post
      iframe
      iexists (k + W64 1), k, asl, acc
      rw [hk1]
      iframe
      iframe #
      ipureintro
      exact ⟨by word, by word⟩
    · -- a log
      subst Ht
      iunfold wQ at HQ
      icases HQ with #HQ
      icases Ho with ⟨%sl, ⟨%Hvs, -⟩, #Hsl⟩
      subst Hvs
      (try wp_auto)
      (try simp only [hbu, _root_.and_self, ↓reduceIte])
      (try wp_auto)
      wp_apply (wp_slice_append asl acc sl o DFrac.discard) $$ [Hacc Hcap] as %asl' ⟨Hacc, Hcap, -⟩
      · iframe Hacc Hcap Hsl
      (try wp_auto)
      wp_for_post
      iframe
      iexists (k + W64 1), k, asl', acc ++ o
      rw [hk1]
      iframe
      isplitr
      · iintro !>
        iapply (BigSepL.bigSepL_append (PROP := IProp GF)).2
        iframe Hoks
        simp only [okFactK_eq_G]
        iexact HQ
      ipureintro
      exact ⟨by word, by word⟩
    · exact Hu.elim
  · have Hge : ¬ sint.Z k < sint.Z nodes.len := by simpa [intoVal_eq_iff] using Hif
    (try wp_auto)
    iapply HΦ
    iframe Htok'
    iexists acc
    iframe Hacc
    iexact Hoks

end proof

end etcd_dist_client
end EtcdGrove
end Perennial
