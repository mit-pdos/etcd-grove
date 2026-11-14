/- Lean-first (no Rocq counterpart). The proof of `decodeOracle` (W4c U5): the decoder over the
encoding's bytes (at most 1 GiB, `tOrSmall`), each field read back by `decoder.u64`/`hs`/`ops`; `ok`
stays set, so the loops run the counts read. -/
module

public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decodeOracle
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__ops
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__hs
public import LinuxFs.Spec.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__u64
public import LinuxFs.Proof.github_com.mit_pdos.etcd_grove.examples.etcd.wal.decoder__ops

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace etcd_wal

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open github_com.mit_pdos.etcd_grove.examples.etcd.wal

section pure
variable [GooseExts]

/-- A candidate's bytes in `encodeOracle`. -/
def tCandEnc (c : TCand) : List w8 := tOpsBytes c.h ++ tU64 c.unl ++ tU64 c.pur

theorem tCandEnc_length (c : TCand) : 8 ≤ (tCandEnc c).length := by
  simp [tCandEnc, tOpsBytes, tU64_length]

end pure

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.etcd.wal.Assumptions]

theorem decodeOracle.wp_proof (wp_u64 : decoder.u64.spec (GF := GF) (hG := hG))
    (wp_hs : decoder.hs.spec (GF := GF) (hG := hG))
    (wp_ops : decoder.ops.spec (GF := GF) (hG := hG)) :
    decodeOracle.spec (GF := GF) (hG := hG) := by
  intro o hsmall
  wp_start
  wp_auto
  wp_apply wp_string_to_bytes as %bsl ⟨Hbs, -⟩
  imod ownSlice_persist $$ Hbs with #Hbs
  ihave %Hbl := ownSlice_len $$ Hbs
  ihave Hd : decRep «$r0_ptr» (tEncodeOracle o) 0 $$ [«$r0»]
  · iunfold decRep
    iexists bsl
    rw [show W64 ((0 : Nat) : Int) = (0 : w64) from rfl]
    iframe
    isplitl []
    · iexact Hbs
    ipureintro; exact ⟨Nat.zero_le _, hsmall⟩
  have E0 : (tEncodeOracle o).drop 0 = tU64 (if o.created then W64 1 else W64 0) ++
      (tU64 (W64 o.cands.length) ++ (o.cands.flatMap tCandEnc ++ (tOpsBytes o.since ++
        (tU64 o.synced ++ (tHsBytes o.lastHS ++ (tU64 (W64 o.opens.length) ++
          o.opens.flatMap tU64)))))) := by
    have hc : tCandEnc = fun c => tOpsBytes c.h ++ (tU64 c.unl ++ tU64 c.pur) := by
      funext c; simp [tCandEnc]
    rw [hc]; simp [tEncodeOracle]
  have E1 := drop_app' E0
  have E2 := drop_app' E1
  simp only [tU64_length] at E1 E2
  have hcl := flat_len_bound _ _ o.cands tCandEnc _ tCandEnc_length E2 hsmall
  wp_apply wp_u64 _ _ 0 _ _ E0 $$ Hd as Hd
  wp_apply wp_u64 _ _ (0 + 8) _ _ E1 $$ Hd as Hd
  wp_apply +noauto (wp_slice_make2 (V := cand) (W64 0)) as %c0 ⟨Hc0, Hc0cap⟩
  · ipureintro; word
  simp only [List.replicate_zero, snap_dec]
  wp_auto
  simp only
  generalize hREST : tOpsBytes o.since ++ (tU64 o.synced ++ (tHsBytes o.lastHS ++
    (tU64 (W64 o.opens.length) ++ o.opens.flatMap tU64))) = REST at E2
  ihave HI : (∃ (c : w64) (csl : GoSlice) (cvs : List cand) (k' : Nat),
      "c" ∷ c_ptr ↦ c ∗
      "o" ∷ o_ptr ↦ (oracle.mk o.created csl (zero_val oracle).since' (zero_val oracle).synced'
        (zero_val oracle).lastHS' (zero_val oracle).opens') ∗
      "Hcs" ∷ csl ↦* cvs ∗ "Hcscap" ∷ ownSliceCap cand csl (DFrac.own 1) ∗
      "Hce" ∷ candsElems cvs (o.cands.take (uint.nat c)) ∗
      "Hd" ∷ decRep «$r0_ptr» (tEncodeOracle o) k' ∗
      "%Hc" ∷ ⌜(tEncodeOracle o).drop k' = (o.cands.drop (uint.nat c)).flatMap tCandEnc ++ REST ∧
        uint.nat c ≤ o.cands.length⌝ : IProp GF) $$ [c o Hc0 Hc0cap Hd]
  · iexists W64 0, c0, [], 0 + 8 + 8
    simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero, List.drop_zero]
    iframe
    isplitl []
    · iapply candsElems_nil
    ipureintro; exact ⟨E2, Nat.zero_le _⟩
  wp_for HI
  wp_if_destruct
  · have hil : uint.nat c < o.cands.length := (lt_count c _ hcl).mp Hif
    obtain ⟨cd, Hcd⟩ : ∃ cd, o.cands[uint.nat c]? = some cd := ⟨_, List.getElem?_eq_getElem hil⟩
    have f1 := Hc.1
    rw [flatMap_drop_cons o.cands tCandEnc _ cd Hcd, List.append_assoc] at f1
    have g1 : (tEncodeOracle o).drop k' = tOpsBytes cd.h ++ (tU64 cd.unl ++ (tU64 cd.pur ++
        ((o.cands.drop (uint.nat c + 1)).flatMap tCandEnc ++ REST))) := by
      rw [f1]; simp [tCandEnc]
    have g2 := drop_app' g1
    have g3 := drop_app' g2
    have g4 := drop_app' g3
    simp only [tU64_length] at g3 g4
    icases decRep_acc _ _ k' $$ Hd with ⟨%sl2, Hd, Hclose⟩
    wp_auto
    simp only [decide_true, ↓reduceIte]
    wp_auto
    ihave Hd := Hclose $$ Hd
    wp_apply wp_ops _ _ k' cd.h _ g1 $$ Hd as %hs ⟨#Hops, -, Hd⟩
    wp_apply wp_u64 _ _ _ _ _ g2 $$ Hd as Hd
    wp_apply wp_u64 _ _ _ _ _ g3 $$ Hd as Hd
    ihave #Hcr : candRep (cand.mk hs cd.unl cd.pur) cd $$ []
    · iunfold candRep
      isplitr
      · ipureintro; exact ⟨rfl, rfl⟩
      iexact Hops
    ihave Hce := candsElems_snoc cvs (o.cands.take (uint.nat c)) _ cd $$ [$Hce $Hcr]
    wp_apply wp_slice_literal
    isplitr
    · ipureintro; rfl
    iintro %csl1 ⟨Hcsl1, -⟩
    wp_apply wp_slice_append $$ [$Hcs $Hcscap $Hcsl1] as %csl' ⟨Hcs, Hcscap, -⟩
    wp_for_post
    iframe
    iexists c + W64 1, csl', cvs ++ [cand.mk hs cd.unl cd.pur], _
    have hc1 := nat_succ c _ hcl hil
    rw [hc1, take_succ_of o.cands _ cd Hcd]
    iframe
    ipureintro
    exact ⟨g4, by omega⟩
  · have hcn : uint.nat c = o.cands.length := by
      have := mt (lt_count c _ hcl).mpr Hif; omega
    have htk : o.cands.take (uint.nat c) = o.cands := by rw [hcn, List.take_length]
    rw [htk]
    have F0 := Hc.1
    rw [hcn, List.drop_length, List.flatMap_nil, List.nil_append, ← hREST] at F0
    have F1 := drop_app' F0
    have F2 := drop_app' F1
    have F3 := drop_app' F2
    have F4 := drop_app' F3
    simp only [tU64_length, tHsBytes_length] at F2 F3 F4
    have F4' : (tEncodeOracle o).drop (k' + (tOpsBytes o.since).length + 8 + 24 + 8) =
        (o.opens.drop (uint.nat (W64 0))).flatMap tU64 ++ [] := by
      rw [F4, List.append_nil]; rfl
    have hol := flat_len_bound _ _ o.opens tU64 [] (fun x => by rw [tU64_length]; exact Nat.le_refl _) F4' hsmall
    wp_apply wp_ops _ _ k' o.since _ F0 $$ Hd as %hsn ⟨#Hsn, Hsncap, Hd⟩
    wp_apply wp_u64 _ _ _ _ _ F1 $$ Hd as Hd
    wp_apply wp_hs _ _ _ _ _ F2 $$ Hd as Hd
    wp_apply wp_u64 _ _ _ _ _ F3 $$ Hd as Hd
    wp_apply +noauto (wp_slice_make2 (V := w64) (W64 0)) as %p0 ⟨Hp0, Hp0cap⟩
    · ipureintro; word
    simp only [List.replicate_zero]
    imod ownSlice_persist $$ Hp0 with #Hp0
    wp_auto
    simp only
    ihave HJ : (∃ (i : w64) (osl : GoSlice) (k'' : Nat),
        "i" ∷ i_ptr ↦ i ∗
        "o" ∷ o_ptr ↦ (oracle.mk o.created csl hsn o.synced o.lastHS osl) ∗
        "Hos" ∷ osl ↦*□ o.opens.take (uint.nat i) ∗ "Hoscap" ∷ ownSliceCap w64 osl (DFrac.own 1) ∗
        "Hd" ∷ decRep «$r0_ptr» (tEncodeOracle o) k'' ∗
        "%Hj" ∷ ⌜(tEncodeOracle o).drop k'' = (o.opens.drop (uint.nat i)).flatMap tU64 ++ [] ∧
          uint.nat i ≤ o.opens.length⌝ : IProp GF) $$ [i o Hp0 Hp0cap Hd]
    · iexists W64 0, p0, _
      simp only [show uint.nat (W64 0) = 0 from rfl, List.take_zero]
      iframe
      isplitl []
      · iexact Hp0
      ipureintro; exact ⟨F4', Nat.zero_le _⟩
    wp_for HJ
    wp_if_destruct
    · have hil : uint.nat i < o.opens.length := (lt_count i _ hol).mp Hif
      obtain ⟨x, Hx⟩ : ∃ x, o.opens[uint.nat i]? = some x := ⟨_, List.getElem?_eq_getElem hil⟩
      have f1 := Hj.1
      rw [flatMap_drop_cons o.opens tU64 _ x Hx, List.append_assoc] at f1
      have f2 := drop_app' f1
      rw [tU64_length] at f2
      icases decRep_acc _ _ k'' $$ Hd with ⟨%sl2, Hd, Hclose⟩
      wp_auto
      simp only [decide_true, ↓reduceIte]
      wp_auto
      ihave Hd := Hclose $$ Hd
      wp_apply wp_u64 _ _ _ _ _ f1 $$ Hd as Hd
      wp_apply wp_slice_literal
      isplitr
      · ipureintro; rfl
      iintro %osl1 ⟨Hosl1, -⟩
      wp_apply wp_slice_append_persistent $$ [$Hos $Hoscap $Hosl1] as %osl' ⟨Hos, Hoscap, -⟩
      wp_for_post
      iframe
      iexists i + W64 1, osl', _
      have hi1 := nat_succ i _ hol hil
      rw [hi1, take_succ_of o.opens _ x Hx]
      iframe
      ipureintro
      exact ⟨f2, by omega⟩
    · have hin : uint.nat i = o.opens.length := by
        have := mt (lt_count i _ hol).mpr Hif; omega
      have htk : o.opens.take (uint.nat i) = o.opens := by rw [hin, List.take_length]
      rw [htk]
      icases decRep_acc _ _ k'' $$ Hd with ⟨%sl2, Hd, Hclose⟩
      wp_auto
      iapply HΦ
      iunfold oracleRep
      simp only
      isplitr
      · ipureintro; simp
      isplitl [Hcs Hcscap Hce]
      · iunfold candsOwn
        iexists cvs
        iframe
      iframe
      iexact Hsn

end proof

end etcd_wal
end EtcdGrove
end Perennial
