/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swift/ClientChecksum.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
`clientChecksum(hs, dep)` (swift/dpath.go): a copy of `dep` sorted by `cmdIdCmp`, its ids
chained from the zero hash, one more round over `(-1, len)` (`sp.depHash`), appended to a copy
of `hs`. `swift.clientChecksum.specR` (ReplyChan.lean) over `slices.SortFunc`, `cmdIdCmp` and
`hash`'s specs.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.ReplyChan
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.swift.SortedIds

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

section proof
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics] [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF]
variable [swift.Assumptions]

set_option goose.wp.extras true

theorem swift.clientChecksum.wp_proof (wp_SortFunc : slices.SortFunc.spec (hG := hG))
    (wp_cmdIdCmp : swift.cmdIdCmp.specI (hG := hG)) (wp_hash : swift.hash.spec (hG := hG)) :
    swift.clientChecksum.specR (hG := hG) := by
  intro hs dep Hs D dqh dqd
  haveI := swift.hlog.cmdId_intoValInj (sem := sem)
  wp_start as ⟨Hhs, Hdep, %Hp⟩
  ihave #Hcmp := swift.cmdIdCmp_implements wp_cmdIdCmp $$ []
  · iassumption
  ihave %HDl := ownSlice_len _ _ _ $$ Hdep
  wp_auto
  wp_apply (wp_slice_make2 (V := swift.CommandId) dep.len) as %ids ⟨Hids, Hidsc⟩
  · ipureintro; exact HDl.2
  try wp_auto
  wp_apply (wp_slice_copy (V := swift.CommandId)) $$ [$Hids $Hdep] as %n1 ⟨%Hn1, Hids, Hdep⟩
  try wp_auto
  have hcp : List.take (List.replicate (sint.nat dep.len) (zero_val swift.CommandId)).length D ++
      List.drop D.length (List.replicate (sint.nat dep.len) (zero_val swift.CommandId)) = D := by
    rw [List.length_replicate, ← HDl.1]; simp
  isimp only [hcp] at Hids
  wp_apply (wp_SortFunc (E := swift.CommandId) (S := go.GoType.SliceType swift.CommandId.ty)
      (fun a b => swift.cmdIdLt a b = true) ids _ D swift.cmdIdLt_swo) $$ [Hids Hcmp]
    as %xs' ⟨Hids, %Hperm, %Hsorted⟩
  · iframe Hids Hcmp
    ipureintro; omega
  try wp_auto
  ihave %Hxl := ownSlice_len _ _ _ $$ Hids
  ihave HL : (∃ (iv : w64) (ha : GoArray w8 32) (x : swift.CommandId),
      "i" ∷ i_ptr ↦ iv ∗ "h" ∷ h_ptr ↦ ha ∗ "id" ∷ id_ptr ↦ x ∗
      "#Hch" ∷ sp.chainHash (List.replicate 32 (W8 0)) ((xs'.take (sint.nat iv)).map swift.toCmdId)
        ha.arr ∗
      "%Hiv" ∷ ⌜0 ≤ sint.Z iv ∧ sint.Z iv ≤ sint.Z ids.len ∧ ha.arr.length = 32⌝ : IProp netDistGF)
    $$ [i h id]
  · iexists (W64 0), _, _
    iframe
    isplitl
    · have e0 : sint.nat (W64 0) = 0 := rfl
      isimp only [e0, List.take_zero, List.map_nil, sp.chainHash]
      ipureintro; rfl
    ipureintro; refine ⟨by decide, by have := Hxl.2; simpa using this, rfl⟩
  wp_for HL
  by_cases hlt : sint.Z iv < sint.Z ids.len
  · simp only [hlt, _root_.decide_true]
    cleanup_bool_decide
    try simp only [↓reduceIte, ite_true]
    wp_auto
    have hb : 0 ≤ sint.Z iv ∧ sint.Z iv < sint.Z ids.len := ⟨Hiv.1, hlt⟩
    isimp only [hb, _root_.and_self, ↓reduceIte]
    have e1 := swift.snat_eq iv Hiv.1
    have e2 := swift.snat_eq ids.len Hxl.2
    have hix : (sint.Z iv).toNat < xs'.length := by have := Hxl.1; omega
    wp_apply (wp_load_slice_index (V := swift.CommandId) ids (sint.Z iv) xs' (DFrac.own 1)
      xs'[(sint.Z iv).toNat] Hiv.1) $$ [$Hids] as Hids
    · ipureintro; exact List.getElem?_eq_getElem hix
    try wp_auto
    ihave #Hsha : isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 $$ []
    · iPkgInit
    wp_apply wp_hash ha xs'[(sint.Z iv).toNat] $$ [$Hsha] as %ha' #Hho
    · ipureintro; exact Hiv.2.2
    wp_for_post
    ihave %Hl' := sp.hashOf_len $$ Hho
    have hiv1 : sint.Z (iv + W64 1) = sint.Z iv + 1 := by
      have := Hxl.1; have hle : xs'.length ≤ 2 ^ 62 := by
        have := Hperm.length_eq; have := Hp.2.2; omega
      word
    iframe
    iexists (iv + W64 1), ha', xs'[(sint.Z iv).toNat]
    iframe
    isplitl
    · have e3 : sint.nat (iv + W64 1) = (sint.Z iv).toNat + 1 := by
        show (sint.Z _).toNat = _; rw [hiv1]; omega
      rw [e3, List.take_add_one, List.getElem?_eq_getElem hix]
      simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
      iapply (sp.chainHash_snoc _ _ _ _).2
      iexists ha.arr
      iframe Hho
      iexact Hch
    ipureintro
    refine ⟨by omega, by omega, Hl'⟩
  · simp only [hlt, decide_false]
    cleanup_bool_decide
    try simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    ihave #Hsha : isPkgInit (PROP := IProp netDistGF) pkg_id.crypto.sha256 $$ []
    · iPkgInit
    wp_apply wp_hash ha _ $$ [$Hsha] as %hd #Hhd
    · ipureintro; exact Hiv.2.2
    try wp_auto
    ihave %Hhsl := ownSlice_len _ _ _ $$ Hhs
    simp only [List.length_map] at Hhsl
    have hlen1 : sint.Z (hs.len + W64 1) = sint.Z hs.len + 1 := by
      have := Hp.2.1; have e := swift.snat_eq hs.len Hhsl.2; word
    wp_apply (wp_slice_make3 (V := swift.SHash) hs.len (hs.len + W64 1) (by omega))
      as %out ⟨Hout, Houtc, -⟩
    try wp_auto
    wp_apply (wp_slice_copy (V := swift.SHash)) $$ [$Hout $Hhs] as %n2 ⟨%Hn2, Hout, Hhs⟩
    try wp_auto
    wp_apply wp_slice_literal (V := swift.SHash) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    try wp_auto
    wp_apply (wp_slice_append (V := swift.SHash)) $$ [$Hout $Houtc $Hsl1] as %out2 ⟨Hout, -, -⟩
    try wp_auto
    have e1 := swift.snat_eq iv Hiv.1
    have e2 := swift.snat_eq ids.len Hxl.2
    have hivl : sint.nat iv = xs'.length := by have := Hxl.1; omega
    have hlenD : sint.Z ids.len = (D.length : Int) := by
      have := Hxl.1; have := Hperm.length_eq; omega
    have hsort : sp.sortIds (D.map swift.toCmdId) = xs'.map swift.toCmdId := by
      apply sp.sortIds_eq _ _ (Hperm.map _).symm
      rw [List.pairwise_map, List.pairwise_iff_getElem]
      intro i j hi hj hij
      have := Hsorted i j _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem hj) hij
      rw [swift.cmdIdLt_toCmdId] at this
      simp [this]
    ihave %Hdl := sp.hashOf_len $$ Hhd
    iapply HΦ
    iframe Hhs Hdep
    iexists hd.arr
    isplitl [Hout]
    · iExactEq Hout
      rw [List.length_replicate, ← Hhsl.1, List.length_map,
        List.take_of_length_le (by simp)]
      simp [swift.handler.shashOf]
    isplitl
    · unfold sp.depHash
      rw [hsort]
      iapply (sp.chainHash_snoc _ _ _ _).2
      iexists ha.arr
      have htk : List.take (sint.nat iv) xs' = xs' := List.take_of_length_le (by omega)
      isplitr
      · isimp only [htk] at Hch; iexact Hch
      iExactEq Hhd
      congr 3
      simp only [List.length_map, swift.toCmdId, hlenD]
      rfl
    ipureintro; exact Hdl

end proof

end Perennial.github_com.imdea_software.swiftpaxos
