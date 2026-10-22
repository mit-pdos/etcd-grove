/-
Proof of `Spec/github_com/mit_pdos/etcd_grove/examples/kv/decodeState.lean`. Lean-first (no
Rocq counterpart).
-/
module

public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.decodeState
public import Spec.github_com.mit_pdos.etcd_grove.examples.kv.getBytes

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace kv

open Iris Iris.BI Iris.ProofMode go_etcd_io.raft.v3

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.kv.Assumptions]

theorem decodeState.wp_proof (wp_getBytes : getBytes.spec (GF := GF) (hG := hG)) :
    decodeState.spec (GF := GF) (hG := hG) := by
  intro b dq kvs ops Hkvs Hops
  wp_start as Hb
  try wp_auto
  wp_apply wp_map_make1 (K := GoString) (V := GoString) as %mK HK
  wp_apply wp_map_make1 (K := GoString) (V := Bool) as %mA HA
  try wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  have Hel : (encState kvs ops).length = 8 + (encKVs kvs).length + (8 + (encOps ops).length) := by
    simp [encState, u64Le_length]; omega
  have Hbl : sint.Z b.len = 8 + (encKVs kvs).length + (8 + (encOps ops).length) := by
    rw [Hel] at Hlen; have := Hlen.1; word
  rw [decide_eq_false (by rw [Hbl]; show ¬ (_ < (8 : Int)); omega)]
  try wp_auto
  ihave Hb := (show (b ↦*{dq} encState kvs ops : IProp GF) ⊣⊢
      b ↦*{dq} (u64Le (W64 kvs.length) ++ (encKVs kvs ++ (u64Le (W64 ops.length) ++ encOps ops))) by
    simp only [encState, List.append_assoc]; exact .rfl).1 $$ Hb
  wp_apply encoding.binary.wp_LittleEndian_Uint64 b (u64Le (W64 kvs.length)) dq _
    (u64Le_length _) $$ [$Hb] as Hb
  rw [u64Le_to_word]
  try wp_auto
  have H8 : sint.Z (W64 8) = 8 := rfl
  rw [ite_eq_left (by rw [H8, Hbl]; refine ⟨by decide, by omega, by omega⟩)]
  try wp_auto
  have Hb8 : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z b.len := by rw [H8, Hbl]; omega
  icases (ownSlice_split_all (W64 8) b dq _ Hb8).1 $$ Hb with ⟨Hb1, Hb2⟩
  have Hd8 : (u64Le (W64 kvs.length) ++ (encKVs kvs ++ (u64Le (W64 ops.length) ++ encOps ops))).drop
      (sint.nat (W64 8)) = encKVs kvs ++ (u64Le (W64 ops.length) ++ encOps ops) :=
    List.drop_left' (u64Le_length _)
  have E0 : (slice.slice b w8 (W64 8) b.len ↦*{dq} (u64Le (W64 kvs.length) ++ (encKVs kvs ++
      (u64Le (W64 ops.length) ++ encOps ops))).drop (sint.nat (W64 8)) : IProp GF) ⊣⊢
      slice.slice b w8 (W64 8) b.len ↦*{dq} (encKVs kvs ++ (u64Le (W64 ops.length) ++ encOps ops)) := by
    rw [Hd8]; exact .rfl
  ihave Hb2 := E0.1 $$ Hb2
  -- the bindings
  ihave IK : iprop(∃ (i : w64) (cur : GoSlice) (K : GMap GoString GoString),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ cur ∗
      "Hcur" ∷ cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ (u64Le (W64 ops.length) ++ encOps ops)) ∗
      "Hback" ∷ (cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ (u64Le (W64 ops.length) ++ encOps ops)) -∗
        b ↦*{dq} encState kvs ops) ∗
      "HK" ∷ mK ↦$ K ∗
      "%HKv" ∷ ⌜(∀ k, K !! k = (kvs.take (uint.nat i)).lookup k) ∧ uint.nat i ≤ kvs.length⌝)
    $$ [i b Hb1 Hb2 HK]
  · iexists W64 0, _, ∅
    iframe
    simp only [show uint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
    iframe
    isplitl
    · iintro Hb2
      ihave Hb2 := E0.2 $$ Hb2
      ihave Hb := (ownSlice_split_all (W64 8) b dq _ Hb8).2 $$ [$Hb1 $Hb2]
      simp only [encState, List.append_assoc]
      iexact Hb
    ipureintro; exact ⟨fun k => rfl, Nat.zero_le _⟩
  wp_for IK
  have Hkl63 := Hkvs.2.1
  wp_if_destruct
  · have Hin : uint.nat i < kvs.length := by
      have h1 : uint.Z (W64 (kvs.length : Int)) = kvs.length := by word
      rw [h1] at Hif; word
    obtain ⟨p, Hp⟩ : ∃ p, kvs[uint.nat i]? = some p := ⟨_, List.getElem?_eq_getElem Hin⟩
    have Hdrop : kvs.drop (uint.nat i) = p :: kvs.drop (uint.nat i + 1) := by
      rw [List.drop_eq_getElem_cons Hin]
      rw [List.getElem?_eq_getElem Hin] at Hp
      rw [Option.some.inj Hp]
    have Hpl := Hkvs.2.2 p (List.mem_of_getElem? Hp)
    have EC : (cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ (u64Le (W64 ops.length) ++ encOps ops)) :
        IProp GF) ⊣⊢ cur ↦*{dq} (putB p.1 ++ (putB p.2 ++ (encKVs (kvs.drop (uint.nat i + 1)) ++
          (u64Le (W64 ops.length) ++ encOps ops)))) := by
      rw [Hdrop, encKVs_cons]; simp only [List.append_assoc]; exact .rfl
    ihave Hcur := EC.1 $$ Hcur
    try wp_auto
    wp_apply wp_getBytes cur dq p.1 _ Hpl.1 $$ [$Hcur] as %kb %rest ⟨Hk, Hrest, Hw1⟩
    try wp_auto
    wp_apply wp_getBytes rest dq p.2 _ Hpl.2 $$ [$Hrest] as %vb %rest2 ⟨Hv, Hrest2, Hw2⟩
    try wp_auto
    wp_apply wp_bytes_to_string vb p.2 dq $$ [$Hv] as Hv
    try wp_auto
    wp_apply wp_bytes_to_string kb p.1 dq $$ [$Hk] as Hk
    wp_apply wp_mapInsert $$ [$HK] as HK
    try wp_auto
    wp_for_post
    iframe
    iexists i + W64 1, rest2, <[p.1 := p.2]> K
    have Hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
    rw [Hi1]
    iframe
    isplitl [Hback Hw1 Hw2 Hk Hv]
    · iintro Hr2
      ihave Hr := Hw2 $$ Hv Hr2
      ihave Hc := Hw1 $$ Hk Hr
      ihave Hc := EC.2 $$ Hc
      iapply Hback $$ Hc
    ipureintro
    refine ⟨fun k => ?_, by omega⟩
    rw [lookup_take_succ kvs (uint.nat i) p Hp Hkvs.1 k, GMap.lookup_insert_eq_iff]
    by_cases hk : p.1 = k
    · subst hk; simp
    · simp [hk, Ne.symm hk, HKv.1 k]
  · have Hie : uint.nat i = kvs.length := by
      have h1 : uint.Z (W64 (kvs.length : Int)) = kvs.length := by word
      rw [h1] at Hif; have := HKv.2; word
    have Hdn : kvs.drop (uint.nat i) = [] := by rw [Hie, List.drop_length]
    have HKv' : ∀ k, K !! k = kvs.lookup k := by
      intro k; rw [HKv.1 k, Hie, List.take_length]
    have EC : (cur ↦*{dq} (encKVs (kvs.drop (uint.nat i)) ++ (u64Le (W64 ops.length) ++ encOps ops)) :
        IProp GF) ⊣⊢ cur ↦*{dq} (u64Le (W64 ops.length) ++ encOps ops) := by
      rw [Hdn]; simp only [encKVs, List.nil_append]; exact .rfl
    ihave Hcur := EC.1 $$ Hcur
    ihave %Hcl := ownSlice_len _ _ _ $$ Hcur
    ihave %Hcwf := ownSlice_wf _ _ _ $$ Hcur
    have Hcll : sint.Z cur.len = 8 + (encOps ops).length := by
      have := Hcl.1; simp only [List.length_append, u64Le_length] at this; word
    rw [decide_eq_false (by rw [Hcll]; show ¬ (_ < (8 : Int)); omega)]
    try wp_auto
    wp_apply encoding.binary.wp_LittleEndian_Uint64 cur (u64Le (W64 ops.length)) dq _
      (u64Le_length _) $$ [$Hcur] as Hcur
    rw [u64Le_to_word]
    try wp_auto
    rw [ite_eq_left (by rw [H8, Hcll]; refine ⟨by decide, by omega, by omega⟩)]
    try wp_auto
    have Hc8 : 0 ≤ sint.Z (W64 8) ∧ sint.Z (W64 8) ≤ sint.Z cur.len := by rw [H8, Hcll]; omega
    icases (ownSlice_split_all (W64 8) cur dq _ Hc8).1 $$ Hcur with ⟨Hc1, Hc2⟩
    have Hd8' : (u64Le (W64 ops.length) ++ encOps ops).drop (sint.nat (W64 8)) = encOps ops :=
      List.drop_left' (u64Le_length _)
    have E1 : (slice.slice cur w8 (W64 8) cur.len ↦*{dq}
        (u64Le (W64 ops.length) ++ encOps ops).drop (sint.nat (W64 8)) : IProp GF) ⊣⊢
        slice.slice cur w8 (W64 8) cur.len ↦*{dq} encOps ops := by rw [Hd8']; exact .rfl
    ihave Hc2 := E1.1 $$ Hc2
    -- the operations
    ihave IO : iprop(∃ (i : w64) (cur2 : GoSlice) (A' : GMap GoString Bool),
        "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ cur2 ∗
        "Hcur" ∷ cur2 ↦*{dq} encOps (ops.drop (uint.nat i)) ∗
        "Hback2" ∷ (cur2 ↦*{dq} encOps (ops.drop (uint.nat i)) -∗ b ↦*{dq} encState kvs ops) ∗
        "HA" ∷ mA ↦$ A' ∗
        "%HAv" ∷ ⌜(∀ o, (o ∈ ops.take (uint.nat i) → A' !! o = some true) ∧
            (o ∉ ops.take (uint.nat i) → A' !! o = none)) ∧ uint.nat i ≤ ops.length⌝)
      $$ [i b Hc1 Hc2 Hback HA]
    · iexists W64 0, _, ∅
      iframe
      simp only [show uint.nat (W64 0) = 0 from rfl, List.drop_zero, List.take_zero]
      iframe
      isplitl
      · iintro Hc2
        ihave Hc2 := E1.2 $$ Hc2
        ihave Hc := (ownSlice_split_all (W64 8) cur dq _ Hc8).2 $$ [$Hc1 $Hc2]
        ihave Hc := EC.2 $$ Hc
        iapply Hback $$ Hc
      ipureintro; exact ⟨fun o => ⟨fun h => by simp at h, fun _ => rfl⟩, Nat.zero_le _⟩
    wp_for IO
    have Hol63 := Hops.2.1
    wp_if_destruct
    · have Hin : uint.nat i < ops.length := by
        have h1 : uint.Z (W64 (ops.length : Int)) = ops.length := by word
        rw [h1] at Hif; word
      obtain ⟨o, Ho⟩ : ∃ o, ops[uint.nat i]? = some o := ⟨_, List.getElem?_eq_getElem Hin⟩
      have Hdrop : ops.drop (uint.nat i) = o :: ops.drop (uint.nat i + 1) := by
        rw [List.drop_eq_getElem_cons Hin]
        rw [List.getElem?_eq_getElem Hin] at Ho
        rw [Option.some.inj Ho]
      have Hol := Hops.2.2 o (List.mem_of_getElem? Ho)
      have EO : (cur2 ↦*{dq} encOps (ops.drop (uint.nat i)) : IProp GF) ⊣⊢
          cur2 ↦*{dq} (putB o ++ encOps (ops.drop (uint.nat i + 1))) := by
        rw [Hdrop, encOps_cons]; exact .rfl
      ihave Hcur := EO.1 $$ Hcur
      try wp_auto
      wp_apply wp_getBytes cur2 dq o _ Hol $$ [$Hcur] as %ob %rest ⟨Hob, Hrest, Hw1⟩
      try wp_auto
      wp_apply wp_bytes_to_string ob o dq $$ [$Hob] as Hob
      wp_apply wp_mapInsert $$ [$HA] as HA
      try wp_auto
      wp_for_post
      iframe
      iexists i + W64 1, rest, <[o := true]> A'
      have Hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
      rw [Hi1]
      iframe
      isplitl [Hback2 Hw1 Hob]
      · iintro Hr
        ihave Hc := Hw1 $$ Hob Hr
        ihave Hc := EO.2 $$ Hc
        iapply Hback2 $$ Hc
      ipureintro
      refine ⟨fun o' => ?_, by omega⟩
      have Htk : ops.take (uint.nat i + 1) = ops.take (uint.nat i) ++ [o] := by
        rw [List.take_add_one, Ho]; rfl
      rw [Htk]
      by_cases ho : o = o'
      · subst ho
        refine ⟨fun _ => by rw [GMap.lookup_insert_eq_iff]; simp, fun h => absurd (by simp) h⟩
      · have h1 := HAv.1 o'
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [GMap.lookup_insert_eq_iff]
          simp only [ho, ↓reduceIte]
          rcases List.mem_append.1 h with h | h
          · exact h1.1 h
          · simp at h; exact absurd h.symm ho
        · rw [GMap.lookup_insert_eq_iff]
          simp only [ho, ↓reduceIte]
          exact h1.2 (fun h' => h (List.mem_append_left _ h'))
    · have Hie : uint.nat i = ops.length := by
        have h1 : uint.Z (W64 (ops.length : Int)) = ops.length := by word
        rw [h1] at Hif; have := HAv.2; word
      have Hdn : ops.drop (uint.nat i) = [] := by rw [Hie, List.drop_length]
      have EN : (cur2 ↦*{dq} encOps (ops.drop (uint.nat i)) : IProp GF) ⊣⊢ cur2 ↦*{dq} ([] : List w8) := by
        rw [Hdn]; exact .rfl
      ihave Hcur := EN.1 $$ Hcur
      ihave %Hc0 := ownSlice_len _ _ _ $$ Hcur
      have Hz : sint.Z cur2.len = 0 := by have := Hc0.1; simp at this; word
      try wp_auto
      rw [decide_eq_true (by word)]
      try wp_auto
      iapply HΦ
      ihave Hcur := EN.2 $$ Hcur
      iframe
      isplitl [Hback2 Hcur]
      · iapply Hback2 $$ Hcur
      ipureintro
      refine ⟨HKv', fun o => ?_⟩
      have h1 := HAv.1 o
      rw [Hie, List.take_length] at h1
      by_cases ho : o ∈ ops
      · rw [if_pos ho]; exact h1.1 ho
      · rw [if_neg ho]; exact h1.2 ho

end proof

end kv
end EtcdGrove
end Perennial
