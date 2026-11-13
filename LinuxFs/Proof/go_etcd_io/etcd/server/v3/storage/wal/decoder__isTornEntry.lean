/-
The proof of `LinuxFs/Spec/go_etcd_io/etcd/server/v3/storage/wal/decoder__isTornEntry.lean`.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.server.v3.storage.wal.decoder__isTornEntry


@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open WalEnc WalFs

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.server.v3.storage.wal.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]


/-! The chunks' bounds, as positions in `data` (the chunks alias `data`). -/

/-- `isTornEntry`'s chunks of an `n`-byte buffer from position `c` at file offset `fo`, as bounds
`[a, b)` in the buffer. -/
private def chunkBnds (fo c n : Nat) : List (Nat × Nat) :=
  if c < n then
    (c, c + min (minSectorSize - fo % minSectorSize) (n - c)) ::
      chunkBnds (fo + min (minSectorSize - fo % minSectorSize) (n - c))
        (c + min (minSectorSize - fo % minSectorSize) (n - c)) n
  else []
termination_by n - c
decreasing_by
  have : fo % minSectorSize < minSectorSize := Nat.mod_lt _ (by decide)
  omega

private theorem chunkBnds_cons (fo c n : Nat) (h : c < n) :
    chunkBnds fo c n =
      (c, c + min (minSectorSize - fo % minSectorSize) (n - c)) ::
        chunkBnds (fo + min (minSectorSize - fo % minSectorSize) (n - c))
          (c + min (minSectorSize - fo % minSectorSize) (n - c)) n := by
  rw [chunkBnds]; simp [h]

private theorem chunkBnds_nil (fo c n : Nat) (h : ¬ c < n) : chunkBnds fo c n = [] := by
  rw [chunkBnds]; simp [h]

private theorem chunkBnds_map (xs : List w8) : ∀ (m fo c : Nat), xs.length - c = m →
    (chunkBnds fo c xs.length).map (fun p => subslice p.1 p.2 xs) = sectorChunks fo (xs.drop c) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro fo c hm
    by_cases h : c < xs.length
    · rw [chunkBnds_cons _ _ _ h]
      obtain ⟨b, bs, hbs⟩ : ∃ b bs, xs.drop c = b :: bs := by
        cases hd : xs.drop c with
        | nil => rw [List.drop_eq_nil_iff] at hd; omega
        | cons b bs => exact ⟨b, bs, rfl⟩
      have hpos : 0 < minSectorSize - fo % minSectorSize := by
        have : fo % minSectorSize < minSectorSize := Nat.mod_lt _ (by decide)
        omega
      rw [hbs, sectorChunks, List.map_cons, ← hbs]
      congr 1
      · simp only
        rw [subslice_comm, Nat.add_sub_cancel_left]
        apply List.take_eq_take_iff.mpr
        simp only [List.length_drop]
        omega
      · by_cases hle : minSectorSize - fo % minSectorSize ≤ xs.length - c
        · rw [Nat.min_eq_left hle, ih (xs.length - (c + (minSectorSize - fo % minSectorSize)))
            (by omega) _ _ rfl, List.drop_drop]
        · rw [chunkBnds_nil _ _ _ (by omega), List.drop_drop,
            List.drop_eq_nil_of_le (by omega), sectorChunks]
          rfl
    · rw [chunkBnds_nil _ _ _ h, List.drop_eq_nil_of_le (by omega), sectorChunks]; rfl

private theorem chunkBnds_le (fo c n : Nat) : ∀ p ∈ chunkBnds fo c n, c ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ n := by
  fun_induction chunkBnds fo c n with
  | case1 fo c h ih =>
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp only; omega
    · have := ih p hp; omega
  | case2 fo c h => simp

theorem go_etcd_io.etcd.server.v3.storage.wal.decoder.isTornEntry.wp_proof :
    go_etcd_io.etcd.server.v3.storage.wal.decoder.isTornEntry.spec (GF := GF) (hG := hG) := by
  intro d sl off data xs dq dq' dq'' hoff hxs
  wp_start as ⟨Hbrs, Hoff, Hdata⟩
  wp_auto
  wp_if_destruct
  rotate_left
  · simp only [show isTorn false off xs = false from rfl]
    iapply HΦ
    iframe
  ihave %Hlen := ownSlice_len _ _ _ $$ Hdata
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hdata
  ihave IH : iprop(∃ (c : Nat) (cs : GoSlice) (dn : List (Nat × Nat)),
      "curOff" ∷ curOff_ptr ↦ W64 c ∗ "fileOff" ∷ fileOff_ptr ↦ W64 (off + 8 + c) ∗
      "chunks" ∷ chunks_ptr ↦ cs ∗
      "Hcs" ∷ cs ↦* dn.map (fun p => slice.slice data w8 (W64 p.1) (W64 p.2)) ∗
      "Hcap" ∷ ownSliceCap GoSlice cs (DFrac.own 1) ∗
      "%Hc" ∷ ⌜c ≤ xs.length ∧ (∀ p ∈ dn, p.1 ≤ p.2 ∧ p.2 ≤ c) ∧
        dn ++ chunkBnds (off + 8 + c) c xs.length = chunkBnds (off + 8) 0 xs.length⌝)
      $$ [curOff fileOff chunks]
  · iexists 0, slice.nil, []
    simp only [named, List.map_nil]
    rw [show W64 (↑off + 8 + ↑(0 : Nat)) = W64 ↑off + W64 8 by word]
    iframe
    isplitl []
    · iapply ownSlice_nil
    isplitl []
    · iapply ownSliceCap_nil
    ipureintro; simp
  wp_for IH
  wp_if_destruct
  · obtain ⟨Hcn, Hdn, Hbnd⟩ := Hc
    have hn : (xs.length : Int) = sint.Z data.len := by rw [Hlen.1]; word
    have hcn : c < xs.length := by
      have : sint.Z (W64 (c : Int)) < sint.Z data.len := by
        exact Hif
      have hc : sint.Z (W64 (c : Int)) = c := by word
      omega
    have hsrem : W64 512 - BitVec.srem (W64 (↑off + 8 + ↑c)) (W64 512) =
        W64 ((minSectorSize - (off + 8 + c) % minSectorSize : Nat) : Int) := by
      have hx : (W64 (↑off + 8 + ↑c)).msb = false := by
        rw [BitVec.msb_eq_decide]; simp only [decide_eq_false_iff_not, Nat.not_le]; word
      have hy : (W64 512).msb = false := by decide
      rw [BitVec.srem, hx, hy]
      simp only
      unfold minSectorSize
      apply BitVec.eq_of_toNat_eq
      have hlt : (off + 8 + c) < 2 ^ 62 := by omega
      have hm : (off + 8 + c) % 512 < 512 := Nat.mod_lt _ (by decide)
      simp only [BitVec.toNat_sub, BitVec.umod_eq, BitVec.toNat_umod]
      have e1 : (W64 (↑off + 8 + ↑c)).toNat = off + 8 + c := by word
      have e2 : (W64 512).toNat = 512 := rfl
      have e3 : (W64 ((512 - (off + 8 + c) % 512 : Nat) : Int)).toNat = 512 - (off + 8 + c) % 512 := by
        word
      rw [e1, e2, e3]
      omega
    rw [hsrem]
    wp_join iprop(chunkLen_ptr ↦ W64 ((min (minSectorSize - (off + 8 + c) % minSectorSize)
        (xs.length - c) : Nat) : Int) ∗ data_ptr ↦ data ∗ curOff_ptr ↦ W64 (c : Int))
      with [chunkLen data curOff] as ⟨chunkLen, data, curOff⟩
    · have hm : minSectorSize - (off + 8 + c) % minSectorSize ≤ 512 := by unfold minSectorSize; omega
      have h1 : sint.Z (data.len - W64 (c : Int)) <
          sint.Z (W64 ((minSectorSize - (off + 8 + c) % minSectorSize : Nat) : Int)) := by
        exact Hif
      have e1 : sint.Z (data.len - W64 (c : Int)) = (xs.length : Int) - c := by word
      have e2 : sint.Z (W64 ((minSectorSize - (off + 8 + c) % minSectorSize : Nat) : Int)) =
          ((minSectorSize - (off + 8 + c) % minSectorSize : Nat) : Int) := by word
      rw [Nat.min_eq_right (by omega), show data.len - W64 (c : Int) = W64 ((xs.length - c : Nat) : Int) by word]
      iframe
    · have hm : minSectorSize - (off + 8 + c) % minSectorSize ≤ 512 := by unfold minSectorSize; omega
      have h1 : ¬ sint.Z (data.len - W64 (c : Int)) <
          sint.Z (W64 ((minSectorSize - (off + 8 + c) % minSectorSize : Nat) : Int)) := by
        exact Hif
      have e1 : sint.Z (data.len - W64 (c : Int)) = (xs.length : Int) - c := by word
      have e2 : sint.Z (W64 ((minSectorSize - (off + 8 + c) % minSectorSize : Nat) : Int)) =
          ((minSectorSize - (off + 8 + c) % minSectorSize : Nat) : Int) := by word
      rw [Nat.min_eq_left (by omega)]
      iframe
    obtain ⟨k, hk⟩ : ∃ k, k = min (minSectorSize - (off + 8 + c) % minSectorSize) (xs.length - c) :=
      ⟨_, rfl⟩
    rw [← hk]
    have hkpos : 0 < k := by
      have : (off + 8 + c) % minSectorSize < minSectorSize := Nat.mod_lt _ (by decide)
      omega
    have hkle : c + k ≤ xs.length := by omega
    have hadd : W64 (c : Int) + W64 (k : Int) = W64 ((c + k : Nat) : Int) := by word
    rw [hadd, ite_eq_left_of_eq_true _ _ (eq_true ⟨by word, by word, by word⟩)]
    wp_auto
    wp_apply (wp_slice_literal (l := [slice.slice data w8 (W64 (c : Int)) (W64 ((c + k : Nat) : Int))]))
    isplitr
    · ipureintro; rfl
    iintro %osl ⟨Hosl, -⟩
    (try wp_auto)
    wp_apply wp_slice_append $$ [$Hcs $Hcap $Hosl] as %cs' ⟨Hcs, Hcap, -⟩
    (try wp_auto)
    wp_for_post
    iframe
    iexists c + k, cs', dn ++ [(c, c + k)]
    simp only [named, List.map_append, List.map_cons, List.map_nil]
    rw [show W64 (↑off + 8 + ↑c) + W64 (k : Int) = W64 (↑off + 8 + ↑(c + k)) by word, hadd]
    iframe
    ipureintro
    refine ⟨hkle, ?_, ?_⟩
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · have := Hdn p hp; omega
      · rw [List.mem_singleton] at hp; subst hp; simp only; omega
    · rw [← Hbnd, chunkBnds_cons _ _ _ hcn, ← hk, List.append_assoc, List.singleton_append,
        show off + 8 + c + k = off + 8 + (c + k) by omega]
  · obtain ⟨Hcn, Hdn, Hbnd⟩ := Hc
    have hc : c = xs.length := by
      have : ¬ sint.Z (W64 (c : Int)) < sint.Z data.len := by
        exact Hif
      have : sint.Z (W64 (c : Int)) = c := by word
      have : (xs.length : Int) = sint.Z data.len := by rw [Hlen.1]; word
      omega
    subst hc
    rw [chunkBnds_nil _ _ _ (Nat.lt_irrefl _), List.append_nil] at Hbnd
    subst Hbnd
    try wp_auto
    have hC := chunkBnds_map xs _ (off + 8) 0 rfl
    rw [List.drop_zero] at hC
    have hB := chunkBnds_le (off + 8) 0 xs.length
    ihave %Hcsl := ownSlice_len _ _ _ $$ Hcs
    rw [List.length_map] at Hcsl
    ihave IH2 : iprop(∃ (i : w64) (sv : GoSlice),
        "i" ∷ i_ptr ↦ i ∗ "sect" ∷ sect_ptr ↦ sv ∗
        "Hcs" ∷ cs ↦* (chunkBnds (off + 8) 0 xs.length).map
          (fun p => slice.slice data w8 (W64 p.1) (W64 p.2)) ∗
        "Hdata" ∷ data ↦*{dq''} xs ∗
        "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.nat i ≤ (chunkBnds (off + 8) 0 xs.length).length ∧
          ((sectorChunks (off + 8) xs).take (sint.nat i)).any (fun s => s.all (· == 0#8)) = false⌝)
      $$ [i sect Hcs Hdata]
    · iexists W64 0, _
      simp only [named]
      iframe
      ipureintro
      have h0 : sint.nat (W64 0) = 0 := rfl
      rw [h0]
      refine ⟨by decide, by simp, by simp⟩
    wp_for IH2
    wp_if_destruct
    · obtain ⟨Hi0, HiB, Hany⟩ := Hi
      have hiB : sint.nat i < (chunkBnds (off + 8) 0 xs.length).length := by
        have : sint.Z i < sint.Z cs.len := by
          exact Hif
        word
      obtain ⟨p, hp⟩ : ∃ p, (chunkBnds (off + 8) 0 xs.length)[sint.nat i]? = some p :=
        ⟨_, List.getElem?_eq_getElem hiB⟩
      have hpm : p ∈ chunkBnds (off + 8) 0 xs.length := List.mem_of_getElem? hp
      have hpb := hB p hpm
      rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hi0, by word⟩)]
      wp_apply wp_load_slice_index cs (sint.Z i) _ (DFrac.own 1)
        (slice.slice data w8 (W64 (p.1 : Int)) (W64 (p.2 : Int))) Hi0 $$ [Hcs] as Hcs
      · iframe; ipureintro
        rw [List.getElem?_map, show (sint.Z i).toNat = sint.nat i from rfl, hp]; rfl
      irename i => io
      try wp_auto
      have hdl : (xs.length : Int) = sint.Z data.len := by rw [Hlen.1]; word
      have hab : 0 ≤ sint.Z (W64 (p.1 : Int)) ∧ sint.Z (W64 (p.1 : Int)) ≤ sint.Z (W64 (p.2 : Int)) ∧
          sint.Z (W64 (p.2 : Int)) ≤ sint.Z data.len := by
        refine ⟨by word, by word, by word⟩
      icases (ownSlice_slice (W64 (p.1 : Int)) (W64 (p.2 : Int)) data dq'' xs hab).1 $$ Hdata
        with ⟨Hpre, Hmid, Hsuf⟩
      have ha : sint.nat (W64 (p.1 : Int)) = p.1 := by word
      have hb : sint.nat (W64 (p.2 : Int)) = p.2 := by word
      rw [ha, hb]
      obtain ⟨ys, hys⟩ : ∃ ys, ys = subslice p.1 p.2 xs := ⟨_, rfl⟩
      rw [← hys]
      ihave %Hysl := ownSlice_len _ _ _ $$ Hmid
      wp_join iprop(isZero_ptr ↦ ys.all (· == 0#8) ∗
          slice.slice data w8 (W64 (p.1 : Int)) (W64 (p.2 : Int)) ↦*{dq''} ys) at next
        with [isZero Hmid io v] as ⟨isZero, Hmid⟩
      · ihave IH3 : iprop(∃ (j : w64) (bv : w8), "io" ∷ i_ptr ↦ j ∗ "v" ∷ v_ptr ↦ bv ∗
            "isZero" ∷ isZero_ptr ↦ true ∗
            "Hmid" ∷ slice.slice data w8 (W64 (p.1 : Int)) (W64 (p.2 : Int)) ↦*{dq''} ys ∗
            "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.nat j ≤ ys.length ∧
              (ys.take (sint.nat j)).all (· == 0#8) = true⌝) $$ [io v isZero Hmid]
        · iexists W64 0, _
          simp only [named]
          iframe
          ipureintro
          have h0 : sint.nat (W64 0) = 0 := rfl
          rw [h0]
          refine ⟨by decide, by simp, by simp⟩
        wp_for IH3
        wp_if_destruct
        · obtain ⟨Hj0, Hjl, Hall⟩ := Hj
          have hjl : sint.nat j < ys.length := by
            have : sint.Z j < sint.Z (slice.slice data w8 (W64 (p.1 : Int)) (W64 (p.2 : Int))).len := by
              exact Hif
            have := Hysl.1
            word
          rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨Hj0, by have := Hysl.1; word⟩)]
          obtain ⟨bj, hbj⟩ : ∃ b, ys[sint.nat j]? = some b := ⟨_, List.getElem?_eq_getElem hjl⟩
          wp_apply wp_load_slice_index _ (sint.Z j) _ dq'' bj Hj0 $$ [Hmid] as Hmid
          · iframe; ipureintro
            exact hbj
          try wp_auto
          have htk : ys.take (sint.nat j + 1) = ys.take (sint.nat j) ++ [bj] := by
            rw [List.take_add_one, hbj]; rfl
          wp_if_destruct
          · try wp_auto
            wp_for_post
            iframe
            iexists j + W64 1, _
            simp only [named]
            iframe
            ipureintro
            have hj1 : sint.nat (j + W64 1) = sint.nat j + 1 := by word
            rw [hj1, htk]
            refine ⟨by word, by omega, ?_⟩
            simp only [List.all_append, Hall, List.all_cons, List.all_nil, Bool.true_and, Bool.and_true]
            simp
          · try wp_auto
            wp_for_post
            have hf : (ys.all fun x => x == 0#8) = false := by
              rw [List.all_eq_false]
              exact ⟨bj, List.mem_of_getElem? hbj, by simpa using Hif⟩
            rw [hf]
            iframe
            ipureintro; rfl
        · obtain ⟨Hj0, Hjl, Hall⟩ := Hj
          have hjl : sint.nat j = ys.length := by
            have : ¬ sint.Z j < sint.Z (slice.slice data w8 (W64 (p.1 : Int)) (W64 (p.2 : Int))).len := by
              exact Hif
            have := Hysl.1
            word
          rw [hjl, List.take_length] at Hall
          rw [Hall]
          iframe
      have hCi : (sectorChunks (off + 8) xs)[sint.nat i]? = some ys := by
        rw [← hC, List.getElem?_map, hp, hys]; rfl
      ihave Hdata := (ownSlice_slice (W64 (p.1 : Int)) (W64 (p.2 : Int)) data dq'' xs hab).2
        $$ [Hpre Hmid Hsuf]
      · rw [ha, hb, ← hys]; iframe
      cases hz : (ys.all fun x => x == 0#8)
      · try wp_auto
        wp_for_post
        iframe
        iexists i + W64 1, _
        simp only [named]
        iframe
        ipureintro
        have hi1 : sint.nat (i + W64 1) = sint.nat i + 1 := by word
        rw [hi1, List.take_add_one, hCi]
        refine ⟨by word, by omega, ?_⟩
        simp only [Option.toList_some, List.any_append, Hany, List.any_cons, List.any_nil, hz,
          Bool.or_false]
      · try wp_auto
        wp_for_post
        have ht : isTorn true off xs = true := by
          unfold isTorn
          simp only [Bool.true_and, List.any_eq_true]
          exact ⟨ys, List.mem_of_getElem? hCi, hz⟩
        rw [ht]
        iapply HΦ
        iframe
    · obtain ⟨Hi0, HiB, Hany⟩ := Hi
      have hi : sint.nat i = (chunkBnds (off + 8) 0 xs.length).length := by
        have : ¬ sint.Z i < sint.Z cs.len := by
          exact Hif
        have := Hcsl.1
        word
      have hCl : (sectorChunks (off + 8) xs).length = (chunkBnds (off + 8) 0 xs.length).length := by
        rw [← hC, List.length_map]
      rw [hi, ← hCl, List.take_length] at Hany
      try wp_auto
      have ht : isTorn true off xs = false := by
        unfold isTorn; rw [Bool.true_and]; exact Hany
      rw [ht]
      iapply HΦ
      iframe

end proof

end EtcdGrove
end Perennial
