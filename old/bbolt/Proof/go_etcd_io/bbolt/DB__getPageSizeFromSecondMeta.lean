module
public import Spec.go_etcd_io.bbolt.DB__getPageSizeFromSecondMeta
public import Spec.go_etcd_io.bbolt.DB__pageInBuffer
public import Spec.go_etcd_io.bbolt.internal.common.Page__Meta
public import Spec.go_etcd_io.bbolt.internal.common.Meta__PageSize
public import Spec.os.File__ReadAt
public import Spec.os.File__Stat
public import Spec.io.fs.FileInfo__Size
public import Proof.go_etcd_io.bbolt.ErrShape
public import Proof.go_etcd_io.bbolt.MetaBuf
public import Perennial.Proof.io

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI Iris.ProofMode go_etcd_io.bbolt

section pure

/-- The buffer after a read at `pos` of `k` bytes, all there were (4096, or the rest of the
file): the probe. -/
theorem probe_buf (bs : List w8) (pos k : Nat)
    (hk : k ≤ ((bs.drop pos).take 4096).length) (h : k = 4096 ∨ k = bs.length - pos) :
    (bs.drop pos).take k ++ (List.replicate 4096 (W8 0)).drop k = probeAt bs pos := by
  unfold probeAt
  rw [List.length_take, List.length_drop] at hk
  rw [List.drop_replicate, List.length_take, List.length_drop]
  rcases h with rfl | rfl
  · congr 2; omega
  · rw [List.take_of_length_le (by rw [List.length_drop]; omega : (bs.drop pos).length ≤ bs.length - pos),
      List.take_of_length_le (by rw [List.length_drop]; omega : (bs.drop pos).length ≤ 4096)]
    congr 2; omega

theorem probeAt_length (bs : List w8) (pos : Nat) : (probeAt bs pos).length = 4096 := by
  unfold probeAt
  rw [List.length_append, List.length_replicate, List.length_take]
  omega

theorem shl_1024 (j : w64) (h0 : 0 ≤ sint.Z j) (h14 : sint.Z j ≤ 14) :
    sint.Z (W64 1024 <<< j) = ((1024 * 2 ^ (sint.nat j) : Nat) : Int) := by
  have hj : j = W64 (sint.nat j : Int) := by word
  have hn : sint.nat j ≤ 14 := by word
  generalize sint.nat j = n at hj hn ⊢
  subst hj
  obtain rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 12 ∨ n = 13 ∨ n = 14 := by omega
  all_goals rfl

theorem len_sub_1024 (n : Nat) (h : n < 2 ^ 62) :
    sint.Z (W64 (n : Int) - W64 1024) = n - 1024 := by
  word

theorem k_4096 (k : Nat) (h : W64 (k : Int) = W64 4096) (hk : k ≤ 4096) : k = 4096 := by
  word

theorem sint_nat_of_cast (x : w64) (n : Nat) (h : sint.Z x = (n : Int)) : sint.nat x = n := by
  word

theorem meta_ps_z (v : w32) :
    sint.Z (W64 (uint.Z v)) = uint.Z v := by
  word

theorem probe_lt (x : w64) (P len : Nat) (hpos : sint.Z x = (P : Int))
    (hfs : sint.Z (W64 (len : Int) - W64 1024) = len - 1024)
    (hb : ¬ sint.Z (W64 (len : Int) - W64 1024) ≤ sint.Z x) : P + 1024 < len := by
  omega

theorem sint_nat_lt15 (j : w64) (h0 : 0 ≤ sint.Z j) (h14 : sint.Z j ≤ 14) : sint.nat j < 15 := by
  word

theorem j_succ (j : w64) (h0 : 0 ≤ sint.Z j) (h14 : sint.Z j ≤ 14) :
    0 ≤ sint.Z (j + W64 1) ∧ sint.Z (j + W64 1) ≤ 15 := by
  word

theorem k_rest (k len P : Nat) (x : w64) (h : W64 (k : Int) = W64 (len : Int) - x)
    (hx : sint.Z x = (P : Int)) (hk : k ≤ 4096) (hl : len < 2 ^ 62) (hP : P + 1024 < len) :
    k = len - P := by
  word

end pure

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]
variable [hash_sem : _root_.Perennial.hash.Hash64.TypeAssumptions]
variable [os_fi : OsFileInfoAssumptions (GF := GF)]

/-- `io`'s initialization: its `EOF`. -/
theorem io_isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.io ⊢ io.isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.io

theorem DB.getPageSizeFromSecondMeta.wp_proof (hStat : os.File.Stat.spec (GF := GF) (hG := hG))
    (hSize : fs.FileInfo.Size.spec (GF := GF) (hG := hG))
    (hReadAt : os.File.ReadAt.spec (GF := GF) (hG := hG))
    (hpib : DB.pageInBuffer.spec (GF := GF) (hG := hG))
    (hMeta : Page.Meta.spec (GF := GF) (hG := hG))
    (hValidate : Meta.Validate.spec (GF := GF) (hG := hG))
    (hPageSize : Meta.PageSize.spec (GF := GF) (hG := hG)) :
    DB.getPageSizeFromSecondMeta.spec (GF := GF) (hG := hG) := by
  intro dbl f fd bs ps dq Hbl
  wp_start as ⟨Hf, Hps, #Hof, Hfb⟩
  ihave #Hei : (isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt.errors) $$ []
  · iPkgInit
  icases bboltError_access errors.ErrInvalid (by simp [bboltErrorNames]) $$ Hei
    with ⟨%e, #He, %Hne⟩
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  icases io_isInit_access $$ Hio with ⟨%eof, #Heof, %Heofp⟩
  wp_auto
  wp_apply hStat f fd bs $$ [Hfb] as %fi %err ⟨Hfb, Hfi⟩
  · iframe; iframe #
  try wp_auto
  icases Hfi with (%Herr | ⟨%Herr, #Hfi⟩)
  · cases err with
    | nil => exact absurd rfl Herr.1
    | ok ei =>
      -- `Stat` failed: its error
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      right
      exact Herr
  subst Herr
  try wp_auto
  wp_apply hSize fi bs.length $$ [Hfi]
  · iexact Hfi
  try wp_auto
  obtain ⟨t', p', rfl⟩ := Hne
  ihave IH : iprop(∃ (j : w64) (cr : Bool), "i" ∷ i_ptr ↦ j ∗
      "metaCanRead" ∷ metaCanRead_ptr ↦ cr ∗ "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 15⌝ ∗
      "Hf" ∷ structFieldRef DB go!"file" dbl ↦{dq} f ∗
      "Hps" ∷ structFieldRef DB go!"pageSize" dbl ↦{dq} ps ∗ "Hfb" ∷ fileBytes fd bs ∗
      "db" ∷ db_ptr ↦ dbl ∗ "fileSize" ∷ fileSize_ptr ↦ W64 (bs.length : Int))
    $$ [i metaCanRead Hf Hps Hfb db fileSize]
  · iexists (W64 0), (zero_val Bool); iframe; ipureintro; decide
  wp_for IH
  have h14 : sint.Z (W64 14) = 14 := by word
  by_cases hj : sint.Z j ≤ 14
  · rw [h14, decide_eq_true hj]
    simp only [↓reduceIte]
    try wp_auto
    have hpos := shl_1024 j Hj.1 hj
    have hfs := len_sub_1024 bs.length Hbl
    by_cases hb : sint.Z (W64 (bs.length : Int) - W64 1024) ≤ sint.Z (W64 1024 <<< j)
    · -- past the file's last KiB: no meta found
      rw [decide_eq_true hb]
      try wp_auto
      wp_for_post
      try wp_auto
      iapply HΦ
      iframe
      ipureintro
      right
      exact ⟨fun h => (by cases h), errWF_newErr _ ⟨t', p', rfl⟩⟩
    rw [decide_eq_false hb]
    try wp_auto
    try rw [show sint.Z (W64 0) = 0 from rfl, arrayIndexRef_zero,
      show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
    have hz : (zero_val (GoArray w8 4096)).arr = List.replicate 4096 (W8 0) := by
      first | rfl | simp [zero_val]
    ihave Hsl := slice_array buf_ptr 4096 (zero_val (GoArray w8 4096))
      (by rw [hz, List.length_replicate]; omega) $$ buf
    rw [hz] at *
    have hposZ : 0 ≤ sint.Z (W64 1024 <<< j) := by rw [hpos]; omega
    have hposn := sint_nat_of_cast _ _ hpos
    wp_apply hReadAt f fd bs _ _ (W64 1024 <<< j) hposZ $$ [Hof Hfb Hsl]
      as %n %err ⟨%k, %hk, Hfb, Hsl⟩
    · iframe; iframe #
    try wp_auto
    obtain ⟨hk1, rfl, hk3, hwf⟩ := hk
    cases err with
    | nil =>
      try wp_auto
      have hk4b : k ≤ 4096 := by
        have := hk1; rw [List.length_replicate, List.length_take] at this; omega
      by_cases hk4 : W64 (k : Int) = W64 4096
      · rw [decide_eq_true hk4]
        have hk' := k_4096 k hk4 hk4b
        have hbuf := probe_buf bs _ k (by rw [List.length_replicate] at hk1; exact hk1) (Or.inl hk')
        rw [hbuf]
        try wp_auto
        try rw [show sint.Z (W64 0) = 0 from rfl, arrayIndexRef_zero,
          show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
        have hne : probeAt bs (sint.nat (W64 1024 <<< j)) ≠ [] :=
          List.ne_nil_of_length_pos (by rw [probeAt_length]; omega)
        icases (ownSlice_bytes _ _ _ hne).1 $$ Hsl with ⟨Hsl, %Hslen⟩
        icases persistent_entails_left (bytesPointsto_car buf_ptr _ _ hne) $$ Hsl with ⟨Hsl, %Hcar⟩
        wp_apply hpib dbl ps dq _ (W64 0) Hcar (by word) (by word) $$ [Hps] as Hps
        · iframe
        try wp_auto
        wp_apply hMeta _
        try wp_auto
        rw [show sint.Z (W64 0 * ps) = 0 by word]
        icases meta_in_bytes buf_ptr (DFrac.own 1) _ 16 (by rw [probeAt_length]; omega) Hcar $$ Hsl
          with ⟨HM, Hback⟩
        rw [show buf_ptr +ₗ 0 +ₗ 16 = buf_ptr +ₗ ((16 : Nat) : Int) by simp [Loc.add]]
        wp_apply hValidate _ _ _ (by simpa [Loc.add] using Hcar) $$ [HM] as %e1 ⟨HM, %He1⟩
        · iframe
        try wp_auto
        cases e1 with
        | nil =>
          try wp_auto
          wp_apply hPageSize _ _ _ $$ [HM] as HM
          · iframe
          try wp_auto
          try wp_for_post
          try wp_auto
          iapply HΦ
          iframe
          ipureintro
          left
          refine ⟨rfl, sint.nat j, sint_nat_lt15 j Hj.1 hj, probe_lt _ _ _ hpos hfs hb,
            by rw [← hposn]; exact He1.1.1 rfl, ?_⟩
          rw [← hposn]
          exact meta_ps_z _
        | ok _ =>
          try wp_auto
          try wp_auto
          wp_for_post
          try wp_auto
          iframe
          iexists _, _
          iframe
          ipureintro
          exact j_succ j Hj.1 hj
      · rw [decide_eq_false hk4]
        try wp_auto
        wp_for_post
        try wp_auto
        iframe
        iexists _, _
        iframe
        ipureintro
        exact j_succ j Hj.1 hj
    | ok ei =>
      try wp_auto
      obtain ⟨te, pe, rfl⟩ := Heofp
      rcases hwf ei rfl with ⟨tp, l, hty, hv⟩ | ⟨x, hty, hv⟩
      · cases ei
        simp only at hty hv
        subst hty hv
        simp only
        by_cases htt : tp = te
        · subst htt
          rw [if_pos rfl]
          try wp_auto
          by_cases hl : l = pe
          · rw [decide_eq_true hl]
            try wp_auto
            have hk4b : k ≤ 4096 := by
              have := hk1; rw [List.length_replicate, List.length_take] at this; omega
            have hlt := probe_lt _ _ _ hpos hfs hb
            by_cases hr : W64 (k : Int) = W64 (bs.length : Int) - W64 1024 <<< j
            · rw [decide_eq_true hr]
              have hk' := k_rest k bs.length _ _ hr hpos hk4b Hbl hlt
              have hbuf := probe_buf bs _ k (by rw [List.length_replicate] at hk1; exact hk1)
                (Or.inr (by rw [hposn]; exact hk'))
              rw [hbuf]
              try wp_auto
              try rw [show sint.Z (W64 0) = 0 from rfl, arrayIndexRef_zero,
                show (W64 4096 - W64 0 : w64) = W64 4096 from rfl]
              have hne : probeAt bs (sint.nat (W64 1024 <<< j)) ≠ [] :=
                List.ne_nil_of_length_pos (by rw [probeAt_length]; omega)
              icases (ownSlice_bytes _ _ _ hne).1 $$ Hsl with ⟨Hsl, %Hslen⟩
              icases persistent_entails_left (bytesPointsto_car buf_ptr _ _ hne) $$ Hsl with ⟨Hsl, %Hcar⟩
              wp_apply hpib dbl ps dq _ (W64 0) Hcar (by word) (by word) $$ [Hps] as Hps
              · iframe
              try wp_auto
              wp_apply hMeta _
              try wp_auto
              rw [show sint.Z (W64 0 * ps) = 0 by word]
              icases meta_in_bytes buf_ptr (DFrac.own 1) _ 16 (by rw [probeAt_length]; omega) Hcar $$ Hsl
                with ⟨HM, Hback⟩
              rw [show buf_ptr +ₗ 0 +ₗ 16 = buf_ptr +ₗ ((16 : Nat) : Int) by simp [Loc.add]]
              wp_apply hValidate _ _ _ (by simpa [Loc.add] using Hcar) $$ [HM] as %e1 ⟨HM, %He1⟩
              · iframe
              try wp_auto
              cases e1 with
              | nil =>
                try wp_auto
                wp_apply hPageSize _ _ _ $$ [HM] as HM
                · iframe
                try wp_auto
                try wp_for_post
                try wp_auto
                iapply HΦ
                iframe
                ipureintro
                left
                refine ⟨rfl, sint.nat j, sint_nat_lt15 j Hj.1 hj, probe_lt _ _ _ hpos hfs hb,
                  by rw [← hposn]; exact He1.1.1 rfl, ?_⟩
                rw [← hposn]
                exact meta_ps_z _
              | ok _ =>
                try wp_auto
                try wp_auto
                wp_for_post
                try wp_auto
                iframe
                iexists _, _
                iframe
                ipureintro
                exact j_succ j Hj.1 hj
            · rw [decide_eq_false hr]
              try wp_auto
              wp_for_post
              try wp_auto
              iframe
              iexists _, _
              iframe
              ipureintro
              exact j_succ j Hj.1 hj
          · rw [decide_eq_false hl]
            try wp_auto
            wp_for_post
            try wp_auto
            iframe
            iexists _, _
            iframe
            ipureintro
            exact j_succ j Hj.1 hj
        · rw [if_neg (by simp [htt])]
          try wp_auto
          wp_for_post
          try wp_auto
          iframe
          iexists _, _
          iframe
          ipureintro
          exact j_succ j Hj.1 hj
      · cases ei
        simp only at hty hv
        subst hty hv
        simp only
        rw [if_neg (by simp [_root_.Perennial.syscall.Errno.ty])]
        try wp_auto
        wp_for_post
        try wp_auto
        iframe
        iexists _, _
        iframe
        ipureintro
        exact j_succ j Hj.1 hj
  · rw [h14, decide_eq_false hj]
    simp only [Bool.false_eq_true, ↓reduceIte]
    try wp_auto
    iapply HΦ
    iframe
    ipureintro
    right
    exact ⟨fun h => (by cases h), errWF_newErr _ ⟨t', p', rfl⟩⟩

end proof

end bbolt
end EtcdGrove
end Perennial
