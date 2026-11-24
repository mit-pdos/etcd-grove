/-
The registered codec's encoders of a `log.Log` and a `[]log.Log` (`examples/vsrnet/json_gen.go`'s
`jenc_log_Log`, `jenc_S_log_Log`, jsongen's) on entries with plain operations: they append
`VsrJson.ser (VsrJson.logJV e)` and `VsrJson.ser (VsrJson.logsJV es)` (`log.encLogs es`), with no
error (the nesting is far below the depth limits). Over the specs of `jsoncodec`'s `AppendRaw`,
`AppendQuotedUint` and `AppendString` (plain subset). Ported from dsverify-lab's
`examples/vr/proof/VsrProof/Proof/vsrnetjson/{EncFlat,EncLogs}.lean` (`wp_jenc_Log`,
`wp_jenc_S_log_Log`; lab master 915f964; the depth arguments are new).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.examples.vsrnet.Base
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Facts
public import Net.Spec.models_lab.jsoncodec.AppendRaw
public import Net.Spec.models_lab.jsoncodec.AppendQuotedUint
public import Net.Spec.models_lab.jsoncodec.AppendString

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false
set_option maxHeartbeats 2000000

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem vsrnet.serVsT_snoc (l : List Entry) (e : Entry) :
    VsrJson.serVsT (VsrJson.mkArr ((l ++ [e]).map VsrJson.logJV)) =
      VsrJson.serVsT (VsrJson.mkArr (l.map VsrJson.logJV)) ++ 44#8 :: VsrJson.ser (VsrJson.logJV e) := by
  induction l with
  | nil => simp [VsrJson.mkArr, VsrJson.serVsT]
  | cons a l ih =>
    simp only [List.cons_append, List.map_cons, VsrJson.mkArr, VsrJson.serVsT] at ih ⊢
    rw [ih]; simp

theorem vsrnet.serVs_snoc (l : List Entry) (e : Entry) :
    VsrJson.serVs (VsrJson.mkArr ((l ++ [e]).map VsrJson.logJV)) =
      VsrJson.serVs (VsrJson.mkArr (l.map VsrJson.logJV)) ++
        ((if l = [] then [] else [44#8]) ++ VsrJson.ser (VsrJson.logJV e)) := by
  cases l with
  | nil => simp [VsrJson.mkArr, VsrJson.serVs, VsrJson.serVsT]
  | cons a l =>
    simp only [List.cons_append, List.map_cons, VsrJson.mkArr, VsrJson.serVs]
    have := vsrnet.serVsT_snoc l e
    simp only [List.map_append, List.map_cons, List.map_nil] at this ⊢
    rw [this]; simp

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]
variable (wp_AppendRaw : models_lab.jsoncodec.AppendRaw.spec (GF := GF) (hG := hG))
variable (wp_AppendQuotedUint : models_lab.jsoncodec.AppendQuotedUint.spec (GF := GF) (hG := hG))
variable (wp_AppendString : models_lab.jsoncodec.AppendString.spec (GF := GF) (hG := hG))

set_option goose.wp.extras true

include wp_AppendRaw wp_AppendQuotedUint wp_AppendString in
theorem vsrnet.wp_jenc_Log (b : GoSlice) (bs : List w8) (x : pkg.log.Log) (d : w64)
    (hd : uint.nat d < 10000) (hop : PlainStr x.Data') :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! vsrnet.jenc_log_Log)) (Val #b)) (Val #x)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.logJV (pkg.log.entryOf x))) ∗
        ownSliceCap w8 b' (DFrac.own 1) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_if_destruct
  · exfalso; simp only [models_lab.jsoncodec.MaxDepth] at *; word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 123]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  repeat (first
    | wp_apply (wp_AppendRaw _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (wp_AppendQuotedUint _ _ _) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    | wp_apply (wp_AppendString _ _ _ (by assumption)) $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap⟩
    ; try wp_auto)
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 125]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  iapply HΦ
  simp only [VsrJson.ser, VsrJson.payJV, VsrJson.reqJV, pkg.log.entryOf, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs,
    VsrJson.serMsT, VsrJson.qn, VsrJson.cQ, VsrJson.cColon, VsrJson.cComma, VsrJson.cLB,
    VsrJson.cRB, List.append_assoc, List.cons_append, List.nil_append, List.singleton_append,
    show (W8 123 : w8) = 123#8 from rfl, show (W8 125 : w8) = 125#8 from rfl]
  iframe


include wp_AppendRaw wp_AppendQuotedUint wp_AppendString in
theorem vsrnet.wp_jenc_S_log_Log (b : GoSlice) (bs : List w8) (sl : GoSlice) (dq : DFrac)
    (es : List Entry) (d : w64) (hd : uint.nat d < 1000) (hes : ∀ e ∈ es, PlainStr e.op) :
    {{ (pkg.log.ownLogs sl dq es ∗ b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) }}
      (App (App (App (Val (@! vsrnet.jenc_S_log_Log)) (Val #b)) (Val #sl)) (Val #d))
    {{ (b' : GoSlice), RET (PairV #b' #(interface.nil : GoInterface));
        b' ↦* (bs ++ VsrJson.ser (VsrJson.logsJV es)) ∗ ownSliceCap w8 b' (DFrac.own 1) ∗
        pkg.log.ownLogs sl dq es }} := by
  wp_start as ⟨Hl, Hb, Hcap⟩
  unfold pkg.log.ownLogs
  icases Hl with ⟨%ls, Hls, %hls, %hnn⟩
  wp_auto
  rw [decide_eq_false hnn]
  wp_auto
  wp_if_destruct
  · exfalso; simp only [vsrnet.jsonCycleDepth] at *; word
  try wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w8) (t := go.byte) [W8 91]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit ⟨Hlit, -⟩
  wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
  try wp_auto
  rename_i iu_ptr
  irename : (iu_ptr ↦ zero_val w64) => iu
  ihave %Hlen := ownSlice_len $$ Hls
  ihave %Hwf := ownSlice_wf $$ Hls
  ihave IH : iprop(∃ (k : w64) (o : GoSlice) (xv : pkg.log.Log) (iv : w64),
      "i" ∷ i_ptr ↦ k ∗ "b" ∷ b_ptr ↦ o ∗
      "Hb" ∷ o ↦* (bs ++ 91#8 :: VsrJson.serVs (VsrJson.mkArr ((es.take (uint.nat k)).map VsrJson.logJV))) ∗
      "Hcap" ∷ ownSliceCap w8 o (DFrac.own 1) ∗ "x" ∷ x_ptr ↦ xv ∗ "iu" ∷ iu_ptr ↦ iv ∗
      "err" ∷ err_ptr ↦ (interface.nil : GoInterface) ∗ "Hls" ∷ sl ↦*{dq} ls ∗
      "%Hk" ∷ ⌜uint.nat k ≤ ls.length⌝) $$ [i b Hb Hcap x iu err Hls]
  · iexists _, _, _, _
    iframe
    rw [show uint.nat (W64 0) = 0 by rfl]
    simp only [List.take_zero, List.map_nil, VsrJson.mkArr, VsrJson.serVs]
    simp only [show (W8 91 : w8) = 91#8 from rfl, List.singleton_append]
    iframe
    ipureintro; omega
  wp_for IH
  wp_if_destruct
  · have Hlt : uint.nat k < ls.length := by word
    obtain ⟨xl, Hx⟩ : ∃ xl, ls[uint.nat k]? = some xl := ⟨_, List.getElem?_eq_getElem Hlt⟩
    have hb : 0 ≤ sint.Z k ∧ sint.Z k < sint.Z sl.len := by word
    have hnz : (sint.Z k).toNat = uint.nat k := by word
    have hes' : es.take (uint.nat k + 1) = es.take (uint.nat k) ++ [pkg.log.entryOf xl] := by
      rw [← hls, List.take_succ, ← List.map_take]
      simp [List.getElem?_map, Hx]
    have hpl : PlainStr xl.Data' :=
      hes (pkg.log.entryOf xl) (by rw [← hls]; exact List.mem_map_of_mem (List.mem_of_getElem? Hx))
    try wp_auto
    rw [if_pos hb]
    wp_apply wp_load_slice_index sl (sint.Z k) ls dq xl hb.1 $$ [Hls] as Hls
    · iframe; ipureintro; rw [hnz]; exact Hx
    try wp_auto
    wp_if_destruct
    · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
        (Val (LiteralValueV _)))
      iapply wp_slice_literal (V := w8) (t := go.byte) [W8 44]
      wp_auto
      isplitl []
      · ipureintro; rfl
      iintro %lit ⟨Hlit, -⟩
      wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
      try wp_auto
      wp_apply (vsrnet.wp_jenc_Log wp_AppendRaw wp_AppendQuotedUint wp_AppendString _ _ xl _ (by word) hpl) $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      rw [show uint.nat (k + W64 1) = uint.nat k + 1 by word, hes', vsrnet.serVs_snoc]
      have hne : (List.take (uint.nat k) es = []) ↔ uint.nat k = 0 := by
        rw [List.take_eq_nil_iff]; constructor
        · rintro (h | h)
          · exact h
          · rw [← hls] at h; simp at h; subst h; simp at Hlt
        · intro h; left; exact h
      rw [if_neg (by rw [hne]; word)]
      simp only [List.append_assoc, List.cons_append, List.singleton_append,
        show (W8 44 : w8) = 44#8 from rfl]
      iframe
      ipureintro; word
    · try wp_auto
      wp_apply (vsrnet.wp_jenc_Log wp_AppendRaw wp_AppendQuotedUint wp_AppendString _ _ xl _ (by word) hpl) $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap⟩
      try wp_auto
      wp_for_post
      iframe
      iexists _, _, _, _
      iframe
      rw [show uint.nat (k + W64 1) = uint.nat k + 1 by word, hes', vsrnet.serVs_snoc]
      have hne : (List.take (uint.nat k) es = []) ↔ uint.nat k = 0 := by
        rw [List.take_eq_nil_iff]; constructor
        · rintro (h | h)
          · exact h
          · rw [← hls] at h; simp at h; subst h; simp at Hlt
        · intro h; left; exact h
      rw [if_pos (by rw [hne]; word)]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      iframe
      ipureintro; word
  · have hk : uint.nat k = ls.length := by word
    have hes2 : es.take (uint.nat k) = es := by
      rw [hk, ← hls]; exact List.take_of_length_le (by simp)
    rw [hes2]
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 93]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit ⟨Hlit, -⟩
    wp_apply wp_slice_append (V := w8) _ _ _ _ _ $$ [$Hb $Hcap $Hlit] as %b' ⟨Hb, Hcap, -⟩
    try wp_auto
    iapply HΦ
    simp only [VsrJson.ser, VsrJson.logsJV, List.append_assoc, List.cons_append,
      show (W8 93 : w8) = 93#8 from rfl, VsrJson.cLS, VsrJson.cRS]
    iframe
    ipureintro; exact ⟨hls, hnn⟩

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
