/-
The registered codec's decoder of a `[]log.Log` (`examples/vsrnet/json_gen.go`'s `jdec_S_log_Log`,
jsongen's): into a nil `*[]log.Log`, on the encoding of entries with plain operations and ids
below `2^64`, it stores a fresh slice of them (an array loop that appends a zero `log.Log` and
decodes each element in place with `jdec_log_Log`, `LogDec.lean`). Over the specs of `jsoncodec`'s
decoding helpers (section hypotheses). Adapted from dsverify-lab's
`examples/vr/proof/VsrProof/Proof/vsrnetjson/SLogDec.lean` (lab master 915f964; the lab's loop
decoded into a local and appended it).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.LogDec
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.log.Logs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]
variable (wp_At : models_lab.jsoncodec.At.spec (GF := GF) (hG := hG))
variable (wp_Empty : models_lab.jsoncodec.Empty.spec (GF := GF) (hG := hG))
variable (wp_Member : models_lab.jsoncodec.Member.spec (GF := GF) (hG := hG))
variable (wp_Next : models_lab.jsoncodec.Next.spec (GF := GF) (hG := hG))
variable (wp_String : models_lab.jsoncodec.String.spec (GF := GF) (hG := hG))
variable (wp_QuotedUint : models_lab.jsoncodec.QuotedUint.spec (GF := GF) (hG := hG))

set_option goose.wp.extras true

theorem vsrnet.ser_logs_nil : VsrJson.ser (VsrJson.logsJV []) = [91#8, 93#8] := by
  simp [VsrJson.logsJV, VsrJson.mkArr, VsrJson.ser, VsrJson.serVs]

theorem vsrnet.ser_logs_cons (e : Entry) (es : List Entry) :
    VsrJson.ser (VsrJson.logsJV (e :: es)) =
      91#8 :: (VsrJson.ser (VsrJson.logJV e) ++ VsrJson.serVsT (VsrJson.mkArr (es.map VsrJson.logJV)) ++ [93#8]) := by
  simp [VsrJson.logsJV, VsrJson.mkArr, VsrJson.ser_arr, VsrJson.serVs_cons]

theorem vsrnet.serVsT_cons' (e : Entry) (es : List Entry) :
    VsrJson.serVsT (VsrJson.mkArr ((e :: es).map VsrJson.logJV)) =
      44#8 :: (VsrJson.ser (VsrJson.logJV e) ++ VsrJson.serVsT (VsrJson.mkArr (es.map VsrJson.logJV))) := by
  simp [VsrJson.mkArr, VsrJson.serVsT_cons]

theorem vsrnet.serVsT_nil' : VsrJson.serVsT (VsrJson.mkArr (([] : List Entry).map VsrJson.logJV)) = [] := by
  simp [VsrJson.mkArr, VsrJson.serVsT_nil]

theorem vsrnet.ownSlice_nonnil' (sl : GoSlice) (dq : DFrac) (ls : List pkg.log.Log) (h : ls ≠ []) :
    (sl ↦*{dq} ls : IProp GF) ⊢ ⌜sl ≠ slice.nil⌝ := by
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.2 h
  · icases typedPointsto_not_null _ _ _ $$ H with %Hn
    ipureintro; intro he; apply Hn; rw [he]; rfl

theorem vsrnet.wp_make_empty_logs :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.GoType.SliceType pkg.log.Log.ty])) (Val #(W64 0)))
    {{ (sl : GoSlice), RET #sl; sl ↦* ([] : List pkg.log.Log) ∗
        ownSliceCap pkg.log.Log sl (DFrac.own 1) ∗ ⌜sl ≠ slice.nil⌝ }} := by
  wp_start
  wp_func_call
  wp_call
  wp_apply wp_GoPrealloc as %p %hnn
  iapply HΦ
  isplitl []
  · iapply ownSlice_empty _ _ (by rfl) (by word)
    iapply array_empty _ _ hnn
  isplitl []
  · iapply ownSliceCap_empty _ rfl (by word)
  · ipureintro
    intro h
    apply hnn
    exact congrArg GoSlice.ptr h


set_option maxHeartbeats 4000000 in
include wp_At wp_Empty wp_Member wp_Next wp_String wp_QuotedUint in
/-- `jdec_S_log_Log(b, i, p, e)`, `*p` nil, on a `[]Log`'s encoding at `i`. -/
theorem vsrnet.wp_jdec_S_log_Log (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (es : List Entry) (R : List w8)
    (hes : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.logsJV es) ++ R) :
    {{ (b ↦*{dq} bs ∗ p ↦ (slice.nil : GoSlice) : IProp GF) }}
      (App (App (App (App (Val (@! vsrnet.jdec_S_log_Log)) (Val #b)) (Val #i)) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, p ↦ sl ∗ pkg.log.ownLogs sl (DFrac.own 1) es ∗
          ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  obtain ⟨X, hX⟩ : ∃ X, VsrJson.ser (VsrJson.logsJV es) = 91#8 :: X :=
    ⟨_, by simp only [VsrJson.logsJV, VsrJson.ser_arr]; rfl⟩
  have hc0 : bs[uint.nat i]? = some 91#8 := hidx _ _ (X ++ R) (by rw [hb, hX]; rfl)
  have hlen := congrArg List.length hb
  simp only [List.length_drop, List.length_append] at hlen
  have hsl : 2 ≤ (VsrJson.ser (VsrJson.logsJV es)).length := by
    cases es <;> simp [vsrnet.ser_logs_nil, vsrnet.ser_logs_cons] <;> omega
  try wp_auto
  wp_apply (wp_At b dq bs i 91#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide),
    show W64 ((uint.nat i : Nat) : Int) = i by word]
  try wp_auto
  cases es with
  | nil =>
    have hb1 : bs.drop (uint.nat i + 1) = 93#8 :: R := by
      have := vsrnet.drop_app bs [91#8] _ _ (by rw [hb, vsrnet.ser_logs_nil]; rfl); simpa using this
    have hc1 : bs[uint.nat i + 1]? = some 93#8 := hidx _ _ _ hb1
    wp_apply (wp_Empty b dq bs i 93#8 (by omega)
      (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
    rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]
    try simp only [show ((93#8 : w8) = W8 93 ∨ (93#8 : w8) = W8 125) from Or.inl rfl, if_true, ite_true]
    try wp_auto
    wp_apply vsrnet.wp_make_empty_logs as %s0 ⟨Hs0, Hcap0, %hs0⟩
    try wp_auto
    rw [vsrnet.ser_logs_nil]
    rw [show W64 ((uint.nat i + [91#8, 93#8].length : Nat) : Int) = W64 ((uint.nat i + 1 + 1 : Nat) : Int)
      by simp only [List.length_cons, List.length_nil]]
    iapply HΦ
    iframe
    unfold pkg.log.ownLogs
    iexists []
    iframe
    ipureintro; exact ⟨rfl, hs0⟩
  | cons e0 es' =>
    have hb1 : bs.drop (uint.nat i + 1) = VsrJson.ser (VsrJson.logJV e0) ++
        (VsrJson.serVsT (VsrJson.mkArr (es'.map VsrJson.logJV)) ++ 93#8 :: R) := by
      have := vsrnet.drop_app bs [91#8] (VsrJson.ser (VsrJson.logJV e0) ++
        (VsrJson.serVsT (VsrJson.mkArr (es'.map VsrJson.logJV)) ++ 93#8 :: R)) _
        (by rw [hb, vsrnet.ser_logs_cons]; simp)
      simpa using this
    obtain ⟨Y, hY⟩ : ∃ Y, VsrJson.ser (VsrJson.logJV e0) = 123#8 :: Y :=
      ⟨_, by simp only [VsrJson.logJV, VsrJson.ser_obj]; rfl⟩
    have hc1 : bs[uint.nat i + 1]? = some 123#8 := hidx _ _ _ (by rw [hb1, hY]; rfl)
    wp_apply (wp_Empty b dq bs i 123#8 (by omega)
      (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
    try simp only [show ¬((123#8 : w8) = W8 93 ∨ (123#8 : w8) = W8 125) by decide, if_false, ite_false]
    try wp_auto
    wp_apply vsrnet.wp_make_empty_logs as %s0 ⟨Hs0, Hcap0, %hs0⟩
    try wp_auto
    ihave IH : iprop(∃ (m : Nat) (kw : w64) (sl : GoSlice) (ls : List pkg.log.Log),
        "k" ∷ k_ptr ↦ kw ∗ "s" ∷ s_ptr ↦ sl ∗ "Hs0" ∷ sl ↦* ls ∗
        "Hcap0" ∷ ownSliceCap pkg.log.Log sl (DFrac.own 1) ∗
        "%Hm" ∷ ⌜m < (e0 :: es').length ∧ ls.length = m ∧
          ls.map pkg.log.entryOf = (e0 :: es').take m ∧
          ∃ em : Entry, (e0 :: es')[m]? = some em ∧
            bs.drop (uint.nat kw) = VsrJson.ser (VsrJson.logJV em) ++
              (VsrJson.serVsT (VsrJson.mkArr (((e0 :: es').drop (m + 1)).map VsrJson.logJV)) ++
                93#8 :: R) ∧
            uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length +
              (VsrJson.serVsT (VsrJson.mkArr (((e0 :: es').drop (m + 1)).map VsrJson.logJV))).length + 1 =
              uint.nat i + (VsrJson.ser (VsrJson.logsJV (e0 :: es'))).length⌝) $$ [k s Hs0 Hcap0]
    · iexists 0, _, s0, []
      iframe
      ipureintro
      refine ⟨by simp, rfl, rfl, e0, rfl, by rw [show uint.nat (i + W64 1) = uint.nat i + 1 by word]; simpa using hb1, ?_⟩
      rw [vsrnet.ser_logs_cons, show uint.nat (i + W64 1) = uint.nat i + 1 by word]; simp; omega
    wp_for IH
    obtain ⟨hm, hlsl, hls, em, hem, hbk, hpos⟩ := Hm
    have hemm : em ∈ e0 :: es' := List.mem_of_getElem? hem
    obtain ⟨hcid, hreq, hop⟩ := hes em hemm
    wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType pkg.log.Log.ty))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := pkg.log.Log) (t := pkg.log.Log.ty) [_]
    try wp_auto
    rw [show go.arrayLiteralSize
      [KeyedElement none (ElementExpression pkg.log.Log.ty #(zero_val pkg.log.Log))] = 1 from rfl]
    isplitl []
    · ipureintro; rfl
    iintro %slp ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [Hs0 Hcap0 Hsl] as %sl' ⟨Hs0, Hcap0, -⟩
    · iframe
    ihave %Hl' := ownSlice_len $$ Hs0
    simp only [List.length_append, List.length_cons, List.length_nil, hlsl] at Hl'
    try wp_auto
    have hidxm : sint.Z (sl'.len - W64 1) = (m : Int) := by word
    have hbnd : 0 ≤ sint.Z (sl'.len - W64 1) ∧ sint.Z (sl'.len - W64 1) < sint.Z sl'.len := by word
    try rw [ite_eq_left_of_eq_true _ _ (eq_true hbnd)]
    try wp_auto
    have hlook : (ls ++ [zero_val pkg.log.Log])[(sint.Z (sl'.len - W64 1)).toNat]? =
        some (zero_val pkg.log.Log) := by
      rw [hidxm]; simp [hlsl]
    icases ownSlice_elem_acc (sint.Z (sl'.len - W64 1)) _ sl' _ _ hbnd.1 hlook $$ Hs0 with ⟨He, Hs0⟩
    wp_apply (vsrnet.wp_jdec_Log wp_At wp_Empty wp_Member wp_Next wp_String wp_QuotedUint
      b dq bs kw _ e _ em.op em.cid em.req _ hop hcid hreq (by rw [hbk])) $$ [Hs He] as ⟨Hs, He⟩
    · iframe
    ihave Hs0 := Hs0 $$ He
    have hset : (ls ++ [zero_val pkg.log.Log]).set (sint.Z (sl'.len - W64 1)).toNat
        (pkg.log.Log.mk em.op (W64 (em.cid : Int)) (W64 (em.req : Int))) =
        ls ++ [pkg.log.Log.mk em.op (W64 (em.cid : Int)) (W64 (em.req : Int))] := by
      rw [hidxm]; simp [List.set_append, hlsl]
    rw [hset]
    have hx : pkg.log.entryOf (pkg.log.Log.mk em.op (W64 (em.cid : Int)) (W64 (em.req : Int))) = em := by
      obtain ⟨o, c, r⟩ := em
      show (⟨o, uint.nat (W64 (c : Int)), uint.nat (W64 (r : Int))⟩ : Entry) = ⟨o, c, r⟩
      simp only at hcid hreq
      rw [show uint.nat (W64 (c : Int)) = c by word, show uint.nat (W64 (r : Int)) = r by word]
    have hls' : (ls ++ [pkg.log.Log.mk em.op (W64 (em.cid : Int)) (W64 (em.req : Int))]).map
        pkg.log.entryOf = (e0 :: es').take (m + 1) := by
      rw [List.map_append, hls, List.take_succ, hem]
      simp only [List.map_cons, List.map_nil, hx, Option.toList_some]
    rcases hd : (e0 :: es').drop (m + 1) with _ | ⟨en, rest'⟩
    · rw [hd, vsrnet.serVsT_nil'] at hbk hpos
      simp only [List.nil_append, List.length_nil] at hbk hpos
      have hc : bs[uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length]? = some 93#8 :=
        hidx _ _ R (by rw [← List.drop_drop, hbk]; simp)
      have hez : uint.nat (W64 ↑(uint.nat kw + (VsrJson.ser (VsrJson.logJV
          { op := em.op, cid := em.cid, req := em.req })).length)) =
          uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length := by
        rw [show (VsrJson.logJV { op := em.op, cid := em.cid, req := em.req }) = VsrJson.logJV em from rfl]
        have := congrArg List.length hbk; simp at this
        have : uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length ≤ bs.length := by omega
        word
      wp_apply (wp_Next b dq bs _ 93#8
        (by rw [hez]; have := congrArg List.length hbk; simp at this; omega)
        (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
      rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
      try wp_auto
      wp_for_post
      have hall : (e0 :: es').take (m + 1) = e0 :: es' := by
        apply List.take_of_length_le
        have := List.drop_eq_nil_iff.1 hd; omega
      rw [hall] at hls'
      ihave %Hne := vsrnet.ownSlice_nonnil' sl' _ (ls ++ [_]) (by simp) $$ Hs0
      rw [show W64 ((uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length + 1 : Nat) : Int) =
        W64 ((uint.nat i + (VsrJson.ser (VsrJson.logsJV (e0 :: es'))).length : Nat) : Int) by
        congr 2]
      iapply HΦ
      iframe
      unfold pkg.log.ownLogs
      iexists _
      iframe
      ipureintro; exact ⟨hls', Hne⟩
    · rw [hd, vsrnet.serVsT_cons'] at hbk hpos
      have hc : bs[uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length]? = some 44#8 :=
        hidx _ _ (VsrJson.ser (VsrJson.logJV en) ++
          (VsrJson.serVsT (VsrJson.mkArr (List.map VsrJson.logJV rest')) ++ 93#8 :: R))
          (by rw [← List.drop_drop, hbk]; simp)
      have hez : uint.nat (W64 ↑(uint.nat kw + (VsrJson.ser (VsrJson.logJV
          { op := em.op, cid := em.cid, req := em.req })).length)) =
          uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length := by
        rw [show (VsrJson.logJV { op := em.op, cid := em.cid, req := em.req }) = VsrJson.logJV em from rfl]
        have := congrArg List.length hbk; simp at this
        have : uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length ≤ bs.length := by omega
        word
      wp_apply (wp_Next b dq bs _ 44#8
        (by rw [hez]; have := congrArg List.length hbk; simp at this; omega)
        (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
      rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
      try wp_auto
      wp_for_post
      iframe
      iexists m + 1, _, sl', _
      iframe
      ipureintro
      have hen : (e0 :: es')[m + 1]? = some en := by
        have := congrArg (fun l => l[0]?) hd; simp only [List.getElem?_drop] at this; simpa using this
      have hd2 : (e0 :: es').drop (m + 1 + 1) = rest' := by
        rw [← List.drop_drop, hd]; simp
      have hmlt : m + 1 < (e0 :: es').length := by
        rcases Nat.lt_or_ge (m + 1) (e0 :: es').length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hen; cases hen
      have hbk' := vsrnet.drop_app bs (VsrJson.ser (VsrJson.logJV em) ++ [44#8]) (VsrJson.ser (VsrJson.logJV en) ++
          (VsrJson.serVsT (VsrJson.mkArr (List.map VsrJson.logJV rest')) ++ 93#8 :: R)) _
        (by rw [hbk]; simp)
      simp only [List.length_append, List.length_cons, List.length_nil] at hbk' hpos
      refine ⟨hmlt, by simp [hlsl], hls', en, hen, ?_, ?_⟩
      · rw [hd2, show uint.nat (W64 ↑(uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length + 1)) =
          uint.nat kw + ((VsrJson.ser (VsrJson.logJV em)).length + (0 + 1)) by
            have := congrArg List.length hbk; simp at this; word]
        exact hbk'
      · rw [hd2, show uint.nat (W64 ↑(uint.nat kw + (VsrJson.ser (VsrJson.logJV em)).length + 1)) =
          uint.nat kw + ((VsrJson.ser (VsrJson.logJV em)).length + (0 + 1)) by
            have := congrArg List.length hbk; simp at this; word]
        omega

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
