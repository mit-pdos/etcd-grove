/-
The registered codec's decoder of a `log.Log` (`examples/vsrnet/json_gen.go`'s `jdec_log_Log`,
`jdecMember_log_Log`, jsongen's): on the encoding of an entry with a plain operation and ids below
`2^64` it stores the entry. Over the specs of `jsoncodec`'s decoding helpers
(`Net/Spec/models_lab/jsoncodec/`), section hypotheses here, linked in `examples/vsrnet/Link.lean`.
Ported from dsverify-lab's `examples/vr/proof/VsrProof/Proof/vsrnetjson/DecFlat.lean` (`wp_jdec_Log`,
`wp_jdecMember_Log_*`; lab master 915f964).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.jsoncodec.Facts
public import Net.Spec.models_lab.jsoncodec.At
public import Net.Spec.models_lab.jsoncodec.Empty
public import Net.Spec.models_lab.jsoncodec.Member
public import Net.Spec.models_lab.jsoncodec.Next
public import Net.Spec.models_lab.jsoncodec.String
public import Net.Spec.models_lab.jsoncodec.QuotedUint
public import Net.Proof.models_lab.jsoncodec.DecBase

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.iris.style.nameCheck false
set_option maxHeartbeats 2000000

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- `bs` from `i + |A|` on, when `bs` from `i` on is `A ++ B`. -/
theorem vsrnet.drop_app (bs A B : List w8) (i : Nat) (h : bs.drop i = A ++ B) :
    bs.drop (i + A.length) = B := by
  rw [← List.drop_drop, h]; simp

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

/-- `jdecMember_log_Log(b, i, "data", p, e)` on a plain string at `i`. -/
include wp_String in
theorem vsrnet.wp_jdecMember_Log_0 (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.log.Log) (str rest : List w8) (hs : ∀ c ∈ str, JsonScan.okB c)
    (hb : bs.drop (uint.nat i) = 34#8 :: (str ++ 34#8 :: rest)) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! vsrnet.jdecMember_log_Log)) (Val #b)) (Val #i))
        (Val #(go!"data"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + 1 + str.length + 1 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with Data' := str } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (wp_String b dq bs i str rest hs hb) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_log_Log(b, i, "client_id", p, e)` on `"n"` at `i`. -/
include wp_QuotedUint in
theorem vsrnet.wp_jdecMember_Log_1 (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.log.Log) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! vsrnet.jdecMember_log_Log)) (Val #b)) (Val #i))
        (Val #(go!"client_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ClientID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (wp_QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_log_Log(b, i, "request_id", p, e)` on `"n"` at `i`. -/
include wp_QuotedUint in
theorem vsrnet.wp_jdecMember_Log_2 (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.log.Log) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! vsrnet.jdecMember_log_Log)) (Val #b)) (Val #i))
        (Val #(go!"request_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with RequestID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (wp_QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_log_Log(b, i, p, e)` on the encoding at `i`. -/
include wp_At wp_Empty wp_Member wp_Next wp_String wp_QuotedUint in
theorem vsrnet.wp_jdec_Log (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.log.Log) (op : List w8) (cid : Nat) (req : Nat) (rest : List w8)
    (h_op : PlainStr op) (h_cid : cid < 2 ^ 64) (h_req : req < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.logJV ⟨op, cid, req⟩) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! vsrnet.jdec_log_Log)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.logJV ⟨op, cid, req⟩)).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.log.Log.mk op (W64 (cid : Int)) (W64 (req : Int)) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.logJV ⟨op, cid, req⟩) =
      [123#8] ++ ((34#8 :: (go!"data" ++ [34#8, 58#8])) ++ ((34#8 :: (op ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"client_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN cid ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"request_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN req ++ [34#8])) ++ [125#8])))))))) := by
    simp [VsrJson.ser, VsrJson.logJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  have hpl_op := VsrJson.plain_okB op h_op
  generalize hM0 : (34#8 :: (go!"data" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (op ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"client_id" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN cid ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"request_id" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN req ++ [34#8])) = V2 at hb
  simp only [List.append_assoc] at hb
  have hb1 := vsrnet.drop_app bs _ _ _ hb
  have hb2 := vsrnet.drop_app bs _ _ _ hb1
  have hb3 := vsrnet.drop_app bs _ _ _ hb2
  have hb4 := vsrnet.drop_app bs _ _ _ hb3
  have hb5 := vsrnet.drop_app bs _ _ _ hb4
  have hb6 := vsrnet.drop_app bs _ _ _ hb5
  have hb7 := vsrnet.drop_app bs _ _ _ hb6
  have hb8 := vsrnet.drop_app bs _ _ _ hb7
  have hb9 := vsrnet.drop_app bs _ _ _ hb8
  have lM0 : M0.length = 7 := by rw [← hM0]; rfl
  have lV0 : V0.length = op.length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 12 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN cid).length + 2 := by rw [← hV1]; simp
  have lM2 : M2.length = 13 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN req).length + 2 := by rw [← hV2]; simp
  have lser : (VsrJson.ser (VsrJson.logJV ⟨op, cid, req⟩)).length = 1 + 7 + V0.length + 1 + 12 + V1.length + 1 + 13 + V2.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb9
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (wp_At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (wp_Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.log.Log),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 7 + V0.length + 1 ∧ rr = pkg.log.Log.mk op r.ClientID' r.RequestID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 7 + V0.length + 1 + 12 + V1.length + 1 ∧ rr = pkg.log.Log.mk op (W64 (cid : Int)) r.RequestID')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"data" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (wp_Member b dq bs kw go!"data" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 7 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 : Nat) : Int))) =
        34#8 :: (op ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_Log_0 wp_String b dq bs _ p e _ op _ hpl_op hv) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"data").length + 3 : Nat) : Int)) +
        1 + op.length + 1 : Nat) : Int)) = uint.nat i + 1 + 7 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 7 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (wp_Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"client_id" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (wp_Member b dq bs kw go!"client_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 7 + V0.length + 1 + 12 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN cid ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_Log_1 wp_QuotedUint b dq bs _ p e _ cid _ hv h_cid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN cid).length + 2 : Nat) : Int)) = uint.nat i + 1 + 7 + V0.length + 1 + 12 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 7 + V0.length + 1 + 12 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (wp_Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"request_id" ++ 34#8 :: 58#8 :: (V2 ++ ([125#8] ++ rest))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (wp_Member b dq bs kw go!"request_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"request_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 7 + V0.length + 1 + 12 + V1.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"request_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN req ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_Log_2 wp_QuotedUint b dq bs _ p e _ req _ hv h_req) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"request_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN req).length + 2 : Nat) : Int)) = uint.nat i + 1 + 7 + V0.length + 1 + 12 + V1.length + 1 + 13 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 7 + V0.length + 1 + 12 + V1.length + 1 + 13 + V2.length]? = some 125#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (wp_Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 7 + V0.length + 1 + 12 + V1.length + 1 + 13 + V2.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 7 + V0.length + 1 + 12 + V1.length + 1 + 13 + V2.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
