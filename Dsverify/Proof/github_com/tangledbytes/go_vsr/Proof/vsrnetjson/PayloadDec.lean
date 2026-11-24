/-
The payload types' generated decoders (`events`' `json_model_gen.go`, jsongen's same-package
methods: `jdec_<T>`, `jdecMember_<T>`, and `jdec_p0_log_Logs` for a `Logs` member, which calls
`Logs.UnmarshalJSON`) on a payload's encoding (`VsrJson.payJV m`): they store `m`'s payload.
Over the specs of `jsoncodec`'s decoding helpers and `log.Logs.UnmarshalJSON` (the bundle
`vsrnet.DecSpecs`, linked in `examples/vsrnet/Link.lean`). Ported from dsverify-lab's
`examples/vr/proof/VsrProof/Proof/vsrnetjson/{Request,DecFlat,DecMore,DecLogs}.lean` (lab master
915f964; generated there by codecgen/gen.py); the `Logs` members are new (the lab's went through its
own `jdecUnmarshaler`), round 9 (notes/dsv-vr.md).
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.FrameDec
public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Proof.vsrnetjson.Vacuous
public import Net.Spec.models_lab.jsoncodec.String
public import Net.Spec.models_lab.jsoncodec.QuotedUint

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.iris.style.nameCheck false
set_option maxHeartbeats 2000000

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [vsrnet.Assumptions]

/-- What the payload decoders' proofs take: the specs of `jsoncodec`'s decoding helpers,
`log.Logs.UnmarshalJSON`'s, and the registered codec's facts (`registeredCodecOk`, `scanOk`: the
`Logs` members decode through `json.Unmarshal`'s codec route). All proved; `Link.lean` builds it. -/
structure vsrnet.DecSpecs : Prop where
  At : models_lab.jsoncodec.At.spec (GF := GF) (hG := hG)
  Empty : models_lab.jsoncodec.Empty.spec (GF := GF) (hG := hG)
  Member : models_lab.jsoncodec.Member.spec (GF := GF) (hG := hG)
  Next : models_lab.jsoncodec.Next.spec (GF := GF) (hG := hG)
  String : models_lab.jsoncodec.String.spec (GF := GF) (hG := hG)
  QuotedUint : models_lab.jsoncodec.QuotedUint.spec (GF := GF) (hG := hG)
  SkipSpace : models_lab.jsoncodec.SkipSpace.spec (GF := GF) (hG := hG)
  ValueEnd : models_lab.jsoncodec.ValueEnd.spec (GF := GF) (hG := hG)
  Valid : models_lab.jsoncodec.Valid.spec (GF := GF) (hG := hG)
  LogsUnmarshalJSON : pkg.log.Logs.UnmarshalJSON.spec (GF := GF) (hG := hG)
  codec : vsrnet.registeredCodecOk (GF := GF) (hG := hG)
  scan : ⊢ models_lab.jsoncodec.scanOk (GF := GF) vsrnet.scanF models_lab.jsoncodec.scanFn

/-- The registered codec's route at `codecPart vsrnet.jsonCodec` (persistent): what a `Logs`
member's `UnmarshalJSON` needs of `json.Unmarshal`. -/
abbrev vsrnet.logsRoute : IProp GF :=
  encoding.json.codecRoute (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))) vsrnet.scanF

/-- The route, from the codec registered (`codecSet`) and its proved facts. -/
theorem vsrnet.logsRoute_of (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) :
    encoding.json.codecSet (GF := GF) ⊢ vsrnet.logsRoute (GF := GF) := by
  unfold encoding.json.codecSet
  iintro #Hset
  have hc := H.codec
  unfold vsrnet.registeredCodecOk at hc
  ihave #⟨Hm, Hu⟩ := hc
  ihave #Hs := H.scan
  unfold vsrnet.logsRoute encoding.json.codecRoute
  iexists encoding.json.kitFn go!"jsonMarshal", encoding.json.kitFn go!"jsonUnmarshal"
  isplitl []
  · iexact Hset
  unfold encoding.json.codecOkWith
  isplitl []
  · iexact Hm
  isplitl []
  · iexact Hu
  iexact Hs

/-- Two slice values with the same pointer and length own the same non-empty elements (a
three-index slice `s[i:k:k]`'s capacity differs from `s[i:k]`'s). -/
theorem vsrnet.ownSlice_same_ptr_len {V : Type} [ZeroVal V] [TypedPointsto (GF := GF) V]
    (s1 s2 : GoSlice) (dq : DFrac) (vs : List V) :
    vs ≠ [] → s1.ptr = s2.ptr → s1.len = s2.len → sint.Z s2.len ≤ sint.Z s2.cap →
    ⊢ (s1 ↦*{dq} vs : IProp GF) -∗ s2 ↦*{dq} vs := by
  intro Hne Hptr Hlen Hcap
  obtain ⟨p1, l1, c1⟩ := s1
  obtain ⟨p2, l2, c2⟩ := s2
  simp only at Hptr Hlen Hcap
  subst Hptr Hlen
  rw [ownSlice_unseal]; unfold ownSliceDef
  iintro (%H | ⟨H, %_⟩)
  · exact absurd H.2 Hne
  · iright
    iframe H
    ipureintro; exact Hcap

/-- The decoded `Logs`' resources once decoded (`true`), nothing before. -/
def vsrnet.logsRes : Bool → GoSlice → List Entry → IProp GF
  | true, sl, es => iprop(pkg.log.ownLogs sl (DFrac.own 1) es ∗
      ownSliceCap pkg.log.Log sl (DFrac.own 1))
  | false, _, _ => iprop(True)

set_option goose.wp.extras true

/-- `jdec_p0_log_Logs(b, i, lp, e)` on a `[]Log`'s encoding at `i`: `lp.UnmarshalJSON` of the
value (`b[j:k:k]`) stores a fresh slice of the entries. -/
theorem vsrnet.wp_jdec_logs (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac)
    (bs : List w8) (i : w64) (lp e : Loc) (sl0 : GoSlice) (es : List Entry) (R : List w8)
    (hes : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.logsJV es) ++ R) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗ b ↦*{dq} bs ∗ lp ↦ sl0 : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_p0_log_Logs)) (Val #b)) (Val #i)) (Val #lp))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, lp ↦ sl ∗ pkg.log.ownLogs sl (DFrac.own 1) es ∗
          ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  generalize hV : VsrJson.ser (VsrJson.logsJV es) = V at hb ⊢
  have hV91 : ∃ T, V = 91#8 :: T := by
    rw [← hV]; simp [VsrJson.logsJV, VsrJson.ser]
  obtain ⟨T, hT⟩ := hV91
  have hc : bs[uint.nat i]? = some 91#8 := by
    have := congrArg (fun l => l[0]?) hb
    simp only [List.getElem?_drop, hT] at this
    simpa using this
  have hplain : ∀ e ∈ es, PlainStr e.op := fun e he => (hes e he).2.2
  have hsc : JsonScan.scanL (bs.drop (uint.nat i)) true = (0, V.length) := by
    rw [hb, ← hV]
    have := VsrJson.top_v (VsrJson.logsJV es) (VsrJson.logsJV_ok es hplain) R 0 false true
      (VsrJson.logsJV_maxd es) trivial
    simpa [JsonScan.scanL] using this
  have hVl : 0 < V.length := by rw [hT]; simp
  have hle : uint.nat i + V.length ≤ bs.length := by
    have := congrArg List.length hb
    simp only [List.length_drop, List.length_append] at this; omega
  wp_auto
  wp_apply (models_lab.jsoncodec.wp_SkipSpace_ns H.SkipSpace b dq bs i 91#8 hc (by decide))
    $$ Hs as Hs
  wp_apply (H.ValueEnd b dq bs i (by omega) (by rw [hsc])) $$ Hs as Hs
  rw [hsc]
  simp only
  ihave %Hwf := ownSlice_wf $$ Hs
  have hb2 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (W64 ↑(uint.nat i + V.length)) ∧
      sint.Z (W64 ↑(uint.nat i + V.length)) ≤ sint.Z b.len := by word
  have hb1 : 0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z (W64 ↑(uint.nat i + V.length)) ∧
      sint.Z (W64 ↑(uint.nat i + V.length)) ≤ sint.Z (W64 ↑(uint.nat i + V.length)) ∧
      sint.Z (W64 ↑(uint.nat i + V.length)) ≤ sint.Z b.cap := by word
  rw [if_pos hb1]
  icases (ownSlice_slice i _ b dq bs hb2).1 $$ Hs with ⟨H1, H2, H3⟩
  have hsub : subslice (sint.nat i) (sint.nat (W64 ↑(uint.nat i + V.length))) bs = V := by
    rw [show sint.nat i = uint.nat i by word,
      show sint.nat (W64 ↑(uint.nat i + V.length)) = uint.nat i + V.length by word]
    simp only [subslice]; rw [List.drop_take, hb]; simp
  rw [hsub]
  have hVne : V ≠ [] := by rw [hT]; simp
  ihave H2' := vsrnet.ownSlice_same_ptr_len (slice.slice b w8 i (W64 ↑(uint.nat i + V.length)))
    (slice.fullSlice b w8 i (W64 ↑(uint.nat i + V.length)) (W64 ↑(uint.nat i + V.length)))
    dq V hVne (by simp only [slice.slice, slice.fullSlice])
    (by simp only [slice.slice, slice.fullSlice]) (by simp only [slice.fullSlice]; word) $$ H2
  have hval : models_lab.jsoncodec.jsonValid vsrnet.scanF (pkg.log.encLogs es) :=
    vsrnet.encLogs_valid es hplain (by
      rw [show pkg.log.encLogs es = V by rw [← hV]; rfl]; omega)
  have hdec : ∀ q : Loc, (q ↦ (slice.nil : GoSlice) : IProp GF) ⊢
      (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))).dec (pkg.log.encLogs es)
        (interface.mkOk (go.GoType.PointerType (go.GoType.SliceType pkg.log.Log.ty)) #q)
        (fun ok => iprop(⌜ok = true⌝ ∗ ∃ sl : GoSlice, q ↦ sl ∗
          pkg.log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap pkg.log.Log sl (DFrac.own 1))) := by
    intro q
    rw [show ∀ (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF),
        (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF))).dec bs ptr Ψ =
        iprop(⌜encoding.json.unmarshalsByCodec ptr⌝ ∗ (vsrnet.jsonCodec (GF := GF)).dec bs ptr Ψ)
      from fun _ _ _ => rfl]
    iintro Hq
    isplitr
    · ipureintro; exact pkg.log.logs_unmarshalsByCodec q
    iapply (vsrnet.dec_logs es q _ hes rfl)
    iexact Hq
  rw [show V = pkg.log.encLogs es by rw [← hV]; rfl]
  wp_auto
  wp_apply (H.LogsUnmarshalJSON (encoding.json.codecPart (vsrnet.jsonCodec (GF := GF)))
    vsrnet.scanF lp sl0 _ dq es hval hdec) $$ [Hp H2'] as ⟨%sl, Hp, Hown, Hcap, H2'⟩
  · iframe
    iexact Hset
  rw [show pkg.log.encLogs es = V by rw [← hV]; rfl]
  ihave H2 := vsrnet.ownSlice_same_ptr_len
    (slice.fullSlice b w8 i (W64 ↑(uint.nat i + V.length)) (W64 ↑(uint.nat i + V.length)))
    (slice.slice b w8 i (W64 ↑(uint.nat i + V.length)))
    dq V hVne (by simp only [slice.slice, slice.fullSlice])
    (by simp only [slice.slice, slice.fullSlice]) (by simp only [slice.slice]; word) $$ H2'
  ihave Hs := (ownSlice_slice i _ b dq bs hb2).2 $$ [H1 H2 H3]
  · rw [hsub]; iframe
  iapply HΦ
  iframe


/-- `jdecMember_events_Request(b, i, "id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Request_id (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Request) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Request)) (Val #b)) (Val #i))
        (Val #(go!"id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Request(b, i, "client_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Request_cid (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Request) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Request)) (Val #b)) (Val #i))
        (Val #(go!"client_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ClientID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Request(b, i, "op", p, e)` on a plain string at `i`. -/
theorem vsrnet.wp_jdecMember_Request_op (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Request) (str rest : List w8) (hs : ∀ c ∈ str, JsonScan.okB c)
    (hb : bs.drop (uint.nat i) = 34#8 :: (str ++ 34#8 :: rest)) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Request)) (Val #b)) (Val #i))
        (Val #(go!"op"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + 1 + str.length + 1 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with Op' := str } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.String b dq bs i str rest hs hb) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_Request(b, i, p, e)` on a request's encoding at `i`. -/
theorem vsrnet.wp_jdec_Request (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.Request) (id cid : Nat) (op rest : List w8) (hid : id < 2 ^ 64)
    (hcid : cid < 2 ^ 64) (hop : PlainStr op)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.reqJV id cid op) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_Request)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.reqJV id cid op)).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.events.Request.mk (W64 id) (W64 cid) op }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.reqJV id cid op) =
      [123#8] ++ ((34#8 :: (go!"id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN id ++ [34#8])) ++ ([44#8] ++
      ((34#8 :: (go!"client_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN cid ++ [34#8])) ++ ([44#8] ++
      ((34#8 :: (go!"op" ++ [34#8, 58#8])) ++ ((34#8 :: (op ++ [34#8])) ++ [125#8])))))))) := by
    simp [VsrJson.ser, VsrJson.reqJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  have hplain := VsrJson.plain_okB op hop
  generalize hM0 : (34#8 :: (go!"id" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN id ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"client_id" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN cid ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"op" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (op ++ [34#8])) = V2 at hb
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
  have lM0 : M0.length = 5 := by rw [← hM0]; rfl
  have lM1 : M1.length = 12 := by rw [← hM1]; rfl
  have lM2 : M2.length = 5 := by rw [← hM2]; rfl
  have lV0 : V0.length = (JsonScan.decN id).length + 2 := by rw [← hV0]; simp
  have lV1 : V1.length = (JsonScan.decN cid).length + 2 := by rw [← hV1]; simp
  have lV2 : V2.length = op.length + 2 := by rw [← hV2]; simp
  have lser : (VsrJson.ser (VsrJson.reqJV id cid op)).length = 1 + 5 + V0.length + 1 + 12 +
      V1.length + 1 + 5 + V2.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  have hlen := congrArg List.length hb9
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  have hidx : ∀ k (A : List w8) (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k A c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ [] _ _ (by rw [hb]; rfl)
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ [] _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.Request),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨
        (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 5 + V0.length + 1 ∧ rr = pkg.events.Request.mk (W64 id) r.ClientID' r.Op') ∨
        (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 ∧
          rr = pkg.events.Request.mk (W64 id) (W64 cid) r.Op')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · -- the member "id"
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"id" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++
        (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 5 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN id ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++
          (V2 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_Request_id H b dq bs _ p e _ id _ hv hid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"id").length + 3 : Nat) : Int)) +
        (JsonScan.decN id).length + 2 : Nat) : Int)) = uint.nat i + 1 + 5 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 5 + V0.length]? = some 44#8 := hidx _ [] _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · -- the member "client_id"
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"client_id" ++ 34#8 :: 58#8 :: (V1 ++
        ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"client_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 5 + V0.length + 1 + 12 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN cid ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_Request_cid H b dq bs _ p e _ cid _ hv hcid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN cid).length + 2 : Nat) : Int)) =
        uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length]? = some 44#8 :=
      hidx _ [] _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, by word, rfl⟩
  · -- the member "op"
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"op" ++ 34#8 :: 58#8 :: (V2 ++
        ([125#8] ++ rest))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"op" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"op").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 5 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"op").length + 3 : Nat) : Int))) =
        34#8 :: (op ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_Request_op H b dq bs _ p e _ op _ hplain hv) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"op").length + 3 : Nat) : Int)) +
        1 + op.length + 1 : Nat) : Int)) =
        uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 5 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 5 + V2.length]? =
        some 125#8 := hidx _ [] _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 5 + V2.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 5 + V2.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe



/-- `jdecMember_events_Reply(b, i, "id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Reply_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Reply) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Reply)) (Val #b)) (Val #i))
        (Val #(go!"id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Reply(b, i, "client_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Reply_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Reply) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Reply)) (Val #b)) (Val #i))
        (Val #(go!"client_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ClientID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Reply(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Reply_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Reply) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Reply)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Reply(b, i, "result", p, e)` on a plain string at `i`. -/
theorem vsrnet.wp_jdecMember_Reply_3 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Reply) (str rest : List w8) (hs : ∀ c ∈ str, JsonScan.okB c)
    (hb : bs.drop (uint.nat i) = 34#8 :: (str ++ 34#8 :: rest)) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Reply)) (Val #b)) (Val #i))
        (Val #(go!"result"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + 1 + str.length + 1 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with Result' := str } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.String b dq bs i str rest hs hb) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_Reply(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_Reply (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.Reply) (id : Nat) (cid : Nat) (v : Nat) (res : List w8) (rest : List w8)
    (h_id : id < 2 ^ 64) (h_cid : cid < 2 ^ 64) (h_v : v < 2 ^ 64) (h_res : PlainStr res)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.reply id cid v res)) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_Reply)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.reply id cid v res))).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.events.Reply.mk (W64 (id : Int)) (W64 (cid : Int)) (W64 (v : Int)) res }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.reply id cid v res)) =
      [123#8] ++ ((34#8 :: (go!"id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN id ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"client_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN cid ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"result" ++ [34#8, 58#8])) ++ ((34#8 :: (res ++ [34#8])) ++ [125#8]))))))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  have hpl_res := VsrJson.plain_okB res h_res
  generalize hM0 : (34#8 :: (go!"id" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN id ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"client_id" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN cid ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V2 at hb
  generalize hM3 : (34#8 :: (go!"result" ++ [34#8, 58#8])) = M3 at hb
  generalize hV3 : (34#8 :: (res ++ [34#8])) = V3 at hb
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
  have hb10 := vsrnet.drop_app bs _ _ _ hb9
  have hb11 := vsrnet.drop_app bs _ _ _ hb10
  have hb12 := vsrnet.drop_app bs _ _ _ hb11
  have lM0 : M0.length = 5 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN id).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 12 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN cid).length + 2 := by rw [← hV1]; simp
  have lM2 : M2.length = 11 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN v).length + 2 := by rw [← hV2]; simp
  have lM3 : M3.length = 9 := by rw [← hM3]; rfl
  have lV3 : V3.length = res.length + 2 := by rw [← hV3]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.reply id cid v res))).length = 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length + 1 + 9 + V3.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2, ← hM3, ← hV3] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2, lM3] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb12
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.Reply),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 5 + V0.length + 1 ∧ rr = pkg.events.Reply.mk (W64 (id : Int)) r.ClientID' r.ViewNum' r.Result') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 ∧ rr = pkg.events.Reply.mk (W64 (id : Int)) (W64 (cid : Int)) r.ViewNum' r.Result') ∨ (n = 3 ∧ uint.nat kw = uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length + 1 ∧ rr = pkg.events.Reply.mk (W64 (id : Int)) (W64 (cid : Int)) (W64 (v : Int)) r.Result')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"id" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([125#8] ++ rest)))))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 5 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN id ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([125#8] ++ rest))))))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_Reply_0 H b dq bs _ p e _ id _ hv h_id) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"id").length + 3 : Nat) : Int)) +
        (JsonScan.decN id).length + 2 : Nat) : Int)) = uint.nat i + 1 + 5 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 5 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"client_id" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"client_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 5 + V0.length + 1 + 12 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN cid ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_Reply_1 H b dq bs _ p e _ cid _ hv h_cid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"client_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN cid).length + 2 : Nat) : Int)) = uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _
    iframe
    ipureintro; right; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN v ++ 34#8 :: ([44#8] ++ (M3 ++ (V3 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_Reply_2 H b dq bs _ p e _ v _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN v).length + 2 : Nat) : Int)) = uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length]? = some 44#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 3, _, _
    iframe
    ipureintro; right; right; right; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"result" ++ 34#8 :: 58#8 :: (V3 ++ ([125#8] ++ rest))) := by
      rw [hk, hb10, ← hM3]; simp
    wp_apply (H.Member b dq bs kw go!"result" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"result").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length + 1 + 9 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"result").length + 3 : Nat) : Int))) =
        34#8 :: (res ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb11, ← hV3]; simp
    wp_apply (vsrnet.wp_jdecMember_Reply_3 H b dq bs _ p e _ res _ hpl_res hv) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"result").length + 3 : Nat) : Int)) +
        1 + res.length + 1 : Nat) : Int)) = uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length + 1 + 9 + V3.length := by
      rw [hvz, lV3]; word
    have hc : bs[uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length + 1 + 9 + V3.length]? = some 125#8 := hidx _ _ _ (by rw [hb12]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length + 1 + 9 + V3.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 5 + V0.length + 1 + 12 + V1.length + 1 + 11 + V2.length + 1 + 9 + V3.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe

/-- `jdecMember_events_PrepareOK(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_PrepareOK_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.PrepareOK) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_PrepareOK)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_PrepareOK(b, i, "op_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_PrepareOK_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.PrepareOK) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_PrepareOK)) (Val #b)) (Val #i))
        (Val #(go!"op_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with OpNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_PrepareOK(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_PrepareOK_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.PrepareOK) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_PrepareOK)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_PrepareOK(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_PrepareOK (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.PrepareOK) (v : Nat) (k : Nat) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_k : k < 2 ^ 64) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.prepareOK v k rid)) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_PrepareOK)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.prepareOK v k rid))).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.events.PrepareOK.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (rid : Int)) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.prepareOK v k rid)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"op_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN k ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8])))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"op_num" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN k ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V2 at hb
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
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN v).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 9 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN k).length + 2 := by rw [← hV1]; simp
  have lM2 : M2.length = 13 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN rid).length + 2 := by rw [← hV2]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.prepareOK v k rid))).length = 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb9
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.PrepareOK),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.PrepareOK.mk (W64 (v : Int)) r.OpNum' r.ReplicaID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 ∧ rr = pkg.events.PrepareOK.mk (W64 (v : Int)) (W64 (k : Int)) r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN v ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_PrepareOK_0 H b dq bs _ p e _ v _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN v).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"op_num" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"op_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN k ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_PrepareOK_1 H b dq bs _ p e _ k _ hv h_k) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN k).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V2 ++ ([125#8] ++ rest))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN rid ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_PrepareOK_2 H b dq bs _ p e _ rid _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN rid).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length]? = some 125#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe

/-- `jdecMember_events_Commit(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Commit_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Commit) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Commit)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Commit(b, i, "commit_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Commit_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Commit) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Commit)) (Val #b)) (Val #i))
        (Val #(go!"commit_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with CommitNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Commit(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Commit_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Commit) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Commit)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_Commit(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_Commit (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.Commit) (v : Nat) (c : Nat) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_c : c < 2 ^ 64) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.commit v c rid)) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_Commit)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.commit v c rid))).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.events.Commit.mk (W64 (v : Int)) (W64 (c : Int)) (W64 (rid : Int)) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.commit v c rid)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"commit_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN c ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8])))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"commit_num" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN c ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V2 at hb
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
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN v).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 13 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN c).length + 2 := by rw [← hV1]; simp
  have lM2 : M2.length = 13 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN rid).length + 2 := by rw [← hV2]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.commit v c rid))).length = 1 + 11 + V0.length + 1 + 13 + V1.length + 1 + 13 + V2.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb9
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.Commit),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.Commit.mk (W64 (v : Int)) r.CommitNum' r.ReplicaID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length + 1 ∧ rr = pkg.events.Commit.mk (W64 (v : Int)) (W64 (c : Int)) r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN v ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_Commit_0 H b dq bs _ p e _ v _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN v).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"commit_num" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"commit_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN c ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_Commit_1 H b dq bs _ p e _ c _ hv h_c) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN c).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V2 ++ ([125#8] ++ rest))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN rid ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_Commit_2 H b dq bs _ p e _ rid _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN rid).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length + 1 + 13 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length + 1 + 13 + V2.length]? = some 125#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length + 1 + 13 + V2.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 13 + V1.length + 1 + 13 + V2.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe

/-- `jdecMember_events_StartViewChange(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_StartViewChange_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.StartViewChange) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_StartViewChange)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_StartViewChange(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_StartViewChange_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.StartViewChange) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_StartViewChange)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_StartViewChange(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_StartViewChange (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.StartViewChange) (v : Nat) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.startViewChange v rid)) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_StartViewChange)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.startViewChange v rid))).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.events.StartViewChange.mk (W64 (v : Int)) (W64 (rid : Int)) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.startViewChange v rid)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8]))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V1 at hb
  simp only [List.append_assoc] at hb
  have hb1 := vsrnet.drop_app bs _ _ _ hb
  have hb2 := vsrnet.drop_app bs _ _ _ hb1
  have hb3 := vsrnet.drop_app bs _ _ _ hb2
  have hb4 := vsrnet.drop_app bs _ _ _ hb3
  have hb5 := vsrnet.drop_app bs _ _ _ hb4
  have hb6 := vsrnet.drop_app bs _ _ _ hb5
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN v).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 13 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN rid).length + 2 := by rw [← hV1]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.startViewChange v rid))).length = 1 + 11 + V0.length + 1 + 13 + V1.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1] at hb1 hb2 hb3 hb4 hb5 hb6
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb6
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.StartViewChange),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.StartViewChange.mk (W64 (v : Int)) r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN v ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_StartViewChange_0 H b dq bs _ p e _ v _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN v).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V1 ++ ([125#8] ++ rest))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN rid ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_StartViewChange_1 H b dq bs _ p e _ rid _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN rid).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length]? = some 125#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 13 + V1.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 13 + V1.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe

/-- `jdecMember_events_GetState(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_GetState_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.GetState) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_GetState)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_GetState(b, i, "op_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_GetState_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.GetState) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_GetState)) (Val #b)) (Val #i))
        (Val #(go!"op_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with OpNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_GetState(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_GetState_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.GetState) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_GetState)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_GetState(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_GetState (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.GetState) (v : Nat) (k : Nat) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_k : k < 2 ^ 64) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.getState v k rid)) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_GetState)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.getState v k rid))).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.events.GetState.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (rid : Int)) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.getState v k rid)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"op_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN k ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8])))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"op_num" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN k ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V2 at hb
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
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN v).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 9 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN k).length + 2 := by rw [← hV1]; simp
  have lM2 : M2.length = 13 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN rid).length + 2 := by rw [← hV2]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.getState v k rid))).length = 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb9
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.GetState),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.GetState.mk (W64 (v : Int)) r.OpNum' r.ReplicaID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 ∧ rr = pkg.events.GetState.mk (W64 (v : Int)) (W64 (k : Int)) r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN v ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_GetState_0 H b dq bs _ p e _ v _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN v).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"op_num" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"op_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN k ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_GetState_1 H b dq bs _ p e _ k _ hv h_k) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN k).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _
    iframe
    ipureintro; right; right; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V2 ++ ([125#8] ++ rest))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN rid ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_GetState_2 H b dq bs _ p e _ rid _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN rid).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length]? = some 125#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe



/-- `jdec_events_Heartbeat(b, i, p, e)` on `{}` at `i`. -/
theorem vsrnet.wp_jdec_Heartbeat (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.Heartbeat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV .heartbeat) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_Heartbeat)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV .heartbeat)).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ r }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV .heartbeat) = [123#8, 125#8] := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.serMs]
  rw [hser] at hb ⊢
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hb1 := vsrnet.drop_app bs [123#8] _ _ hb
  simp only [List.length_cons, List.length_nil] at hb1
  have hc1 : bs[uint.nat i + 1]? = some 125#8 := hidx _ _ _ (by rw [hb1])
  have hlen := congrArg List.length hb
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  wp_apply (H.Empty b dq bs i 125#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  try rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]
  rw [show (uint.nat i + [123#8, 125#8].length) = uint.nat i + 1 + 1 by simp]
  iapply HΦ; iframe

/-- `jdecMember_events_Prepare(b, i, "request", p, e)` on a request's encoding at `i`. -/
theorem vsrnet.wp_jdecMember_Prepare_3 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Prepare) (en : Entry) (rest : List w8)
    (h1 : en.req < 2 ^ 64) (h2 : en.cid < 2 ^ 64) (h3 : PlainStr en.op)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.reqJV en.req en.cid en.op) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Prepare)) (Val #b)) (Val #i))
        (Val #(go!"request"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.reqJV en.req en.cid en.op)).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with Request' := pkg.events.Request.mk (W64 en.req) (W64 en.cid) en.op } }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_auto
  iStructNamed Hp
  wp_apply (vsrnet.wp_jdec_Request H b dq bs i _ e _ en.req en.cid en.op rest h1 h2 h3 hb
   ) $$ [Hs Request] as ⟨Hs, Request⟩
  · iframe
  ihave Hp : (p ↦ { r with Request' := pkg.events.Request.mk (W64 en.req) (W64 en.cid) en.op } :
      IProp GF) $$ [ViewNum OpNum CommitNum Request ReplicaID]
  · iapply typedPointsto_combine _ _ _ Hpnn
    simp only [typedPointstoDef]
    iframe
  iapply HΦ; iframe


/-- `jdecMember_events_Prepare(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Prepare_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Prepare) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Prepare)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Prepare(b, i, "op_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Prepare_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Prepare) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Prepare)) (Val #b)) (Val #i))
        (Val #(go!"op_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with OpNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Prepare(b, i, "commit_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Prepare_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Prepare) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Prepare)) (Val #b)) (Val #i))
        (Val #(go!"commit_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with CommitNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_Prepare(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_Prepare_4 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.Prepare) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_Prepare)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_Prepare(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_Prepare (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.Prepare) (v : Nat) (k : Nat) (c : Nat) (en : Entry) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_k : k < 2 ^ 64) (h_c : c < 2 ^ 64) (h_en1 : en.req < 2 ^ 64) (h_en2 : en.cid < 2 ^ 64) (h_en3 : PlainStr en.op) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.prepare v k c en rid)) ++ rest) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_Prepare)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.prepare v k c en rid))).length : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ pkg.events.Prepare.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (c : Int)) (pkg.events.Request.mk (W64 en.req) (W64 en.cid) en.op) (W64 (rid : Int)) }} := by
  wp_start as ⟨Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.prepare v k c en rid)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"op_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN k ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"commit_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN c ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"request" ++ [34#8, 58#8])) ++ (VsrJson.ser (VsrJson.reqJV en.req en.cid en.op) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8])))))))))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"op_num" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN k ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"commit_num" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN c ++ [34#8])) = V2 at hb
  generalize hM3 : (34#8 :: (go!"request" ++ [34#8, 58#8])) = M3 at hb
  generalize hV3 : VsrJson.ser (VsrJson.reqJV en.req en.cid en.op) = V3 at hb
  generalize hM4 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M4 at hb
  generalize hV4 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V4 at hb
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
  have hb10 := vsrnet.drop_app bs _ _ _ hb9
  have hb11 := vsrnet.drop_app bs _ _ _ hb10
  have hb12 := vsrnet.drop_app bs _ _ _ hb11
  have hb13 := vsrnet.drop_app bs _ _ _ hb12
  have hb14 := vsrnet.drop_app bs _ _ _ hb13
  have hb15 := vsrnet.drop_app bs _ _ _ hb14
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN v).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 9 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN k).length + 2 := by rw [← hV1]; simp
  have lM2 : M2.length = 13 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN c).length + 2 := by rw [← hV2]; simp
  have lM3 : M3.length = 10 := by rw [← hM3]; rfl
  have lV3 : V3.length = (VsrJson.ser (VsrJson.reqJV en.req en.cid en.op)).length := by rw [← hV3]
  have lM4 : M4.length = 13 := by rw [← hM4]; rfl
  have lV4 : V4.length = (JsonScan.decN rid).length + 2 := by rw [← hV4]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.prepare v k c en rid))).length = 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length + 1 + 13 + V4.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2, ← hM3, ← hV3, ← hM4, ← hV4] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2, lM3, lM4] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb15
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.Prepare),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.Prepare.mk (W64 (v : Int)) r.OpNum' r.CommitNum' r.Request' r.ReplicaID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 ∧ rr = pkg.events.Prepare.mk (W64 (v : Int)) (W64 (k : Int)) r.CommitNum' r.Request' r.ReplicaID') ∨ (n = 3 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 ∧ rr = pkg.events.Prepare.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (c : Int)) r.Request' r.ReplicaID') ∨ (n = 4 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length + 1 ∧ rr = pkg.events.Prepare.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (c : Int)) (pkg.events.Request.mk (W64 en.req) (W64 en.cid) en.op) r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r; iframe; ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN v ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_Prepare_0 H b dq bs _ p e _ v _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN v).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _
    iframe
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"op_num" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"op_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN k ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_Prepare_1 H b dq bs _ p e _ k _ hv h_k) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN k).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _
    iframe
    ipureintro; right; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"commit_num" ++ 34#8 :: 58#8 :: (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"commit_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN c ++ 34#8 :: ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_Prepare_2 H b dq bs _ p e _ c _ hv h_c) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN c).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length]? = some 44#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 3, _, _
    iframe
    ipureintro; right; right; right; left; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"request" ++ 34#8 :: 58#8 :: (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb10, ← hM3]; simp
    wp_apply (H.Member b dq bs kw go!"request" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"request").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"request").length + 3 : Nat) : Int))) =
        VsrJson.ser (VsrJson.reqJV en.req en.cid en.op) ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))) := by
      rw [hvz, hb11, ← hV3]
    wp_apply (vsrnet.wp_jdecMember_Prepare_3 H b dq bs _ p e _ en _ h_en1 h_en2 h_en3 hv) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"request").length + 3 : Nat) : Int)) +
        (VsrJson.ser (VsrJson.reqJV en.req en.cid en.op)).length : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length := by
      rw [hvz, lV3]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length]? = some 44#8 := hidx _ _ _ (by rw [hb12]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 4, _, _
    iframe
    ipureintro; right; right; right; right; exact ⟨rfl, by word, rfl⟩
  · have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V4 ++ ([125#8] ++ rest))) := by
      rw [hk, hb13, ← hM4]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN rid ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb14, ← hV4]; simp
    wp_apply (vsrnet.wp_jdecMember_Prepare_4 H b dq bs _ p e _ rid _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN rid).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length + 1 + 13 + V4.length := by
      rw [hvz, lV4]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length + 1 + 13 + V4.length]? = some 125#8 := hidx _ _ _ (by rw [hb15]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length + 1 + 13 + V4.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 10 + V3.length + 1 + 13 + V4.length + 1) : Nat) : Int)
      by congr 2; omega]
    iapply HΦ; iframe




/-- `jdecMember_events_DoViewChange(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_DoViewChange_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.DoViewChange) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_DoViewChange)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_DoViewChange(b, i, "logs", p, e)` on a `[]Log`'s encoding at `i`. -/
theorem vsrnet.wp_jdecMember_DoViewChange_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.DoViewChange) (es : List Entry) (R : List w8)
    (hes : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.logsJV es) ++ R) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_DoViewChange)) (Val #b)) (Val #i))
        (Val #(go!"logs"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, p ↦ { r with Logs' := sl } ∗
          pkg.log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, Hs, Hp⟩
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_auto
  iStructNamed Hp
  wp_apply (vsrnet.wp_jdec_logs H b dq bs i _ e _ es R hes hb) $$ [Hs Logs]
    as ⟨Hs, %sl, Logs, Hown, Hcap⟩
  · isplitr; · iexact Hset
    iframe
  ihave Hp : (p ↦ { r with Logs' := sl } : IProp GF) $$ [ViewNum Logs LastStableViewNum OpNum CommitNum ReplicaID]
  · iapply typedPointsto_combine _ _ _ Hpnn
    simp only [typedPointstoDef]
    iframe
  iapply HΦ; iframe

/-- `jdecMember_events_DoViewChange(b, i, "last_stable_view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_DoViewChange_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.DoViewChange) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_DoViewChange)) (Val #b)) (Val #i))
        (Val #(go!"last_stable_view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with LastStableViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_DoViewChange(b, i, "op_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_DoViewChange_3 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.DoViewChange) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_DoViewChange)) (Val #b)) (Val #i))
        (Val #(go!"op_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with OpNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_DoViewChange(b, i, "commit_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_DoViewChange_4 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.DoViewChange) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_DoViewChange)) (Val #b)) (Val #i))
        (Val #(go!"commit_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with CommitNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_DoViewChange(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_DoViewChange_5 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.DoViewChange) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_DoViewChange)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_DoViewChange(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_DoViewChange (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.DoViewChange) (v : Nat) (es : List Entry) (lnv : Nat) (c : Nat) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_es : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op) (h_lnv : lnv < 2 ^ 64) (h_es_length : es.length < 2 ^ 64) (h_c : c < 2 ^ 64) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.doViewChange ⟨v, es, lnv, c, rid⟩)) ++ rest) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_DoViewChange)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.doViewChange ⟨v, es, lnv, c, rid⟩))).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, p ↦ pkg.events.DoViewChange.mk (W64 (v : Int)) sl (W64 (lnv : Int)) (W64 (es.length : Int)) (W64 (c : Int)) (W64 (rid : Int)) ∗
          pkg.log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.doViewChange ⟨v, es, lnv, c, rid⟩)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"logs" ++ [34#8, 58#8])) ++ (VsrJson.ser (VsrJson.logsJV es) ++ ([44#8] ++ ((34#8 :: (go!"last_stable_view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN lnv ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"op_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN es.length ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"commit_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN c ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8]))))))))))))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"logs" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : VsrJson.ser (VsrJson.logsJV es) = V1 at hb
  generalize hM2 : (34#8 :: (go!"last_stable_view_num" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN lnv ++ [34#8])) = V2 at hb
  generalize hM3 : (34#8 :: (go!"op_num" ++ [34#8, 58#8])) = M3 at hb
  generalize hV3 : (34#8 :: (JsonScan.decN es.length ++ [34#8])) = V3 at hb
  generalize hM4 : (34#8 :: (go!"commit_num" ++ [34#8, 58#8])) = M4 at hb
  generalize hV4 : (34#8 :: (JsonScan.decN c ++ [34#8])) = V4 at hb
  generalize hM5 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M5 at hb
  generalize hV5 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V5 at hb
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
  have hb10 := vsrnet.drop_app bs _ _ _ hb9
  have hb11 := vsrnet.drop_app bs _ _ _ hb10
  have hb12 := vsrnet.drop_app bs _ _ _ hb11
  have hb13 := vsrnet.drop_app bs _ _ _ hb12
  have hb14 := vsrnet.drop_app bs _ _ _ hb13
  have hb15 := vsrnet.drop_app bs _ _ _ hb14
  have hb16 := vsrnet.drop_app bs _ _ _ hb15
  have hb17 := vsrnet.drop_app bs _ _ _ hb16
  have hb18 := vsrnet.drop_app bs _ _ _ hb17
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN (v)).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 7 := by rw [← hM1]; rfl
  have lV1 : V1.length = (VsrJson.ser (VsrJson.logsJV es)).length := by rw [← hV1]
  have lM2 : M2.length = 23 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN (lnv)).length + 2 := by rw [← hV2]; simp
  have lM3 : M3.length = 9 := by rw [← hM3]; rfl
  have lV3 : V3.length = (JsonScan.decN (es.length)).length + 2 := by rw [← hV3]; simp
  have lM4 : M4.length = 13 := by rw [← hM4]; rfl
  have lV4 : V4.length = (JsonScan.decN (c)).length + 2 := by rw [← hV4]; simp
  have lM5 : M5.length = 13 := by rw [← hM5]; rfl
  have lV5 : V5.length = (JsonScan.decN (rid)).length + 2 := by rw [← hV5]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.doViewChange ⟨v, es, lnv, c, rid⟩))).length = 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 + 13 + V5.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2, ← hM3, ← hV3, ← hM4, ← hV4, ← hM5, ← hV5] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2, lM3, lM4, lM5] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15 hb16 hb17 hb18
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb18
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.DoViewChange) (sl : GoSlice),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗ "HL" ∷ vsrnet.logsRes (decide (1 < n)) sl es ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.DoViewChange.mk (W64 (v : Int)) r.Logs' r.LastStableViewNum' r.OpNum' r.CommitNum' r.ReplicaID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 ∧ rr = pkg.events.DoViewChange.mk (W64 (v : Int)) sl r.LastStableViewNum' r.OpNum' r.CommitNum' r.ReplicaID') ∨ (n = 3 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 ∧ rr = pkg.events.DoViewChange.mk (W64 (v : Int)) sl (W64 (lnv : Int)) r.OpNum' r.CommitNum' r.ReplicaID') ∨ (n = 4 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 ∧ rr = pkg.events.DoViewChange.mk (W64 (v : Int)) sl (W64 (lnv : Int)) (W64 (es.length : Int)) r.CommitNum' r.ReplicaID') ∨ (n = 5 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 ∧ rr = pkg.events.DoViewChange.mk (W64 (v : Int)) sl (W64 (lnv : Int)) (W64 (es.length : Int)) (W64 (c : Int)) r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r, slice.nil
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl []
    · rw [show decide (1 < 0) = false from rfl]; simp only [vsrnet.logsRes]; try itrivial
    ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · simp only [show decide (1 < 0) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest)))))))))))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (v) ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest))))))))))))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_DoViewChange_0 H b dq bs _ p e _ (v) _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (v)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (1 < 1) = false from rfl]; iexact HL
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 1) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"logs" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest))))))))))))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"logs" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int))) =
        VsrJson.ser (VsrJson.logsJV es) ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest))))))))))))) := by
      rw [hvz, hb5, ← hV1]
    wp_apply (vsrnet.wp_jdecMember_DoViewChange_1 H b dq bs _ p e _ es _ h_es hv) $$ [Hs Hp]
      as ⟨Hs, %sl', Hp, Hown, Hcap⟩
    · isplitr; · iexact Hset
      iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int)) +
        (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _, sl'
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [Hown Hcap]
    · rw [show decide (1 < 2) = true from rfl]; simp only [vsrnet.logsRes]; isplitl [Hown]; · iexact Hown
      iexact Hcap
    ipureintro; right; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 2) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"last_stable_view_num" ++ 34#8 :: 58#8 :: (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest)))))))))))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"last_stable_view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"last_stable_view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"last_stable_view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (lnv) ++ 34#8 :: ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest))))))))))) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_DoViewChange_2 H b dq bs _ p e _ (lnv) _ hv h_lnv) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"last_stable_view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (lnv)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length]? = some 44#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 3, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (1 < 3) = true from rfl]; iexact HL
    ipureintro; right; right; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 3) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"op_num" ++ 34#8 :: 58#8 :: (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb10, ← hM3]; simp
    wp_apply (H.Member b dq bs kw go!"op_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (es.length) ++ 34#8 :: ([44#8] ++ (M4 ++ (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb11, ← hV3]; simp
    wp_apply (vsrnet.wp_jdecMember_DoViewChange_3 H b dq bs _ p e _ (es.length) _ hv h_es_length) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (es.length)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length := by
      rw [hvz, lV3]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length]? = some 44#8 := hidx _ _ _ (by rw [hb12]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 4, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (1 < 4) = true from rfl]; iexact HL
    ipureintro; right; right; right; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 4) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"commit_num" ++ 34#8 :: 58#8 :: (V4 ++ ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb13, ← hM4]; simp
    wp_apply (H.Member b dq bs kw go!"commit_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (c) ++ 34#8 :: ([44#8] ++ (M5 ++ (V5 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb14, ← hV4]; simp
    wp_apply (vsrnet.wp_jdecMember_DoViewChange_4 H b dq bs _ p e _ (c) _ hv h_c) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (c)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length := by
      rw [hvz, lV4]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length]? = some 44#8 := hidx _ _ _ (by rw [hb15]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 5, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (1 < 5) = true from rfl]; iexact HL
    ipureintro; right; right; right; right; right; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 5) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V5 ++ ([125#8] ++ rest))) := by
      rw [hk, hb16, ← hM5]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (rid) ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb17, ← hV5]; simp
    wp_apply (vsrnet.wp_jdecMember_DoViewChange_5 H b dq bs _ p e _ (rid) _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN (rid)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 + 13 + V5.length := by
      rw [hvz, lV5]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 + 13 + V5.length]? = some 125#8 := hidx _ _ _ (by rw [hb18]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 + 13 + V5.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 23 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 + 13 + V5.length + 1) : Nat) : Int)
      by congr 2; omega]
    simp only [vsrnet.logsRes]
    iNamed HL
    iapply HΦ; iframe

/-- `jdecMember_events_StartView(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_StartView_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.StartView) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_StartView)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_StartView(b, i, "op_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_StartView_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.StartView) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_StartView)) (Val #b)) (Val #i))
        (Val #(go!"op_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with OpNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_StartView(b, i, "commit_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_StartView_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.StartView) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_StartView)) (Val #b)) (Val #i))
        (Val #(go!"commit_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with CommitNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_StartView(b, i, "logs", p, e)` on a `[]Log`'s encoding at `i`. -/
theorem vsrnet.wp_jdecMember_StartView_3 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.StartView) (es : List Entry) (R : List w8)
    (hes : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.logsJV es) ++ R) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_StartView)) (Val #b)) (Val #i))
        (Val #(go!"logs"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, p ↦ { r with Logs' := sl } ∗
          pkg.log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, Hs, Hp⟩
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_auto
  iStructNamed Hp
  wp_apply (vsrnet.wp_jdec_logs H b dq bs i _ e _ es R hes hb) $$ [Hs Logs]
    as ⟨Hs, %sl, Logs, Hown, Hcap⟩
  · isplitr; · iexact Hset
    iframe
  ihave Hp : (p ↦ { r with Logs' := sl } : IProp GF) $$ [ViewNum OpNum CommitNum Logs ReplicaID]
  · iapply typedPointsto_combine _ _ _ Hpnn
    simp only [typedPointstoDef]
    iframe
  iapply HΦ; iframe

/-- `jdecMember_events_StartView(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_StartView_4 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.StartView) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_StartView)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_StartView(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_StartView (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.StartView) (v : Nat) (k : Nat) (c : Nat) (es : List Entry) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_k : k < 2 ^ 64) (h_c : c < 2 ^ 64) (h_es : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.startView v k c es rid)) ++ rest) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_StartView)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.startView v k c es rid))).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, p ↦ pkg.events.StartView.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (c : Int)) sl (W64 (rid : Int)) ∗
          pkg.log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.startView v k c es rid)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"op_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN k ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"commit_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN c ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"logs" ++ [34#8, 58#8])) ++ (VsrJson.ser (VsrJson.logsJV es) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8])))))))))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"op_num" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : (34#8 :: (JsonScan.decN k ++ [34#8])) = V1 at hb
  generalize hM2 : (34#8 :: (go!"commit_num" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN c ++ [34#8])) = V2 at hb
  generalize hM3 : (34#8 :: (go!"logs" ++ [34#8, 58#8])) = M3 at hb
  generalize hV3 : VsrJson.ser (VsrJson.logsJV es) = V3 at hb
  generalize hM4 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M4 at hb
  generalize hV4 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V4 at hb
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
  have hb10 := vsrnet.drop_app bs _ _ _ hb9
  have hb11 := vsrnet.drop_app bs _ _ _ hb10
  have hb12 := vsrnet.drop_app bs _ _ _ hb11
  have hb13 := vsrnet.drop_app bs _ _ _ hb12
  have hb14 := vsrnet.drop_app bs _ _ _ hb13
  have hb15 := vsrnet.drop_app bs _ _ _ hb14
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN (v)).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 9 := by rw [← hM1]; rfl
  have lV1 : V1.length = (JsonScan.decN (k)).length + 2 := by rw [← hV1]; simp
  have lM2 : M2.length = 13 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN (c)).length + 2 := by rw [← hV2]; simp
  have lM3 : M3.length = 7 := by rw [← hM3]; rfl
  have lV3 : V3.length = (VsrJson.ser (VsrJson.logsJV es)).length := by rw [← hV3]
  have lM4 : M4.length = 13 := by rw [← hM4]; rfl
  have lV4 : V4.length = (JsonScan.decN (rid)).length + 2 := by rw [← hV4]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.startView v k c es rid))).length = 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length + 1 + 13 + V4.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2, ← hM3, ← hV3, ← hM4, ← hV4] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2, lM3, lM4] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb15
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.StartView) (sl : GoSlice),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗ "HL" ∷ vsrnet.logsRes (decide (3 < n)) sl es ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.StartView.mk (W64 (v : Int)) r.OpNum' r.CommitNum' r.Logs' r.ReplicaID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 ∧ rr = pkg.events.StartView.mk (W64 (v : Int)) (W64 (k : Int)) r.CommitNum' r.Logs' r.ReplicaID') ∨ (n = 3 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 ∧ rr = pkg.events.StartView.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (c : Int)) r.Logs' r.ReplicaID') ∨ (n = 4 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length + 1 ∧ rr = pkg.events.StartView.mk (W64 (v : Int)) (W64 (k : Int)) (W64 (c : Int)) sl r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r, slice.nil
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl []
    · rw [show decide (3 < 0) = false from rfl]; simp only [vsrnet.logsRes]; try itrivial
    ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · simp only [show decide (3 < 0) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (v) ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_StartView_0 H b dq bs _ p e _ (v) _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (v)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (3 < 1) = false from rfl]; iexact HL
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (3 < 1) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"op_num" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"op_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (k) ++ 34#8 :: ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))))) := by
      rw [hvz, hb5, ← hV1]; simp
    wp_apply (vsrnet.wp_jdecMember_StartView_1 H b dq bs _ p e _ (k) _ hv h_k) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (k)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (3 < 2) = false from rfl]; iexact HL
    ipureintro; right; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (3 < 2) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"commit_num" ++ 34#8 :: 58#8 :: (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"commit_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (c) ++ 34#8 :: ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_StartView_2 H b dq bs _ p e _ (c) _ hv h_c) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (c)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length]? = some 44#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 3, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (3 < 3) = false from rfl]; iexact HL
    ipureintro; right; right; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (3 < 3) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"logs" ++ 34#8 :: 58#8 :: (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb10, ← hM3]; simp
    wp_apply (H.Member b dq bs kw go!"logs" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int))) =
        VsrJson.ser (VsrJson.logsJV es) ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))) := by
      rw [hvz, hb11, ← hV3]
    wp_apply (vsrnet.wp_jdecMember_StartView_3 H b dq bs _ p e _ es _ h_es hv) $$ [Hs Hp]
      as ⟨Hs, %sl', Hp, Hown, Hcap⟩
    · isplitr; · iexact Hset
      iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int)) +
        (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length := by
      rw [hvz, lV3]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length]? = some 44#8 := hidx _ _ _ (by rw [hb12]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 4, _, _, sl'
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [Hown Hcap]
    · rw [show decide (3 < 4) = true from rfl]; simp only [vsrnet.logsRes]; isplitl [Hown]; · iexact Hown
      iexact Hcap
    ipureintro; right; right; right; right; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (3 < 4) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V4 ++ ([125#8] ++ rest))) := by
      rw [hk, hb13, ← hM4]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (rid) ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb14, ← hV4]; simp
    wp_apply (vsrnet.wp_jdecMember_StartView_4 H b dq bs _ p e _ (rid) _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN (rid)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length + 1 + 13 + V4.length := by
      rw [hvz, lV4]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length + 1 + 13 + V4.length]? = some 125#8 := hidx _ _ _ (by rw [hb15]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length + 1 + 13 + V4.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 9 + V1.length + 1 + 13 + V2.length + 1 + 7 + V3.length + 1 + 13 + V4.length + 1) : Nat) : Int)
      by congr 2; omega]
    simp only [vsrnet.logsRes]
    iNamed HL
    iapply HΦ; iframe

/-- `jdecMember_events_NewState(b, i, "view_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_NewState_0 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.NewState) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_NewState)) (Val #b)) (Val #i))
        (Val #(go!"view_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ViewNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_NewState(b, i, "logs", p, e)` on a `[]Log`'s encoding at `i`. -/
theorem vsrnet.wp_jdecMember_NewState_1 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.NewState) (es : List Entry) (R : List w8)
    (hes : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.logsJV es) ++ R) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_NewState)) (Val #b)) (Val #i))
        (Val #(go!"logs"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, p ↦ { r with Logs' := sl } ∗
          pkg.log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, Hs, Hp⟩
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_auto
  iStructNamed Hp
  wp_apply (vsrnet.wp_jdec_logs H b dq bs i _ e _ es R hes hb) $$ [Hs Logs]
    as ⟨Hs, %sl, Logs, Hown, Hcap⟩
  · isplitr; · iexact Hset
    iframe
  ihave Hp : (p ↦ { r with Logs' := sl } : IProp GF) $$ [ViewNum Logs CommitNum OpNum ReplicaID]
  · iapply typedPointsto_combine _ _ _ Hpnn
    simp only [typedPointstoDef]
    iframe
  iapply HΦ; iframe

/-- `jdecMember_events_NewState(b, i, "commit_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_NewState_2 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.NewState) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_NewState)) (Val #b)) (Val #i))
        (Val #(go!"commit_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with CommitNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_NewState(b, i, "op_num", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_NewState_3 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.NewState) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_NewState)) (Val #b)) (Val #i))
        (Val #(go!"op_num"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with OpNum' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdecMember_events_NewState(b, i, "replica_id", p, e)` on `"n"` at `i`. -/
theorem vsrnet.wp_jdecMember_NewState_4 (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64)
    (p e : Loc) (r : pkg.events.NewState) (n : Nat) (rest : List w8)
    (hb : bs.drop (uint.nat i) = 34#8 :: (JsonScan.decN n ++ 34#8 :: rest)) (hn : n < 2 ^ 64) :
    {{ (b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (App (Val (@! pkg.events.jdecMember_NewState)) (Val #b)) (Val #i))
        (Val #(go!"replica_id"))) (Val #p)) (Val #e))
    {{ RET #(W64 ((uint.nat i + (JsonScan.decN n).length + 2 : Nat) : Int));
        b ↦*{dq} bs ∗ p ↦ { r with ReplicaID' := W64 (n : Int) } }} := by
  wp_start as ⟨Hs, Hp⟩
  wp_auto
  wp_apply (H.QuotedUint b dq bs i _ n rest hb (by simp; omega)) $$ Hs as Hs
  iapply HΦ; iframe

/-- `jdec_events_NewState(b, i, p, e)` on the encoding at `i`. -/
theorem vsrnet.wp_jdec_NewState (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (b : GoSlice) (dq : DFrac) (bs : List w8) (i : w64) (p e : Loc)
    (r : pkg.events.NewState) (v : Nat) (es : List Entry) (c : Nat) (k : Nat) (rid : Nat) (rest : List w8)
    (h_v : v < 2 ^ 64) (h_es : ∀ e ∈ es, e.cid < 2 ^ 64 ∧ e.req < 2 ^ 64 ∧ PlainStr e.op) (h_c : c < 2 ^ 64) (h_k : k < 2 ^ 64) (h_rid : rid < 2 ^ 64)
    (hb : bs.drop (uint.nat i) = VsrJson.ser (VsrJson.payJV (.newState v es c k rid)) ++ rest) :
    {{ (isPkgInit (PROP := IProp GF) pkg_id.github_com.tangledbytes.go_vsr.pkg.log ∗
        vsrnet.logsRoute (GF := GF) ∗
        b ↦*{dq} bs ∗ p ↦ r : IProp GF) }}
      (App (App (App (App (Val (@! pkg.events.jdec_NewState)) (Val #b)) (Val #i)) (Val #p))
        (Val #e))
    {{ RET #(W64 ((uint.nat i + (VsrJson.ser (VsrJson.payJV (.newState v es c k rid))).length : Nat) : Int));
        b ↦*{dq} bs ∗ ∃ sl : GoSlice, p ↦ pkg.events.NewState.mk (W64 (v : Int)) sl (W64 (c : Int)) (W64 (k : Int)) (W64 (rid : Int)) ∗
          pkg.log.ownLogs sl (DFrac.own 1) es ∗ ownSliceCap pkg.log.Log sl (DFrac.own 1) }} := by
  wp_start as ⟨#Hset, Hs, Hp⟩
  ihave %Hlen := ownSlice_len $$ Hs
  have hl63 := models_lab.jsoncodec.len_lt b bs Hlen
  have hser : VsrJson.ser (VsrJson.payJV (.newState v es c k rid)) =
      [123#8] ++ ((34#8 :: (go!"view_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN v ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"logs" ++ [34#8, 58#8])) ++ (VsrJson.ser (VsrJson.logsJV es) ++ ([44#8] ++ ((34#8 :: (go!"commit_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN c ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"op_num" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN k ++ [34#8])) ++ ([44#8] ++ ((34#8 :: (go!"replica_id" ++ [34#8, 58#8])) ++ ((34#8 :: (JsonScan.decN rid ++ [34#8])) ++ [125#8])))))))))))))) := by
    simp [VsrJson.ser, VsrJson.payJV, VsrJson.mkObj, VsrJson.serMs, VsrJson.serMsT, VsrJson.qn]
  rw [hser] at hb
  generalize hM0 : (34#8 :: (go!"view_num" ++ [34#8, 58#8])) = M0 at hb
  generalize hV0 : (34#8 :: (JsonScan.decN v ++ [34#8])) = V0 at hb
  generalize hM1 : (34#8 :: (go!"logs" ++ [34#8, 58#8])) = M1 at hb
  generalize hV1 : VsrJson.ser (VsrJson.logsJV es) = V1 at hb
  generalize hM2 : (34#8 :: (go!"commit_num" ++ [34#8, 58#8])) = M2 at hb
  generalize hV2 : (34#8 :: (JsonScan.decN c ++ [34#8])) = V2 at hb
  generalize hM3 : (34#8 :: (go!"op_num" ++ [34#8, 58#8])) = M3 at hb
  generalize hV3 : (34#8 :: (JsonScan.decN k ++ [34#8])) = V3 at hb
  generalize hM4 : (34#8 :: (go!"replica_id" ++ [34#8, 58#8])) = M4 at hb
  generalize hV4 : (34#8 :: (JsonScan.decN rid ++ [34#8])) = V4 at hb
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
  have hb10 := vsrnet.drop_app bs _ _ _ hb9
  have hb11 := vsrnet.drop_app bs _ _ _ hb10
  have hb12 := vsrnet.drop_app bs _ _ _ hb11
  have hb13 := vsrnet.drop_app bs _ _ _ hb12
  have hb14 := vsrnet.drop_app bs _ _ _ hb13
  have hb15 := vsrnet.drop_app bs _ _ _ hb14
  have lM0 : M0.length = 11 := by rw [← hM0]; rfl
  have lV0 : V0.length = (JsonScan.decN (v)).length + 2 := by rw [← hV0]; simp
  have lM1 : M1.length = 7 := by rw [← hM1]; rfl
  have lV1 : V1.length = (VsrJson.ser (VsrJson.logsJV es)).length := by rw [← hV1]
  have lM2 : M2.length = 13 := by rw [← hM2]; rfl
  have lV2 : V2.length = (JsonScan.decN (c)).length + 2 := by rw [← hV2]; simp
  have lM3 : M3.length = 9 := by rw [← hM3]; rfl
  have lV3 : V3.length = (JsonScan.decN (k)).length + 2 := by rw [← hV3]; simp
  have lM4 : M4.length = 13 := by rw [← hM4]; rfl
  have lV4 : V4.length = (JsonScan.decN (rid)).length + 2 := by rw [← hV4]; simp
  have lser : (VsrJson.ser (VsrJson.payJV (.newState v es c k rid))).length = 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 := by
    rw [hser, ← hM0, ← hV0, ← hM1, ← hV1, ← hM2, ← hV2, ← hM3, ← hV3, ← hM4, ← hV4] at *; simp; omega
  simp only [List.length_cons, List.length_nil, lM0, lM1, lM2, lM3, lM4] at hb1 hb2 hb3 hb4 hb5 hb6 hb7 hb8 hb9 hb10 hb11 hb12 hb13 hb14 hb15
  have hidx : ∀ k (c : w8) (R : List w8), bs.drop k = c :: R → bs[k]? = some c := by
    intro k c R h; have := congrArg (fun l => l[0]?) h; simp only [List.getElem?_drop] at this
    simpa using this
  have hc0 : bs[uint.nat i]? = some 123#8 := hidx _ _ _ (by rw [hb]; rfl)
  have hlen := congrArg List.length hb15
  simp only [List.length_drop, List.length_append, List.length_cons, List.length_nil] at hlen
  wp_auto
  wp_apply (H.At b dq bs i 123#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide)]; exact hc0)) $$ Hs as Hs
  rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc0 (by decide), show W64 ((uint.nat i : Nat) : Int) = i by word]
  have hc1 : bs[uint.nat i + 1]? = some 34#8 := hidx _ _ _ (by rw [hb1, ← hM0]; rfl)
  wp_apply (H.Empty b dq bs i 34#8 (by omega)
    (by rw [models_lab.jsoncodec.skipEnd_ns' bs _ _ hc1 (by decide)]; exact hc1)) $$ Hs as Hs
  ihave IH : iprop(∃ (n : Nat) (kw : w64) (rr : pkg.events.NewState) (sl : GoSlice),
      "k" ∷ k_ptr ↦ kw ∗ "Hp" ∷ p ↦ rr ∗ "HL" ∷ vsrnet.logsRes (decide (1 < n)) sl es ∗
      "%Hn" ∷ ⌜(n = 0 ∧ uint.nat kw = uint.nat i + 1 ∧ rr = r) ∨ (n = 1 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 ∧ rr = pkg.events.NewState.mk (W64 (v : Int)) r.Logs' r.CommitNum' r.OpNum' r.ReplicaID') ∨ (n = 2 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 ∧ rr = pkg.events.NewState.mk (W64 (v : Int)) sl r.CommitNum' r.OpNum' r.ReplicaID') ∨ (n = 3 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 ∧ rr = pkg.events.NewState.mk (W64 (v : Int)) sl (W64 (c : Int)) r.OpNum' r.ReplicaID') ∨ (n = 4 ∧ uint.nat kw = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length + 1 ∧ rr = pkg.events.NewState.mk (W64 (v : Int)) sl (W64 (c : Int)) (W64 (k : Int)) r.ReplicaID')⌝) $$ [k Hp]
  · iexists 0, _, r, slice.nil
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl []
    · rw [show decide (1 < 0) = false from rfl]; simp only [vsrnet.logsRes]; try itrivial
    ipureintro; left; exact ⟨rfl, by word, rfl⟩
  wp_for IH
  try (rw [if_pos (by simp)]; wp_auto)
  rcases Hn with ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩ | ⟨rfl, hk, rfl⟩
  · simp only [show decide (1 < 0) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"view_num" ++ 34#8 :: 58#8 :: (V0 ++ ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))))))))) := by
      rw [hk, hb1, ← hM0]; simp
    wp_apply (H.Member b dq bs kw go!"view_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (v) ++ 34#8 :: ([44#8] ++ (M1 ++ (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))))))))) := by
      rw [hvz, hb2, ← hV0]; simp
    wp_apply (vsrnet.wp_jdecMember_NewState_0 H b dq bs _ p e _ (v) _ hv h_v) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"view_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (v)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length := by
      rw [hvz, lV0]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length]? = some 44#8 := hidx _ _ _ (by rw [hb3]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 1, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (1 < 1) = false from rfl]; iexact HL
    ipureintro; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 1) = false from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"logs" ++ 34#8 :: 58#8 :: (V1 ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))))))) := by
      rw [hk, hb4, ← hM1]; simp
    wp_apply (H.Member b dq bs kw go!"logs" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int))) =
        VsrJson.ser (VsrJson.logsJV es) ++ ([44#8] ++ (M2 ++ (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))))) := by
      rw [hvz, hb5, ← hV1]
    wp_apply (vsrnet.wp_jdecMember_NewState_1 H b dq bs _ p e _ es _ h_es hv) $$ [Hs Hp]
      as ⟨Hs, %sl', Hp, Hown, Hcap⟩
    · isplitr; · iexact Hset
      iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"logs").length + 3 : Nat) : Int)) +
        (VsrJson.ser (VsrJson.logsJV es)).length : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length := by
      rw [hvz, lV1]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length]? = some 44#8 := hidx _ _ _ (by rw [hb6]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 2, _, _, sl'
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [Hown Hcap]
    · rw [show decide (1 < 2) = true from rfl]; simp only [vsrnet.logsRes]; isplitl [Hown]; · iexact Hown
      iexact Hcap
    ipureintro; right; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 2) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"commit_num" ++ 34#8 :: 58#8 :: (V2 ++ ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))))))) := by
      rw [hk, hb7, ← hM2]; simp
    wp_apply (H.Member b dq bs kw go!"commit_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (c) ++ 34#8 :: ([44#8] ++ (M3 ++ (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))))) := by
      rw [hvz, hb8, ← hV2]; simp
    wp_apply (vsrnet.wp_jdecMember_NewState_2 H b dq bs _ p e _ (c) _ hv h_c) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"commit_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (c)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length := by
      rw [hvz, lV2]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length]? = some 44#8 := hidx _ _ _ (by rw [hb9]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 3, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (1 < 3) = true from rfl]; iexact HL
    ipureintro; right; right; right; left; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 3) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"op_num" ++ 34#8 :: 58#8 :: (V3 ++ ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest)))))) := by
      rw [hk, hb10, ← hM3]; simp
    wp_apply (H.Member b dq bs kw go!"op_num" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (k) ++ 34#8 :: ([44#8] ++ (M4 ++ (V4 ++ ([125#8] ++ rest))))) := by
      rw [hvz, hb11, ← hV3]; simp
    wp_apply (vsrnet.wp_jdecMember_NewState_3 H b dq bs _ p e _ (k) _ hv h_k) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"op_num").length + 3 : Nat) : Int)) +
        (JsonScan.decN (k)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length := by
      rw [hvz, lV3]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length]? = some 44#8 := hidx _ _ _ (by rw [hb12]; rfl)
    wp_apply (H.Next b dq bs _ 44#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    iframe
    iexists 4, _, _, sl
    isplitl [k]; · iexact k
    isplitl [Hp]; · iexact Hp
    isplitl [HL]
    · rw [show decide (1 < 4) = true from rfl]; iexact HL
    ipureintro; right; right; right; right; exact ⟨rfl, by word, rfl⟩
  · simp only [show decide (1 < 4) = true from rfl]
    have hm : bs.drop (uint.nat kw) = 34#8 :: (go!"replica_id" ++ 34#8 :: 58#8 :: (V4 ++ ([125#8] ++ rest))) := by
      rw [hk, hb13, ← hM4]; simp
    wp_apply (H.Member b dq bs kw go!"replica_id" _ (by decide) hm) $$ Hs as Hs
    have hvz : uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) =
        uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length + 1 + 13 := by simp; word
    have hv : bs.drop (uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int))) =
        34#8 :: (JsonScan.decN (rid) ++ 34#8 :: ([125#8] ++ rest)) := by
      rw [hvz, hb14, ← hV4]; simp
    wp_apply (vsrnet.wp_jdecMember_NewState_4 H b dq bs _ p e _ (rid) _ hv h_rid) $$ [Hs Hp] as ⟨Hs, Hp⟩
    · iframe
    have hez : uint.nat (W64 ((uint.nat (W64 ((uint.nat kw + (go!"replica_id").length + 3 : Nat) : Int)) +
        (JsonScan.decN (rid)).length + 2 : Nat) : Int)) = uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length := by
      rw [hvz, lV4]; word
    have hc : bs[uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length]? = some 125#8 := hidx _ _ _ (by rw [hb15]; rfl)
    wp_apply (H.Next b dq bs _ 125#8 (by omega)
      (by rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]; exact hc)) $$ Hs as Hs
    rw [hez, models_lab.jsoncodec.skipEnd_ns' bs _ _ hc (by decide)]
    wp_for_post
    rw [lser]
    rw [show W64 ((uint.nat i + 1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1 : Nat) : Int)
      = W64 ((uint.nat i + (1 + 11 + V0.length + 1 + 7 + V1.length + 1 + 13 + V2.length + 1 + 9 + V3.length + 1 + 13 + V4.length + 1) : Nat) : Int)
      by congr 2; omega]
    simp only [vsrnet.logsRes]
    iNamed HL
    iapply HΦ; iframe

/-- A payload's encoding scans as one complete value. -/
theorem vsrnet.scanL_encPayload (m : Msg) (hm : PlainMsg m) :
    JsonScan.scanL (pkg.events.encPayload m) true = (0, (pkg.events.encPayload m).length) := by
  obtain ⟨ms, hms⟩ := VsrJson.payJV_obj m
  have := VsrJson.top_v (VsrJson.payJV m) (VsrJson.payJV_ok m hm) [] 0 false true
    (VsrJson.payJV_maxd m) (by rw [hms]; trivial)
  simpa [JsonScan.scanL, pkg.events.encPayload, VsrJson.encPayload] using this

/-- **`TypeCodecs` of `events.Request`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_Request (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.Request.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.Request.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i id cid op
  obtain ⟨h1, h2⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.request id cid op)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.request id cid op) hm hlen
  have hsc := vsrnet.scanL_encPayload (.request id cid op) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.request id cid op)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.reqJV id cid op) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_Request H data dq _ (W64 0) p err_ptr _ id cid op [] h1 h2 hm hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists _
  ipureintro
  refine ⟨rfl, ?_⟩
  try simp only [pkg.events.reqIs]
  and_intros <;> first | rfl | word

/-- **`TypeCodecs` of `events.Reply`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_Reply (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.Reply.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.Reply.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i id cid v res
  obtain ⟨h1, h2, h3⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.reply id cid v res)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.reply id cid v res) hm hlen
  have hsc := vsrnet.scanL_encPayload (.reply id cid v res) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.reply id cid v res)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.reply id cid v res)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_Reply H data dq _ (W64 0) p err_ptr _ id cid v res [] h1 h2 h3 hm hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists _
  ipureintro
  refine ⟨rfl, ?_⟩
  try simp only [pkg.events.reqIs]
  and_intros <;> first | rfl | word

/-- **`TypeCodecs` of `events.Prepare`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_Prepare (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.Prepare.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.Prepare.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i v k c en rid
  obtain ⟨h1, h2, h3, ⟨h4, h5⟩, h6⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.prepare v k c en rid)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.prepare v k c en rid) hm hlen
  have hsc := vsrnet.scanL_encPayload (.prepare v k c en rid) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.prepare v k c en rid)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.prepare v k c en rid)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_Prepare H data dq _ (W64 0) p err_ptr _ v k c en rid [] h1 h2 h3 h5 h4 hm h6 hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists _
  ipureintro
  refine ⟨rfl, ?_⟩
  try simp only [pkg.events.reqIs]
  and_intros <;> first | rfl | word

/-- **`TypeCodecs` of `events.PrepareOK`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_PrepareOK (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.PrepareOK.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.PrepareOK.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i v k rid
  obtain ⟨h1, h2, h3⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.prepareOK v k rid)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.prepareOK v k rid) hm hlen
  have hsc := vsrnet.scanL_encPayload (.prepareOK v k rid) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.prepareOK v k rid)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.prepareOK v k rid)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_PrepareOK H data dq _ (W64 0) p err_ptr _ v k rid [] h1 h2 h3 hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists _
  ipureintro
  refine ⟨rfl, ?_⟩
  try simp only [pkg.events.reqIs]
  and_intros <;> first | rfl | word

/-- **`TypeCodecs` of `events.Commit`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_Commit (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.Commit.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.Commit.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i v c rid
  obtain ⟨h1, h2, h3⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.commit v c rid)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.commit v c rid) hm hlen
  have hsc := vsrnet.scanL_encPayload (.commit v c rid) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.commit v c rid)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.commit v c rid)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_Commit H data dq _ (W64 0) p err_ptr _ v c rid [] h1 h2 h3 hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists _
  ipureintro
  refine ⟨rfl, ?_⟩
  try simp only [pkg.events.reqIs]
  and_intros <;> first | rfl | word

/-- **`TypeCodecs` of `events.StartViewChange`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_StartViewChange (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.StartViewChange.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.StartViewChange.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i v rid
  obtain ⟨h1, h2⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.startViewChange v rid)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.startViewChange v rid) hm hlen
  have hsc := vsrnet.scanL_encPayload (.startViewChange v rid) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.startViewChange v rid)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.startViewChange v rid)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_StartViewChange H data dq _ (W64 0) p err_ptr _ v rid [] h1 h2 hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists _
  ipureintro
  refine ⟨rfl, ?_⟩
  try simp only [pkg.events.reqIs]
  and_intros <;> first | rfl | word

/-- **`TypeCodecs` of `events.DoViewChange`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_DoViewChange (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.DoViewChange.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.DoViewChange.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i d
  obtain ⟨v, es, lnv, c, rid⟩ := d
  obtain ⟨h1, h2, h3, h4, h5, hbe⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.doViewChange ⟨v, es, lnv, c, rid⟩)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.doViewChange ⟨v, es, lnv, c, rid⟩) hm hlen
  have hsc := vsrnet.scanL_encPayload (.doViewChange ⟨v, es, lnv, c, rid⟩) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.doViewChange ⟨v, es, lnv, c, rid⟩)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.doViewChange ⟨v, es, lnv, c, rid⟩)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  ihave #Hroute := vsrnet.logsRoute_of H $$ Hset
  wp_apply +noauto (vsrnet.wp_jdec_DoViewChange H data dq _ (W64 0) p err_ptr _ v es lnv c rid [] h1 (fun e he => ⟨(hbe e he).1, (hbe e he).2, hm e he⟩) h3 h2 h4 h5 hb0) $$ [Hd Hz]
    as ⟨Hd, %sl, Hp, Hown, Hcap⟩
  · isplitr
    · iexact Hroute
    iframe
  ihave Hown := pkg.log.ownLogs_persist _ _ _ $$ Hown
  imod Hown with #Hown
  wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  isplitl [Hp]
  · iexact Hp
  isplitr
  · iexists _
    isplitr
    · ipureintro
      refine ⟨rfl, ?_⟩
      and_intros <;> first | rfl | word
    iexact Hown
  iexact Hcap

/-- **`TypeCodecs` of `events.StartView`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_StartView (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.StartView.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.StartView.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i v k c es rid
  obtain ⟨h1, h2, h3, h4, hbe⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.startView v k c es rid)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.startView v k c es rid) hm hlen
  have hsc := vsrnet.scanL_encPayload (.startView v k c es rid) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.startView v k c es rid)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.startView v k c es rid)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  ihave #Hroute := vsrnet.logsRoute_of H $$ Hset
  wp_apply +noauto (vsrnet.wp_jdec_StartView H data dq _ (W64 0) p err_ptr _ v k c es rid [] h1 h2 h3 (fun e he => ⟨(hbe e he).1, (hbe e he).2, hm e he⟩) h4 hb0) $$ [Hd Hz]
    as ⟨Hd, %sl, Hp, Hown, Hcap⟩
  · isplitr
    · iexact Hroute
    iframe
  ihave Hown := pkg.log.ownLogs_persist _ _ _ $$ Hown
  imod Hown with #Hown
  wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  isplitl [Hp]
  · iexact Hp
  isplitr
  · iexists _
    isplitr
    · ipureintro
      refine ⟨rfl, ?_⟩
      and_intros <;> first | rfl | word
    iexact Hown
  iexact Hcap

/-- **`TypeCodecs` of `events.GetState`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_GetState (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.GetState.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.GetState.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i v k rid
  obtain ⟨h1, h2, h3⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.getState v k rid)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.getState v k rid) hm hlen
  have hsc := vsrnet.scanL_encPayload (.getState v k rid) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.getState v k rid)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.getState v k rid)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_GetState H data dq _ (W64 0) p err_ptr _ v k rid [] h1 h2 h3 hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists _
  ipureintro
  refine ⟨rfl, ?_⟩
  try simp only [pkg.events.reqIs]
  and_intros <;> first | rfl | word

/-- **`TypeCodecs` of `events.NewState`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_NewState (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.NewState.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.NewState.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  rename_i v es c k rid
  obtain ⟨h1, h2, h3, h4, hbe⟩ := hmb
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload (.newState v es c k rid)).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid (.newState v es c k rid) hm hlen
  have hsc := vsrnet.scanL_encPayload (.newState v es c k rid) hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload (.newState v es c k rid)).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV (.newState v es c k rid)) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  ihave #Hroute := vsrnet.logsRoute_of H $$ Hset
  wp_apply +noauto (vsrnet.wp_jdec_NewState H data dq _ (W64 0) p err_ptr _ v es c k rid [] h1 (fun e he => ⟨(hbe e he).1, (hbe e he).2, hm e he⟩) h2 h3 h4 hb0) $$ [Hd Hz]
    as ⟨Hd, %sl, Hp, Hown, Hcap⟩
  · isplitr
    · iexact Hroute
    iframe
  ihave Hown := pkg.log.ownLogs_persist _ _ _ $$ Hown
  imod Hown with #Hown
  wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  isplitl [Hp]
  · iexact Hp
  isplitr
  · iexists _
    isplitr
    · ipureintro
      refine ⟨rfl, ?_⟩
      and_intros <;> first | rfl | word
    iexact Hown
  iexact Hcap

/-- **`TypeCodecs` of `events.Heartbeat`, proved**: its `JSONModelUnmarshal` meets the kit's contract
(`decP`'s payload case at this type; the other cases are at other pointer types). -/
theorem vsrnet.unmarshalOk_Heartbeat (H : vsrnet.DecSpecs (GF := GF) (hG := hG)) (l : Loc) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType pkg.events.Heartbeat.ty) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.Heartbeat.ty) #l) := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec HΦ
  rw [vsrnet.dec_eq]; unfold vsrnet.decP
  icases Hdec with (⟨%_, %ws, %m, %p, %fr, %hb, %hws, %hm, %hfr, %hptr, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hb, %hm, %hmb, %hptr, #Hpkg, #Hset, Hz, Hk⟩ |
    ⟨%_, %es, %p, %hb, %hes, %hptr, -⟩)
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
    first | exact hty | exact absurd hty (by decide) | exact absurd hty.1 (by decide)
  rotate_left
  · exfalso
    have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq, go.GoType.Named.injEq, reduceCtorEq] at hty
  have hlp := ((interface_mkOk_inj _ _ _ _).1 hptr).2
  have hty := ((interface_mkOk_inj _ _ _ _).1 hptr).1
  rw [hlp]
  cases m <;> simp only [pkg.events.payloadTy, pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty, pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty, pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty, pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty, vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, go.GoType.PointerType.injEq,
    go.GoType.Named.injEq, reduceCtorEq] at hty
  all_goals (try (exfalso; first | exact hty | exact absurd hty (by decide) |
    exact absurd hty.1 (by decide)))
  subst hb
  ihave %Hlen := ownSlice_len $$ Hd
  have hlen : (pkg.events.encPayload .heartbeat).length < 2 ^ 64 := by
    have := models_lab.jsoncodec.len_lt data _ Hlen; omega
  have hval := vsrnet.encPayload_valid .heartbeat hm hlen
  have hsc := vsrnet.scanL_encPayload .heartbeat hm
  wp_method_call
  wp_auto
  wp_apply (H.Valid data dq _ hsc) $$ Hd as Hd
  simp only [pkg.events.payloadZero]
  ihave %Hpnn := typedPointsto_not_null _ _ _ $$ Hz
  rw [decide_eq_false Hpnn]
  wp_auto
  have hb0 : (pkg.events.encPayload .heartbeat).drop (uint.nat (W64 0)) = VsrJson.ser (VsrJson.payJV .heartbeat) ++ [] := by
    simp [pkg.events.encPayload, VsrJson.encPayload, VsrJson.payJV]
  wp_apply (vsrnet.wp_jdec_Heartbeat H data dq _ (W64 0) p err_ptr _ [] hb0) $$ [Hd Hz]
    as ⟨Hd, Hp⟩
  · iframe
  try wp_auto
  iapply HΦ $$ Hd
  ileft
  isplitr
  · ipureintro; exact hval
  iexists true
  isplitr
  · ipureintro; simp
  iapply Hk
  simp only [pkg.events.payloadAt, pkg.events.payloadOf]
  iexists _
  iframe
  iexists (zero_val pkg.events.Heartbeat)
  ipureintro; trivial

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
