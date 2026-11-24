/-
The kit's generated codec, server side (`CodecSrv.lean`'s `SrvCodecLaws`), proved: decoding an
encoding of a request argument into the fresh value `NewArg()` allocates gives back exactly the
encoded value, and the replies' encoders give `Wire.lean`'s bytes.
-/
module

public import Dsverify.Proof.github_com.despreston.go_craq.Craq.CodecSrv
public import Dsverify.Proof.github_com.despreston.go_craq.Craq.CodecProof

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)

namespace github_com.despreston.go_craq

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [examples.craqnet.Assumptions] [transport.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

/-! ## Decoding the arguments -/

theorem wp_rpcDec_t22 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t22)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb HΦ
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_func_call
  wp_call
  wp_auto
  rcases bs with _ | ⟨c, rest⟩
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 1) by simp at Hl; word)]
    wp_auto
    iapply HΦ
    simp only [decHdr]
    iframe
  · have hlen : sint.Z b.len = rest.length + 1 := by
      have := Hl.1; simp only [List.length_cons] at this
      have h2 : ((sint.Z b.len).toNat : Int) = sint.Z b.len := Int.toNat_of_nonneg Hl.2
      rw [show sint.nat b.len = (sint.Z b.len).toNat from rfl] at this; omega
    rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 1) by
      rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
    wp_auto
    rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
      rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
    wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
    · iframe; ipureintro; rfl
    by_cases hc : c = W8 1
    · simp only [hc, decide_true, Bool.not_true]
      wp_auto
      rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap by
        rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
      wp_auto
      icases ownSlice_suffix (W64 1) b dq _ ⟨by decide, by rw [show sint.Z (W64 1) = 1 from rfl]; omega⟩
        $$ Hb with ⟨Hr, Hback⟩
      iapply HΦ
      simp only [decHdr, hc, ↓reduceIte, show sint.nat (W64 1) = 1 from rfl, List.drop_succ_cons,
        List.drop_zero]
      iframe
    · simp only [hc, decide_false, Bool.not_false]
      wp_auto
      iapply HΦ
      simp only [decHdr, if_neg hc]
      iframe

theorem getTag_tagged (t body : List w8) (ht : t.length < 2 ^ 64) :
    getTag (tagged t body) = some (t, body) := by
  unfold tagged; exact getTag_encStr' _ _ ht

theorem decA_EmptyArgs : decA_EmptyArgs.spec (GF := GF) := by
  intro p args Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encEmptyArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t22 r _ dq p $$ Hr
  iintro %r2 %ok2 H2
  simp only [show decHdr (strct []) = some [] from rfl]
  icases H2 with ⟨%Hok, Hr2, Hback2⟩
  subst Hok
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
  wp_auto
  ihave Hd := Hback $$ [Hback2 Hr2]
  · iapply Hback2 $$ Hr2
  rw [show r2.len = W64 0 by simp at Hl2; word]
  wp_auto
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial

set_option hygiene false in
/-- A decoding's success tail: `Hr2`, `Hback2` (the inner decoder's rest, empty), `Hback`; ends
with `Hd` back and the length check done, before `HΦ`. -/
macro "dec_ok" : tactic => `(tactic| (
  ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
  wp_auto
  ihave Hd := Hback $$ [Hback2 Hr2]
  · iapply Hback2 $$ Hr2
  rw [show r2.len = W64 0 by simp at Hl2; word]
  wp_auto))

theorem len_fStr (k : GoString) : k.length ≤ (fStr k).length := by
  by_cases hk : k = []
  · simp [hk]
  · simp [fStr, fld, hk, encStr]; omega

theorem decA_string : decA_string.spec (GF := GF) := by
  intro p args s Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have hs : s.length < 2 ^ 64 := by
    have h3 : sint.Z data.len < 2 ^ 63 := by word
    have h2 : s.length ≤ (encString s).length := by simp [encString, tagged, encStr]; omega
    omega
  have hd : getTag (encStr s) = some (s, []) := by
    have := getTag_encStr' s [] hs; simpa using this
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encString, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t5 r _ dq p _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ; simp only [ite_true]; iexact Hp
  simp only [ite_true]
  ipureintro; trivial

theorem wp_rpcDec_t18 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (k0 : GoString) (v0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.netrpc.CommitArgs.mk k0 v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decVR k0 v0 bs with
          | some ((k, v), rest) => ⌜ok = true⌝ ∗ p ↦ transport.netrpc.CommitArgs.mk k v ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ k v, p ↦ transport.netrpc.CommitArgs.mk k v) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t18)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decVR
  all_goals fld_step wp_rpcDec_t5 getTag Key fail struct_close decVR
  all_goals fld_step wp_rpcDec_t6 getU64 Version fail struct_close decVR
  all_goals ((try wp_auto); struct_close decVR)

theorem decA_CommitArgs : decA_CommitArgs.spec (GF := GF) := by
  intro p args k v Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have hk : k.length < 2 ^ 64 := by
    have h3 : sint.Z data.len < 2 ^ 63 := by word
    have h1 := len_fStr k
    have h2 : (fStr k).length ≤ (encCommitArgs k v).length := by
      simp [encCommitArgs, tagged, strct]; omega
    omega
  have hd := decVR_enc k v hk
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encCommitArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t18 r _ dq p _ _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ; simp only [ite_true]; iexact Hp
  simp only [ite_true]
  ipureintro; trivial

theorem wp_rpcDec_t14 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (k0 : GoString)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.netrpc.ClientWriteArgs.mk k0 slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decItem k0 bs with
          | some ((k, x), rest) => ⌜ok = true⌝ ∗
              (∃ sl, p ↦ transport.netrpc.ClientWriteArgs.mk k sl ∗ sl ↦* x) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ k sl, p ↦ transport.netrpc.ClientWriteArgs.mk k sl) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t14)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decItem
  all_goals fld_step wp_rpcDec_t5 getTag Key fail item_close decItem
  all_goals fld_step wp_rpcDec_t11 decBytes Value fail item_close decItem
  all_goals ((try wp_auto); item_close decItem)

theorem decA_ClientWriteArgs : decA_ClientWriteArgs.spec (GF := GF) := by
  intro p args k x Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have h3 : sint.Z data.len < 2 ^ 63 := by word
  have hk : k.length < 2 ^ 64 := by
    have h1 := len_fStr k
    have h2 : (fStr k).length ≤ (encClientWriteArgs k x).length := by
      simp [encClientWriteArgs, tagged, strct]; omega
    omega
  have hx : x.length < 2 ^ 64 := by
    have h1 := len_fBytes x
    have h2 : (fBytes x).length ≤ (encClientWriteArgs k x).length := by
      simp [encClientWriteArgs, tagged, strct]; omega
    omega
  have hd := decItem_enc k x hk hx
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encClientWriteArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t14 r _ dq p _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ; simp only [ite_true]; iexact Hp
  simp only [ite_true]
  ipureintro; trivial

/-- The pure `rpcDec_t31` (`WriteArgs`), into `{k0, nil, v0}`. -/
def decWA (k0 : GoString) (v0 : w64) (bs : List w8) : Option ((GoString × List w8 × w64) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getTag k0 r with
    | none => none
    | some (k, r) =>
      match decFld decBytes [] r with
      | none => none
      | some (x, r) =>
        match decFld getU64 v0 r with
        | none => none
        | some (v, r) => some ((k, x, v), r)

set_option hygiene false in
/-- Close a `WriteArgs` decoder's proof (the `Value` field in any of its states). -/
macro "wa_close " D:ident : tactic => `(tactic| (
  iapply HΦ
  simp only [$D:ident, decHdr, decFld, ↓reduceIte, *]
  iframe
  first
  | (icases Value with ⟨%sl, Value, Hsl⟩
     iexists sl
     iframe Hsl
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists slice.nil
     ihave Hsl := ownSlice_nil (V := w8) (DFrac.own 1)
     iframe Hsl
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases Value with ⟨%sl, Value, -⟩
     iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (icases Value with ⟨%sl, Value⟩
     iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _; iexists _; iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)))

set_option hygiene false in
/-- `hdr_step`, with the closing tactic `cl` for the header's failures. -/
macro "hdr_step_with " _D:ident " (" cl:tacticSeq ")" : tactic => `(tactic| (
  ihave %Hl := ownSlice_len _ _ _ $$ Hb
  ihave %Hwf := ownSlice_wf _ _ _ $$ Hb
  wp_func_call
  wp_call
  wp_auto
  rcases bs with _ | ⟨c, rest⟩
  · rw [decide_eq_true (show sint.Z b.len < sint.Z (W64 1) by simp at Hl; word)]
    wp_auto
    ($cl)
  have hlen : sint.Z b.len = rest.length + 1 := by
    have := Hl.1; simp only [List.length_cons] at this
    have h2 : ((sint.Z b.len).toNat : Int) = sint.Z b.len := Int.toNat_of_nonneg Hl.2
    rw [show sint.nat b.len = (sint.Z b.len).toNat from rfl] at this; omega
  rw [decide_eq_false (show ¬ sint.Z b.len < sint.Z (W64 1) by
    rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 0) ∧ sint.Z (W64 0) < sint.Z b.len by
    rw [show sint.Z (W64 0) = 0 from rfl]; omega)]
  wp_apply wp_load_slice_index b _ _ dq _ (by decide) $$ [Hb] with Hb
  · iframe; ipureintro; rfl
  by_cases hc : c = W8 1
  rotate_left
  · simp only [hc, decide_false, Bool.not_false]
    wp_auto
    ($cl)
  subst hc
  simp only [_root_.decide_true, Bool.not_true]
  wp_auto
  rw [if_pos (show 0 ≤ sint.Z (W64 1) ∧ sint.Z (W64 1) ≤ sint.Z b.len ∧ sint.Z b.len ≤ sint.Z b.cap by
    rw [show sint.Z (W64 1) = 1 from rfl]; omega)]
  icases ownSlice_tail b dq _ _ $$ Hb with ⟨%R, %HR, %hlR, Hr, Hback⟩
  rw [HR]
  wp_auto
  generalize hcur : rest = cur at *
  clear hcur))

theorem wp_rpcDec_t31 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (k0 : GoString) (v0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.netrpc.WriteArgs.mk k0 slice.nil v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decWA k0 v0 bs with
          | some ((k, x, v), rest) => ⌜ok = true⌝ ∗
              (∃ sl, p ↦ transport.netrpc.WriteArgs.mk k sl v ∗ sl ↦* x) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ k sl v, p ↦ transport.netrpc.WriteArgs.mk k sl v) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t31)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step_with decWA (wa_close decWA)
  all_goals fld_step wp_rpcDec_t5 getTag Key fail wa_close decWA
  all_goals fld_step wp_rpcDec_t11 decBytes Value fail wa_close decWA
  all_goals fld_step wp_rpcDec_t6 getU64 Version fail wa_close decWA
  all_goals ((try wp_auto); wa_close decWA)

theorem decWA_enc (k x : GoString) (v : w64) (hk : k.length < 2 ^ 64) (hx : x.length < 2 ^ 64) :
    decWA go!"" (W64 0) (strct [fStr k, fBytes x, fU64 v]) = some ((k, x, v), []) := by
  have e : strct [fStr k, fBytes x, fU64 v] = W8 1 :: (fStr k ++ (fBytes x ++ (fU64 v ++ []))) := by
    simp [strct]
  rw [e]
  simp only [decWA, decHdr, ↓reduceIte, decFld_fStr k _ hk, decFld_fBytes x _ hx, decFld_fU64]

theorem decA_WriteArgs : decA_WriteArgs.spec (GF := GF) := by
  intro p args k x v Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have h3 : sint.Z data.len < 2 ^ 63 := by word
  have hk : k.length < 2 ^ 64 := by
    have h1 := len_fStr k
    have h2 : (fStr k).length ≤ (encWriteArgs k x v).length := by
      simp [encWriteArgs, tagged, strct]; omega
    omega
  have hx : x.length < 2 ^ 64 := by
    have h1 := len_fBytes x
    have h2 : (fBytes x).length ≤ (encWriteArgs k x v).length := by
      simp [encWriteArgs, tagged, strct]; omega
    omega
  have hd := decWA_enc k x v hk hx
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encWriteArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t31 r _ dq p _ _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ; simp only [ite_true]; iexact Hp
  simp only [ite_true]
  ipureintro; trivial

/-- The pure `rpcDec_t28` (`NodeMeta`), into `m0`, with the values. -/
def decMetaV (m0 : MetaV) (bs : List w8) : Option (MetaV × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld decBool m0.isHead r with
    | none => none
    | some (h, r) =>
      match decFld decBool m0.isTail r with
      | none => none
      | some (t, r) =>
        match decFld getTag m0.prev r with
        | none => none
        | some (pr, r) =>
          match decFld getTag m0.next r with
          | none => none
          | some (nx, r) =>
            match decFld getTag m0.tail r with
            | none => none
            | some (tl, r) => some (⟨h, t, pr, nx, tl⟩, r)

set_option maxHeartbeats 4000000 in
theorem wp_rpcDec_t28V (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (m0 : MetaV)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ transport.NodeMeta.mk m0.isHead m0.isTail m0.prev m0.next m0.tail -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decMetaV m0 bs with
          | some (m, rest) => ⌜ok = true⌝ ∗
              p ↦ transport.NodeMeta.mk m.isHead m.isTail m.prev m.next m.tail ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ h t pr nx tl, p ↦ transport.NodeMeta.mk h t pr nx tl) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t28)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decMetaV
  all_goals fld_step wp_rpcDec_t29 decBool IsHead fail struct_close decMetaV
  all_goals fld_step wp_rpcDec_t29 decBool IsTail fail struct_close decMetaV
  all_goals fld_step wp_rpcDec_t5 getTag Prev fail struct_close decMetaV
  all_goals fld_step wp_rpcDec_t5 getTag Next fail struct_close decMetaV
  all_goals fld_step wp_rpcDec_t5 getTag Tail fail struct_close decMetaV
  all_goals ((try wp_auto); struct_close decMetaV)

theorem decFld_fBool (x : Bool) (rest : List w8) :
    decFld decBool false (fBool x ++ rest) = some (x, rest) := by
  apply decFld_fld
  · intro h; exact h
  · intro h; subst h
    simp only [encBool, ↓reduceIte, List.cons_append, List.nil_append, decBool]
    simp [show uint.Z (W8 1) = 1 from rfl]
    decide

theorem decMetaV_enc (m : MetaV) (hp : m.prev.length < 2 ^ 64) (hn : m.next.length < 2 ^ 64)
    (ht : m.tail.length < 2 ^ 64) :
    decMetaV ⟨false, false, go!"", go!"", go!""⟩
      (strct [fBool m.isHead, fBool m.isTail, fStr m.prev, fStr m.next, fStr m.tail]) =
      some (m, []) := by
  have e : strct [fBool m.isHead, fBool m.isTail, fStr m.prev, fStr m.next, fStr m.tail] =
      W8 1 :: (fBool m.isHead ++ (fBool m.isTail ++ (fStr m.prev ++ (fStr m.next ++
        (fStr m.tail ++ []))))) := by
    simp [strct]
  rw [e]
  simp only [decMetaV, decHdr, ↓reduceIte, decFld_fBool, decFld_fStr _ _ hp, decFld_fStr _ _ hn,
    decFld_fStr _ _ ht]

theorem decA_NodeMeta : decA_NodeMeta.spec (GF := GF) := by
  intro p args m Ψ
  unfold metaPtr
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have h3 : sint.Z data.len < 2 ^ 63 := by word
  have hl : ∀ s, (fStr s).length ≤ (encMeta m).length → s.length < 2 ^ 64 := by
    intro s h2; have h1 := len_fStr s; omega
  have hd := decMetaV_enc m
    (hl _ (by simp [encMeta, tagged, strct]; omega))
    (hl _ (by simp [encMeta, tagged, strct]; omega))
    (hl _ (by simp [encMeta, tagged, strct]; omega))
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encMeta, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t28V r _ dq p ⟨false, false, go!"", go!"", go!""⟩ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ; simp only [ite_true]; iexact Hp
  simp only [ite_true]
  ipureintro; trivial

/-! ### `PropagateRequest` -/

/-- `k` more request entries, after `acc`. -/
def decRQGo : Nat → List (GoString × w64) → List w8 → Option (List (GoString × w64) × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match getTag r with
    | none => none
    | some (key, r') =>
      match getU64 r' with
      | none => none
      | some (v, r'') => decRQGo k (acc ++ [(key, v)]) r''

/-- The pure `rpcDec_t4` (`PropagateRequest`): its entries in order. -/
def decRQ (bs : List w8) : Option (List (GoString × w64) × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decRQGo (uint.nat n) [] r else none

/-- The map of a list of request entries (later ones win). -/
def reqL (es : List (GoString × w64)) : GMap GoString w64 :=
  es.foldl (fun m e => <[e.1 := e.2]> m) ∅

theorem wp_rpcDec_t4 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ (null : Loc) -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decRQ bs with
          | some (es, rest) => ⌜ok = true⌝ ∗
              (∃ mp' : Loc, p ↦ mp' ∗ ownMap mp' (DFrac.own 1) (reqL es)) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ mp' : Loc, p ↦ mp') ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.craqnet.rpcDec_t4)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decRQ
  rcases hg : getU64 bs with _ | ⟨n, rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hb⟩
    subst Hok
    wp_auto
    iapply HΦ
    iframe
    ipureintro; rfl
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    ihave %Hl := ownSlice_lenZ _ _ _ $$ Hr
    wp_auto
    by_cases hn : uint.nat x ≤ rest.length
    rotate_left
    · rw [decide_eq_true (show uint.Z r.len < uint.Z x by word)]
      wp_auto
      iapply HΦ
      rw [if_neg hn]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr
    rw [decide_eq_false (show ¬ uint.Z r.len < uint.Z x by word)]
    rw [if_pos hn]
    wp_auto
    rw [go.make1_underlying, go.is_underlying (t := transport.PropagateRequest.ty)]
    wp_apply (wp_map_make1 (K := GoString) (V := w64) _ _) as %mp Hm
    (try wp_auto)
    ihave HI : (∃ (i : w64) (R : GoSlice) (acc : List (GoString × w64)) (cur : List w8),
        "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ R ∗ "ok" ∷ ok_ptr ↦ true ∗ "Hr" ∷ R ↦*{dq} cur ∗
        "Hback" ∷ (R ↦*{dq} cur -∗ b ↦*{dq} bs) ∗
        "Hm" ∷ ownMap mp (DFrac.own 1) (reqL acc) ∗
        "%Hi" ∷ ⌜acc.length = uint.nat i ∧ uint.nat i ≤ uint.nat x ∧
          decRQGo (uint.nat x - uint.nat i) acc cur = decRQGo (uint.nat x) [] rest⌝ : IProp GF)
        $$ [i r ok Hr Hback Hm]
    · iexists W64 0, r, [], rest
      simp only [show uint.nat (W64 0) = 0 from rfl, Nat.sub_zero]
      iframe
      ipureintro
      simp
    wp_for HI
    wp_if_destruct
    · have hi : uint.Z i < uint.Z x := by
        first | exact Hif | exact of_decide_eq_true (go.intoVal_inj Hif)
      have hk : uint.nat x - uint.nat i = (uint.nat x - uint.nat i - 1) + 1 := by word
      wp_apply wp_rpcDec_t5 R cur dq x_ptr _ _ $$ Hr x
      iintro %R1 %ok1 Hd1
      rcases hd1 : getTag cur with _ | ⟨key, cur1⟩
      · simp only [hd1]
        icases Hd1 with ⟨%Hok, Hx, Hr⟩
        subst Hok
        wp_auto
        have hres : decRQGo (uint.nat x) [] rest = none := by
          rw [← Hi.2.2, hk]; simp [decRQGo, hd1]
        ihave Hb := Hback $$ Hr
        rw [forPostcondition_unseal]; unfold forPostconditionDef; iright; iright; iright; ileft
        iexists #()
        isplitr
        · ipureintro; rfl
        dsimp only
        wp_auto
        iapply HΦ
        rw [hres]
        dsimp only
        iframe
        ipureintro; rfl
      simp only [hd1]
      icases Hd1 with ⟨%Hok, Hx, Hr1, Hback1⟩
      subst Hok
      wp_auto
      wp_apply wp_rpcDec_t6 R1 cur1 dq y_ptr _ _ $$ Hr1 y
      iintro %R2 %ok2 Hd2
      rcases hd2 : getU64 cur1 with _ | ⟨v, cur2⟩
      · simp only [hd2]
        icases Hd2 with ⟨%Hok, Hy, Hr1⟩
        subst Hok
        wp_auto
        have hres : decRQGo (uint.nat x) [] rest = none := by
          rw [← Hi.2.2, hk]; simp [decRQGo, hd1, hd2]
        ihave Hb := Hback $$ [Hback1 Hr1]
        · iapply Hback1 $$ Hr1
        rw [forPostcondition_unseal]; unfold forPostconditionDef; iright; iright; iright; ileft
        iexists #()
        isplitr
        · ipureintro; rfl
        dsimp only
        wp_auto
        iapply HΦ
        rw [hres]
        dsimp only
        iframe
        ipureintro; rfl
      simp only [hd2]
      icases Hd2 with ⟨%Hok, Hy, Hr2, Hback2⟩
      subst Hok
      wp_auto
      wp_apply wp_mapInsert go.string mp (reqL acc) key v $$ Hm as Hm
      (try wp_auto)
      wp_for_post
      ihave Hback2 := wand_trans _ _ _ $$ Hback2 Hback1
      ihave Hback := wand_trans _ _ _ $$ Hback2 Hback
      have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
      have hrl : reqL (acc ++ [(key, v)]) = <[key := v]> (reqL acc) := by
        simp [reqL, List.foldl_append]
      iframe
      iexists i + W64 1, R2, acc ++ [(key, v)], cur2
      rw [hrl]
      iframe
      ipureintro
      refine ⟨by rw [List.length_append, Hi.1, hi1]; rfl, by rw [hi1]; omega, ?_⟩
      rw [← Hi.2.2, hk, hi1, show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
      simp [decRQGo, hd1, hd2]
    · have hc : ¬ uint.Z i < uint.Z x := by
        first | exact Hif | exact fun h => Hif (by simp [h])
      (try (rw [decide_eq_false hc, if_pos (by simp)]))
      (try wp_auto)
      have hix : uint.nat x - uint.nat i = 0 := by
        word
      have hres : decRQGo (uint.nat x) [] rest = some (acc, cur) := by
        rw [← Hi.2.2, hix]; rfl
      iapply HΦ
      rw [hres]
      dsimp only
      iframe
      ipureintro; rfl

theorem foldIns_spec {V : Type} (es : List (GoString × V)) (hnd : (es.map Prod.fst).Nodup)
    (m0 : GMap GoString V) (k : GoString) (v : V) :
    (es.foldl (fun m e => <[e.1 := e.2]> m) m0) !! k = some v ↔
      ((k, v) ∈ es ∨ (k ∉ es.map Prod.fst ∧ m0 !! k = some v)) := by
  induction es generalizing m0 with
  | nil => simp
  | cons e es ih =>
    obtain ⟨k', v'⟩ := e
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rw [ih hnd.2]
    by_cases hk : k' = k
    · subst hk
      have : ∀ w, (k', w) ∉ es := fun w hw => hnd.1 (List.mem_map.2 ⟨_, hw, rfl⟩)
      simp [this, hnd.1, GMap.lookup_insert_eq_iff, eq_comm]
    · have hk' : k ≠ k' := fun h => hk h.symm
      simp [hk, hk', GMap.lookup_insert_eq_iff]

theorem reqL_eq (r : GMap GoString w64) (es : List (GoString × w64))
    (h : entriesOf r es) : reqL es = r := by
  rw [GMap.ext_iff']
  intro k
  have hs := foldIns_spec es h.1 ∅ k
  show (reqL es) !! k = r !! k
  rcases hr : r !! k with _ | v
  · rcases hl : (reqL es) !! k with _ | v
    · rfl
    · rcases (hs v).1 hl with h' | ⟨-, h'⟩
      · have := (h.2 k v).2 h'
        rw [show r.lookup k = r !! k from rfl, hr] at this; cases this
      · simp at h'
  · exact (hs v).2 (Or.inl ((h.2 k v).1 (by rw [show r.lookup k = r !! k from rfl, hr])))

theorem decRQGo_enc (es acc : List (GoString × w64)) (rest : List w8)
    (h : ∀ e ∈ es, e.1.length < 2 ^ 64) :
    decRQGo es.length acc ((es.map fun e => encStr e.1 ++ encU64 e.2).flatten ++ rest) =
      some (acc ++ es, rest) := by
  induction es generalizing acc with
  | nil => simp [decRQGo]
  | cons e es ih =>
    have he := h e (List.mem_cons_self ..)
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decRQGo,
      getTag_encStr' e.1 _ he, encU64, getU64_enc']
    have := ih (acc ++ [e]) (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    simp only [encU64] at this
    simp [this]

theorem decRQ_enc (es : List (GoString × w64)) (hb : (encPropReqL es).length < 2 ^ 63) :
    decRQ (encU64 (W64 es.length) ++ (es.map fun e => encStr e.1 ++ encU64 e.2).flatten) =
      some (es, []) := by
  unfold encPropReqL tagged at hb
  have hfl : (es.map fun e => encStr e.1 ++ encU64 e.2).flatten.length < 2 ^ 63 := by
    simp only [List.length_append] at hb; omega
  have hcnt : es.length ≤ (es.map fun e => encStr e.1 ++ encU64 e.2).flatten.length := by
    have := count_le_flatten (es.map fun e => encStr e.1 ++ encU64 e.2)
      (fun l hl => by
        obtain ⟨e, -, rfl⟩ := List.mem_map.1 hl
        intro h; have := congrArg List.length h; simp [encStr, u64Le_length] at this)
    simpa using this
  have h : ∀ e ∈ es, e.1.length < 2 ^ 64 := by
    intro e he
    have h1 := len_le_flatten _ _ (List.mem_map_of_mem (f := fun e => encStr e.1 ++ encU64 e.2) he)
    have h2 : e.1.length ≤ (encStr e.1 ++ encU64 e.2).length := by
      simp only [encStr, List.length_append]; omega
    omega
  unfold decRQ encU64
  rw [getU64_enc']
  have hn : uint.nat (W64 es.length) = es.length := by
    show (BitVec.ofNat 64 es.length).toNat = es.length
    simp only [BitVec.toNat_ofNat]; omega
  simp only [hn]
  rw [if_pos (by simpa [encU64] using hcnt)]
  have := decRQGo_enc es [] [] h
  simpa [encU64] using this

theorem decA_PropagateRequest : decA_PropagateRequest.spec (GF := GF) := by
  intro p args req Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  obtain ⟨es, hes, rfl⟩ := Hargs
  unfold craqCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have h3 : sint.Z data.len < 2 ^ 63 := by word
  have hd := decRQ_enc es (by omega)
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encPropReqL, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t4 r _ dq p $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, ⟨%mp, Hp, Hm⟩, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp Hm]
  · iapply HΨ
    simp only [ite_true]
    unfold reqPtr
    rw [reqL_eq req es hes]
    iexists mp
    iframe
  simp only [ite_true]
  ipureintro; trivial

/-! ## Encoding the replies -/

theorem wp_rpcEnc_t16 :
    encFn (GF := GF) examples.craqnet.rpcEnc_t16 #transport.netrpc.EmptyReply.mk
      (strct []) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := w8) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t20 (k : GoString) (v : w64) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t20 #(transport.netrpc.VersionResponse.mk k v)
      (strct [fStr k, fU64 v]) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := w8) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 k
    by_cases h1 : k = [] <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 k _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t6 v
    by_cases h2 : v = W64 0 <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t6 v _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t24 (k : GoString) (sl : GoSlice) (dq : DFrac) (x : List w8) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t24 #(transport.Item.mk k sl)
      (strct [fStr k, fBytes x]) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := w8) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t5 k
    by_cases h1 : k = [] <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t5 k _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t11 sl dq x $$ [$Hsl] as Hsl
    by_cases h2 : x = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t11 sl dq x _ _ $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, Hsl⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t10 (sl : GoSlice) (dq : DFrac) (x : List w8) (v : w64) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t10 #(transport.ValueVersion.mk sl v)
      (strct [fBytes x, fU64 v]) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  wp_apply wp_slice_literal (V := w8) _
  isplitr
  · ipureintro; rfl
  iintro %sl1 ⟨Hsl1, -⟩
  wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t11 sl dq x $$ [$Hsl] as Hsl
    by_cases h2 : x = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t11 sl dq x _ _ $$ [$Hb $Hcap $Hsl] as %b2 ⟨Hb, Hcap, Hsl⟩))
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t6 v
    by_cases h3 : v = W64 0 <;> simp only [h3, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true]
    )
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t6 v _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩))
    )
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t9 (sl : GoSlice) (xs : List (GoString × w64)) :
    encFn (GF := GF) examples.craqnet.rpcEnc_t9 #sl (encVVs xs) (vvsOwn sl xs) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hv⟩
  unfold vvsOwn
  icases Hv with ⟨%vvs, Hs, %Hver, HV⟩
  ihave %Hlen := ownSlice_len _ _ _ $$ Hs
  have hl : vvs.length = xs.length := by simpa using congrArg List.length Hver
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  (try wp_auto)
  have hsl : sl.len = W64 xs.length := by rw [← hl, Hlen.1]; word
  ihave HI : (∃ (j : Nat) (bb : GoSlice) (y : transport.ValueVersion),
      "i" ∷ i_ptr ↦ W64 j ∗ "b" ∷ b_ptr ↦ bb ∗ "x" ∷ x_ptr ↦ y ∗
      "Hb" ∷ bb ↦* (bs ++ u64Le sl.len ++
        ((xs.take j).map fun e => strct [fBytes e.1, fU64 e.2]).flatten) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗ "%Hj" ∷ ⌜j ≤ vvs.length⌝ : IProp GF)
      $$ [i b x Hb Hcap]
  · iexists 0, b1, _
    simp only [List.take_zero, List.map_nil, List.flatten_nil, List.append_nil]
    iframe
    ipureintro; omega
  wp_for HI
  by_cases hj : j < vvs.length
  · have hc : sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_true hc, ↓reduceIte]
    wp_auto
    have h0 : 0 ≤ sint.Z (W64 (j : Int)) := by word
    simp only [h0, hc, and_self, ↓reduceIte]
    have hsj : (sint.Z (W64 (j : Int))).toNat = j := by word
    obtain ⟨vv, hx⟩ : ∃ x, vvs[j]? = some x := ⟨_, List.getElem?_eq_getElem hj⟩
    wp_apply (wp_load_slice_index sl (sint.Z (W64 (j : Int))) vvs (DFrac.own 1) vv h0) $$ [Hs] as Hs
    · iframe; ipureintro; rw [hsj]; exact hx
    icases (BigSepL.bigSepL_lookup_acc hx).1 $$ HV with ⟨He, HVback⟩
    unfold vvElem
    icases He with ⟨%xv, %Hxv, #Hxs⟩
    rcases vv with ⟨vsl, vver⟩
    (try wp_auto)
    wp_apply wp_rpcEnc_t10 vsl _ xv vver _ _ $$ [$Hb $Hcap $Hxs] as %b2 ⟨Hb, Hcap, -⟩
    wp_for_post
    ihave HV := HVback $$ [Hxs]
    · iexists xv
      isplitr
      · ipureintro; exact Hxv
      iexact Hxs
    have hxj : xs[j]? = some (xv, vver) := by
      have h1 : (vvs.map (·.Version'))[j]? = some vver := by simp [hx]
      rw [Hver] at h1
      rcases hxs : xs[j]? with _ | ⟨a, c⟩
      · simp [hxs] at Hxv
      · simp [hxs] at Hxv h1
        rw [Hxv, h1]
    have hset : vvs.set j (transport.ValueVersion.mk vsl vver) = vvs := by
      apply List.ext_getElem?
      intro n
      rw [List.getElem?_set]
      by_cases hn : j = n
      · subst hn
        simp only [hj, ↓reduceIte, hx]
      · simp [hn]
    rw [hset]
    iframe
    iexists j + 1, b2, _
    have hw : W64 (j : Int) + W64 1 = W64 ((j + 1 : Nat) : Int) := by word
    rw [hw, List.take_add_one, hxj, Option.toList_some, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← List.append_assoc]
    iframe
    ipureintro; omega
  · have hc : ¬ sint.Z (W64 (j : Int)) < sint.Z sl.len := by word
    simp only [decide_eq_false hc, Bool.false_eq_true, ↓reduceIte]
    have hjl : j = xs.length := by omega
    subst hjl
    (try wp_auto)
    iapply HΦ
    rw [List.take_length] at *
    unfold encVVs encU64
    rw [← hsl, List.append_assoc]
    iframe
    ipureintro; exact Hver

/-- A response map's value at `k` (`[]` if absent). -/
abbrev respAt (resp : GMap GoString (List (GoString × w64))) (k : GoString) : List (GoString × w64) :=
  (resp.lookup k).getD []

theorem wp_rpcEnc_t8 (mp : Loc) (m : GMap GoString GoSlice)
    (resp : GMap GoString (List (GoString × w64))) (b : GoSlice) (bs : List w8) :
    {{ (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) ∗ ownMap mp (DFrac.own 1) m ∗
        ([∗map] k ↦ sl ∈ m, vvsOwn sl (respAt resp k)) : IProp GF) }}
      (App (App (Val (@! examples.craqnet.rpcEnc_t8)) (Val #b)) (Val #mp))
    {{ (b' : GoSlice), RET #b'; ∃ keys : List GoString,
        ⌜keys.Nodup ∧ ∀ k, k ∈ keys ↔ (m !! k).isSome⌝ ∗
        b' ↦* (bs ++ encU64 (W64 keys.length) ++
          (keys.map fun k => encStr k ++ encVVs (respAt resp k)).flatten) ∗
        ownSliceCap w8 b' (DFrac.own 1) ∗ ownMap mp (DFrac.own 1) m ∗
        ([∗map] k ↦ sl ∈ m, vvsOwn sl (respAt resp k)) }} := by
  wp_start as ⟨Hb, Hcap, Hm, HM⟩
  wp_auto
  wp_apply wp_map_len_lt mp m (DFrac.own 1) $$ [$Hm] as ⟨Hm, %Hsz⟩
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  wp_func_lits
  wp_bind (App (App (Val (map.forRange _ _)) _) _)
  iapply (wp_map_for_range (K := GoString) (V := GoSlice) (fun keys (i : Int) => iprop(
      ⌜0 ≤ i⌝ ∗ ∃ (bb : GoSlice) (xs : GoString) (ys : GoSlice), b_ptr ↦ bb ∗ x_ptr ↦ xs ∗ y_ptr ↦ ys ∗
        bb ↦* (bs ++ u64Le (W64 (GMap.size m)) ++
          ((keys.take i.toNat).map fun k => encStr k ++ encVVs (respAt resp k)).flatten) ∗
        ownSliceCap w8 bb (DFrac.own 1) ∗
        ([∗map] k ↦ sl ∈ m, vvsOwn sl (respAt resp k))))) $$ Hm
  iintro %keys %hkeys
  isplitl [b x y Hb Hcap HM]
  · isplitr
    · ipureintro; omega
    iexists b1, _, _
    simp only [Int.toNat_zero, List.take_zero, List.map_nil, List.flatten_nil, List.append_nil]
    iframe
  isplitl []
  · imodintro
    iintro %i %key %v ⟨%hk1, %hk2⟩ ⟨%hi, %bb, %xs, %ys, Hbp, Hx, Hy, Hb, Hcap, HM⟩
    icases (BigSepM.bigSepM_lookup_acc (Φ := fun k sl => vvsOwn (GF := GF) sl (respAt resp k))
      (m := m) (i := key) (x := v) hk2).1 $$ HM with ⟨Hv, HMback⟩
    wp_auto
    wp_apply wp_rpcEnc_t5 key _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩
    wp_apply wp_rpcEnc_t9 v (respAt resp key) _ _ $$ [$Hb $Hcap $Hv] as %b3 ⟨Hb, Hcap, Hv⟩
    unfold forMapPostcondition
    iright; ileft
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; omega
    iexists b3, key, v
    ihave HM := HMback $$ Hv
    rw [show (i + 1).toNat = i.toNat + 1 by omega, List.take_add_one, hk1]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil,
      List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← List.append_assoc]
    iframe
  · iintro ⟨%h0, %bb, %xs, %ys, Hbp, Hx, Hy, Hb, Hcap, HM⟩ Hm
    wp_auto
    iapply HΦ
    iexists keys
    rw [← hkeys.2.1, List.take_of_length_le (by omega)]
    unfold encU64
    iframe
    ipureintro
    exact ⟨hkeys.2.2, hkeys.1⟩

theorem enc_EmptyReply : enc_EmptyReply.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t16 _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encEmptyReply, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_VersionResponse : enc_VersionResponse.spec (GF := GF) := by
  intro p dq k v Ψ
  iintro ⟨Hp, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t20 k v _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encVersionResp, tagged] at HΨ
  iapply HΨ $$ Hp

theorem enc_Item : enc_Item.spec (GF := GF) := by
  intro p dq k sl dqs x Ψ
  iintro ⟨Hp, Hsl, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t24 k sl dqs x _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encItem, tagged] at HΨ
  iapply HΨ $$ Hp Hsl

theorem enc_PropagateResponse : enc_PropagateResponse.spec (GF := GF) := by
  intro p resp Ψ
  unfold respPtr
  iintro ⟨⟨%mp, %m, Hp, Hm, %Hdom, HM⟩, HΨ⟩
  unfold craqCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  ihave HM : ([∗map] k ↦ sl ∈ m, vvsOwn sl (respAt resp k)) $$ [HM]
  · unfold vvsOwn vvElem respAt; iexact HM
  wp_apply wp_rpcEnc_t8 mp m resp $$ [$Hb $Hcap $Hm $HM] as %b' ⟨%keys, %Hkeys, Hb, Hcap, Hm, HM⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  iapply HΨ $$ [Hp Hm HM]
  · iexists mp, m
    unfold vvsOwn vvElem respAt
    iframe
    ipureintro; exact Hdom
  ipureintro
  refine ⟨keys.map fun k => (k, respAt resp k), ⟨?_, ?_⟩, ?_⟩
  · rw [List.map_map, show (Prod.fst ∘ fun k => (k, respAt resp k)) = id from rfl, List.map_id]
    exact Hkeys.1
  · intro k v
    have hk : k ∈ keys ↔ (resp.lookup k).isSome := by
      rw [Hkeys.2 k, ← Hdom k]
    constructor
    · intro h
      refine List.mem_map.2 ⟨k, hk.2 (by simp [h]), by simp [respAt, h]⟩
    · intro h
      obtain ⟨k', hk', he⟩ := List.mem_map.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have := hk.1 hk'
      rcases h' : resp.lookup k' with _ | w
      · simp [h'] at this
      · simp [respAt, h']
  · simp only [encPropRespL, tagged, encU64, List.length_map, List.map_map, List.append_assoc]
    rfl

/-- The server side's codec lemmas (H5, the bindings), proved. -/
theorem craqSrvCodecLaws : SrvCodecLaws (GF := GF) where
  decA_EmptyArgs := decA_EmptyArgs
  decA_string := decA_string
  decA_NodeMeta := decA_NodeMeta
  decA_CommitArgs := decA_CommitArgs
  decA_WriteArgs := decA_WriteArgs
  decA_ClientWriteArgs := decA_ClientWriteArgs
  decA_PropagateRequest := decA_PropagateRequest
  enc_EmptyReply := enc_EmptyReply
  enc_VersionResponse := enc_VersionResponse
  enc_Item := enc_Item
  enc_NodeMeta := enc_NodeMeta
  enc_PropagateResponse := enc_PropagateResponse

/-! ## Injectivity of the argument encodings, and the length bound from a decoding -/

theorem tagged_inj {t b b' : List w8} (h : tagged t b = tagged t b') : b = b' :=
  List.append_cancel_left h

theorem encString_inj (s s' : GoString) : encString s = encString s' → s = s' := by
  intro h
  have hl := congrArg List.length h
  simp only [encString, tagged, encStr, List.length_append, u64Le_length] at hl
  have hl' : s.length = s'.length := by omega
  unfold encString tagged encStr at h
  rw [hl'] at h
  simp only [← List.append_assoc] at h
  exact List.append_cancel_left h

theorem encMeta_inj (m m' : MetaV) : (encMeta m).length < 2 ^ 63 → encMeta m = encMeta m' → m = m' := by
  intro hl h
  have hl' : (encMeta m').length < 2 ^ 63 := h ▸ hl
  have bnd : ∀ m : MetaV, (encMeta m).length < 2 ^ 63 →
      decMetaV ⟨false, false, go!"", go!"", go!""⟩
        (strct [fBool m.isHead, fBool m.isTail, fStr m.prev, fStr m.next, fStr m.tail]) = some (m, []) := by
    intro m hl
    have b : ∀ s, (fStr s).length ≤ (encMeta m).length → s.length < 2 ^ 64 := by
      intro s h2; have h1 := len_fStr s; omega
    exact decMetaV_enc m (b _ (by simp [encMeta, tagged, strct]; omega))
      (b _ (by simp [encMeta, tagged, strct]; omega)) (b _ (by simp [encMeta, tagged, strct]; omega))
  have hb := tagged_inj h
  have e1 := bnd m hl
  rw [hb, bnd m' hl'] at e1
  cases e1; rfl

theorem encCommitArgs_inj (k k' : GoString) (v v' : w64) :
    (encCommitArgs k v).length < 2 ^ 63 → encCommitArgs k v = encCommitArgs k' v' → k = k' ∧ v = v' := by
  intro hl h
  have hl' : (encCommitArgs k' v').length < 2 ^ 63 := h ▸ hl
  have bnd : ∀ k v, (encCommitArgs k v).length < 2 ^ 63 → k.length < 2 ^ 64 := by
    intro k v hl
    have h1 := len_fStr k
    have h2 : (fStr k).length ≤ (encCommitArgs k v).length := by
      simp [encCommitArgs, tagged, strct]; omega
    omega
  have e1 := decVR_enc k v (bnd k v hl)
  rw [tagged_inj h, decVR_enc k' v' (bnd k' v' hl')] at e1
  cases e1; exact ⟨rfl, rfl⟩

theorem encClientWriteArgs_inj (k k' x x' : GoString) :
    (encClientWriteArgs k x).length < 2 ^ 63 → encClientWriteArgs k x = encClientWriteArgs k' x' →
      k = k' ∧ x = x' := by
  intro hl h
  have hl' : (encClientWriteArgs k' x').length < 2 ^ 63 := h ▸ hl
  have bnd : ∀ k x, (encClientWriteArgs k x).length < 2 ^ 63 →
      k.length < 2 ^ 64 ∧ x.length < 2 ^ 64 := by
    intro k x hl
    have h1 := len_fStr k
    have h2 : (fStr k).length ≤ (encClientWriteArgs k x).length := by
      simp [encClientWriteArgs, tagged, strct]; omega
    have h3 := len_fBytes x
    have h4 : (fBytes x).length ≤ (encClientWriteArgs k x).length := by
      simp [encClientWriteArgs, tagged, strct]; omega
    omega
  have e1 := decItem_enc k x (bnd k x hl).1 (bnd k x hl).2
  rw [tagged_inj h, decItem_enc k' x' (bnd k' x' hl').1 (bnd k' x' hl').2] at e1
  cases e1; exact ⟨rfl, rfl⟩

theorem encWriteArgs_inj (k k' x x' : GoString) (v v' : w64) :
    (encWriteArgs k x v).length < 2 ^ 63 → encWriteArgs k x v = encWriteArgs k' x' v' →
      k = k' ∧ x = x' ∧ v = v' := by
  intro hl h
  have hl' : (encWriteArgs k' x' v').length < 2 ^ 63 := h ▸ hl
  have bnd : ∀ k x v, (encWriteArgs k x v).length < 2 ^ 63 →
      k.length < 2 ^ 64 ∧ x.length < 2 ^ 64 := by
    intro k x v hl
    have h1 := len_fStr k
    have h2 : (fStr k).length ≤ (encWriteArgs k x v).length := by
      simp [encWriteArgs, tagged, strct]; omega
    have h3 := len_fBytes x
    have h4 : (fBytes x).length ≤ (encWriteArgs k x v).length := by
      simp [encWriteArgs, tagged, strct]; omega
    omega
  have e1 := decWA_enc k x v (bnd k x v hl).1 (bnd k x v hl).2
  rw [tagged_inj h, decWA_enc k' x' v' (bnd k' x' v' hl').1 (bnd k' x' v' hl').2] at e1
  cases e1; exact ⟨rfl, rfl, rfl⟩

theorem encPropReq_inj (req req' : GMap GoString w64) (bs : List w8) :
    bs.length < 2 ^ 63 → encPropReq req bs → encPropReq req' bs → req = req' := by
  rintro hl ⟨es, hes, rfl⟩ ⟨es', hes', h⟩
  have hl' : (encPropReqL es').length < 2 ^ 63 := h ▸ hl
  have e1 := decRQ_enc es hl
  unfold encPropReqL at h
  rw [tagged_inj h, decRQ_enc es' hl'] at e1
  cases e1
  rw [← reqL_eq req es hes, ← reqL_eq req' es hes']

/-- A decoding's bytes are in a slice: their length is below `2^63`. -/
theorem dec_len (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF) :
    (⌜bs.length < 2 ^ 63⌝ -∗ craqCodec.dec bs ptr Ψ) ⊢
      craqCodec.dec bs ptr (fun ok => iprop(⌜bs.length < 2 ^ 63⌝ ∗ Ψ ok)) := by
  unfold craqCodec
  iintro H %data %dq %Φ Hd HΦ
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have hb : bs.length < 2 ^ 63 := by have : sint.Z data.len < 2 ^ 63 := by word
                                     omega
  iapply H $$ %hb Hd
  iintro !> %err %ok Hd %Herr HΨ Hif
  iapply HΦ $$ Hd %Herr [HΨ] Hif
  dsimp only
  iframe
  ipureintro; exact hb

end proof

end github_com.despreston.go_craq
end Perennial
