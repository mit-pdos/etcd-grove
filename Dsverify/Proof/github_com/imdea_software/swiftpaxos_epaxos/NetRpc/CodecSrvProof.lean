/-
The kit's generated codec, server side (`NetRpc/CodecSrv.lean`'s `SrvCodecLaws`), proved
(`epSrvCodecLaws`): decoding an encoding of a request argument into the fresh value `NewArg()`
allocates gives back exactly the encoded value, and the replies' encoders give `Wire.lean`'s
bytes; with the argument encodings' injectivity (`epArgFacts`) and a decoding's length bound
(`epDecLen`). As dsv-craq's `Craq/CodecSrvProof.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.CodecSrv
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos_epaxos.NetRpc.CodecProof

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.mit_pdos.perennial.goose.model.strings (wp_string_len)
open github_com.imdea_software.swiftpaxos_epaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos_epaxos


/-! ## Pure facts -/

theorem getTag_tagged (t body : List w8) (ht : t.length < 2 ^ 64) :
    getTag (tagged t body) = some (t, body) := by
  unfold tagged; exact getTag_encStr' _ _ ht

theorem len_fStr (k : GoString) : k.length ≤ (fStr k).length := by
  by_cases hk : k = []
  · simp [hk]
  · simp [fStr, fld, hk, encStr]; omega

theorem decFld_fStr (k rest : List w8) (hk : k.length < 2 ^ 64) :
    decFld getTag go!"" (fStr k ++ rest) = some (k, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact getTag_encStr' k rest hk

/-- The pure `rpcDec_t18` (`RegisterArgs`), into `{a0, p0}`. -/
def decRA (a0 : GoString) (p0 : w64) (bs : List w8) : Option ((GoString × w64) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getTag a0 r with
    | none => none
    | some (a, r) =>
      match decFld getU64 p0 r with
      | none => none
      | some (v, r) => some ((a, v), r)

theorem decRA_enc (a : GoString) (v : w64) (ha : a.length < 2 ^ 64) :
    decRA go!"" (W64 0) (strct [fStr a, fInt v]) = some ((a, v), []) := by
  have e : strct [fStr a, fInt v] = W8 1 :: (fStr a ++ (fInt v ++ [])) := by
    simp [strct]
  rw [e]
  simp only [decRA, decHdr, ↓reduceIte, decFld_fStr a _ ha, decFld_fInt]

/-- The pure `rpcDec_t66` (`uint8`). -/
def decU8 (bs : List w8) : Option (w8 × List w8) :=
  match getU64 bs with
  | none => none
  | some (x, r) => if uint.Z x < 256 then some (W8 (uint.Z x), r) else none

theorem decU8_enc (c : w8) (rest : List w8) : decU8 (encU8 c ++ rest) = some (c, rest) := by
  unfold decU8 encU8
  rw [getU64_enc']
  have h1 : uint.Z (W64 (uint.Z c)) < 256 := by word
  have h2 : W8 (uint.Z (W64 (uint.Z c))) = c := by word
  simp only [h1, ↓reduceIte, h2]

theorem decFld_fU8 (a : w8) (rest : List w8) :
    decFld decU8 (W8 0) (fU8 a ++ rest) = some (a, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decU8_enc a rest

/-- The pure `rpcDec_t88` (`PingArgs`), into `{a0}`. -/
def decPA (a0 : w8) (bs : List w8) : Option (w8 × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld decU8 a0 r with
    | none => none
    | some (a, r) => some (a, r)

theorem decPA_enc (a : w8) : decPA (W8 0) (strct [fU8 a]) = some (a, []) := by
  have e : strct [fU8 a] = W8 1 :: (fU8 a ++ []) := by simp [strct]
  rw [e]
  simp only [decPA, decHdr, ↓reduceIte, decFld_fU8]


section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [examples.epaxosnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

/-! ## Decoding the arguments -/

theorem wp_rpcDec_t6 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t6)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem wp_rpcDec_t10 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t10)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem wp_rpcDec_t84 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decHdr bs with
          | some rest => ⌜ok = true⌝ ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t84)) (Val #b)) (Val #p)) {{ Φ }} := by
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

theorem decA_GetLeaderArgs : decA_GetLeaderArgs.spec (GF := GF) := by
  intro p args Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold epCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encGetLeaderArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t6 r _ dq p $$ Hr
  iintro %r2 %ok2 H2
  simp only [show decHdr (strct []) = some [] from rfl]
  icases H2 with ⟨%Hok, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial

theorem decA_GetReplicaListArgs : decA_GetReplicaListArgs.spec (GF := GF) := by
  intro p args Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold epCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encGetReplicaListArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t10 r _ dq p $$ Hr
  iintro %r2 %ok2 H2
  simp only [show decHdr (strct []) = some [] from rfl]
  icases H2 with ⟨%Hok, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial

theorem decA_BtlArgs : decA_BtlArgs.spec (GF := GF) := by
  intro p args Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold epCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encBtlArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t84 r _ dq p $$ Hr
  iintro %r2 %ok2 H2
  simp only [show decHdr (strct []) = some [] from rfl]
  icases H2 with ⟨%Hok, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ $$ Hp
  simp only [ite_true]
  ipureintro; trivial


theorem wp_rpcDec_t18 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (a0 : GoString) (p0 : w64)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ replica.defs.RegisterArgs.mk a0 p0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decRA a0 p0 bs with
          | some ((a, v), rest) => ⌜ok = true⌝ ∗ p ↦ replica.defs.RegisterArgs.mk a v ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ a v, p ↦ replica.defs.RegisterArgs.mk a v) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t18)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step decRA
  all_goals fld_step wp_rpcDec_t14 getTag Addr fail struct_close decRA
  all_goals fld_step wp_rpcDec_t4 getU64 Port fail struct_close decRA
  all_goals ((try wp_auto); struct_close decRA)

theorem decA_RegisterArgs : decA_RegisterArgs.spec (GF := GF) := by
  intro p args a v Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold epCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have ha : a.length < 2 ^ 64 := by
    have h3 : sint.Z data.len < 2 ^ 63 := by word
    have h1 := len_fStr a
    have h2 : (fStr a).length ≤ (encRegisterArgs a v).length := by
      simp [encRegisterArgs, tagged, strct]; omega
    omega
  have hd := decRA_enc a v ha
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encRegisterArgs, getTag_tagged]
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

theorem wp_rpcDec_t66 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (v0 : w8)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ v0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decU8 bs with
          | some (v, rest) => ⌜ok = true⌝ ∗ p ↦ v ∗ r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ p ↦ v0 ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t66)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decU8
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
    wp_auto
    by_cases hx : uint.Z x < 256
    · rw [decide_eq_true (show W64 (uint.Z (W8 (uint.Z x))) = x by word)]
      wp_auto
      iapply HΦ
      rw [if_pos hx]
      dsimp only
      iframe
      ipureintro; rfl
    · rw [decide_eq_false (show ¬ W64 (uint.Z (W8 (uint.Z x))) = x by
        intro h; apply hx; rw [← h]; word)]
      wp_auto
      iapply HΦ
      rw [if_neg hx]
      dsimp only
      iframe
      isplitr
      · ipureintro; rfl
      iapply Hback $$ Hr


set_option hygiene false in
/-- Close a `PingArgs` decoder's proof. -/
macro "pa_close " D:ident : tactic => `(tactic| (
  iapply HΦ
  simp only [$D:ident, decHdr, decFld, ↓reduceIte, *]
  iframe
  first
  | (iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)))

theorem wp_rpcDec_t88 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc) (a0 : w8)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ replica.defs.PingArgs.mk a0 -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decPA a0 bs with
          | some (a, rest) => ⌜ok = true⌝ ∗ p ↦ replica.defs.PingArgs.mk a ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ a, p ↦ replica.defs.PingArgs.mk a) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.epaxosnet.rpcDec_t88)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step_with decPA (pa_close decPA)
  all_goals fld_step wp_rpcDec_t66 decU8 ActAsLeader fail pa_close decPA
  all_goals ((try wp_auto); pa_close decPA)

theorem decA_PingArgs : decA_PingArgs.spec (GF := GF) := by
  intro p args a Ψ
  iintro ⟨%Hargs, Hp, HΨ⟩
  subst Hargs
  unfold epCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  have hd := decPA_enc a
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data _ dq $$ Hd
  iintro %t %r %ok H
  simp (disch := decide) only [encPingArgs, getTag_tagged]
  icases H with ⟨%Hok, Hr, Hback⟩
  obtain ⟨rfl, rfl⟩ := Hok
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcDec_t88 r _ dq p _ $$ Hr Hp
  iintro %r2 %ok2 H2
  simp only [hd]
  icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
  subst Hok
  dec_ok
  iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
  · iapply HΨ; simp only [ite_true]; iexact Hp
  simp only [ite_true]
  ipureintro; trivial

/-! ## Encoding the replies -/

theorem wp_rpcEnc_t26 (x : w32) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t26 #x (encI32 x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  iapply HΦ
  iframe

theorem wp_rpcSent_t26 (x : w32) :
    {{ (True : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcSent_t26)) (Val #x))
    {{ RET #(decide (x ≠ W32 0)); True }} := by
  wp_start
  wp_auto
  rw [show (!decide (x = W32 0)) = decide (x ≠ W32 0) by simp]
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcEnc_t16 (x : Bool) : encFn (GF := GF) examples.epaxosnet.rpcEnc_t16 #x (encBool x) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  wp_auto
  cases x
  · wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 0]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iframe
  · wp_auto
    wp_apply wp_slice_literal (V := w8) [W8 1]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    iapply HΦ
    iframe

theorem wp_rpcSent_t16 (x : Bool) :
    {{ (True : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcSent_t16)) (Val #x))
    {{ RET #x; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  ipureintro; trivial

theorem wp_rpcSent_t13 (sl : GoSlice) (dq : DFrac) (x : List GoString) :
    {{ (sl ↦*{dq} x : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcSent_t13)) (Val #sl))
    {{ RET #(decide (x ≠ [])); sl ↦*{dq} x }} := by
  wp_start as Hsl
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have h : (!decide (sl.len = W64 0)) = decide (x ≠ []) := by
    by_cases hx : x = []
    · subst hx
      have : sl.len = W64 0 := by simp at Hl; word
      simp [this]
    · have : x.length ≠ 0 := by simpa using hx
      have : sl.len ≠ W64 0 := by
        intro h0; rw [h0] at Hl; exact absurd (Hl.1.trans (by rfl)) this
      simp only [hx, this, decide_false, decide_true, Bool.not_false, ne_eq, not_false_eq_true]
  rw [h]
  iapply HΦ $$ Hsl

theorem wp_rpcEnc_t13 (sl : GoSlice) (dq : DFrac) (x : List GoString) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t13 #sl (encStrs x) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  have hlen : sl.len = W64 x.length := by rw [Hl.1]; word
  ihave HI : (∃ (i : w64) (bb : GoSlice) (y : GoString),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "x" ∷ x_ptr ↦ y ∗
      "Hb" ∷ bb ↦* (bs ++ u64Le sl.len ++
        ((x.take (sint.nat i)).map encStr).flatten) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i b x Hb Hcap]
  · iexists W64 0, b1, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.flatten_nil,
      List.append_nil]
    iframe
    ipureintro
    exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hi : sint.Z i < sint.Z sl.len := Hif
    list_elem x (sint.nat i) as e
    rw [ite_eq_left ⟨Hi.1, hi⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) x dq e Hi.1 $$ [Hsl] with Hsl
    · iframe; ipureintro; exact He_lookup
    wp_apply wp_rpcEnc_t14 e _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, b2, e
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
      List.take_add_one, He_lookup, Option.toList_some, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← List.append_assoc]
    iframe
    ipureintro; word
  · have hn : sint.nat i = x.length := by rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    iframe Hsl Hcap
    unfold encStrs
    rw [← hlen, List.append_assoc,
      show (x.map encStr).flatten =
        ((x.take (sint.nat i)).map encStr).flatten by
        rw [hn, List.take_length]]
    iexact Hb

theorem wp_rpcSent_t15 (sl : GoSlice) (dq : DFrac) (x : List Bool) :
    {{ (sl ↦*{dq} x : IProp GF) }} (App (Val (@! examples.epaxosnet.rpcSent_t15)) (Val #sl))
    {{ RET #(decide (x ≠ [])); sl ↦*{dq} x }} := by
  wp_start as Hsl
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  have h : (!decide (sl.len = W64 0)) = decide (x ≠ []) := by
    by_cases hx : x = []
    · subst hx
      have : sl.len = W64 0 := by simp at Hl; word
      simp [this]
    · have : x.length ≠ 0 := by simpa using hx
      have : sl.len ≠ W64 0 := by
        intro h0; rw [h0] at Hl; exact absurd (Hl.1.trans (by rfl)) this
      simp only [hx, this, decide_false, decide_true, Bool.not_false, ne_eq, not_false_eq_true]
  rw [h]
  iapply HΦ $$ Hsl

theorem wp_rpcEnc_t15 (sl : GoSlice) (dq : DFrac) (x : List Bool) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t15 #sl (encBools x) iprop(sl ↦*{dq} x) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, Hsl⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  wp_auto
  wp_apply wp_rpcPutU64 $$ [$Hb $Hcap] as %b1 ⟨Hb, Hcap⟩
  have hlen : sl.len = W64 x.length := by rw [Hl.1]; word
  ihave HI : (∃ (i : w64) (bb : GoSlice) (y : Bool),
      "i" ∷ i_ptr ↦ i ∗ "b" ∷ b_ptr ↦ bb ∗ "x" ∷ x_ptr ↦ y ∗
      "Hb" ∷ bb ↦* (bs ++ u64Le sl.len ++
        ((x.take (sint.nat i)).map encBool).flatten) ∗
      "Hcap" ∷ ownSliceCap w8 bb (DFrac.own 1) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z sl.len⌝ : IProp GF) $$ [i b x Hb Hcap]
  · iexists W64 0, b1, _
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.flatten_nil,
      List.append_nil]
    iframe
    ipureintro
    exact ⟨by decide, Hl.2⟩
  wp_for HI
  wp_if_destruct
  · have hi : sint.Z i < sint.Z sl.len := Hif
    list_elem x (sint.nat i) as e
    rw [ite_eq_left ⟨Hi.1, hi⟩]
    wp_apply wp_load_slice_index sl (sint.Z i) x dq e Hi.1 $$ [Hsl] with Hsl
    · iframe; ipureintro; exact He_lookup
    wp_apply wp_rpcEnc_t16 e _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩
    wp_for_post
    iframe
    iexists i + W64 1, b2, e
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word,
      List.take_add_one, He_lookup, Option.toList_some, List.map_append, List.flatten_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil,
      ← List.append_assoc]
    iframe
    ipureintro; word
  · have hn : sint.nat i = x.length := by rw [Hl.1]; word
    (try wp_auto)
    iapply HΦ
    iframe Hsl Hcap
    unfold encBools
    rw [← hlen, List.append_assoc,
      show (x.map encBool).flatten =
        ((x.take (sint.nat i)).map encBool).flatten by
        rw [hn, List.take_length]]
    iexact Hb

theorem wp_rpcEnc_t20 (id : w64) (sl : GoSlice) (dqs : DFrac) (nl : List GoString) (r il : Bool) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t20 #(replica.defs.RegisterReply.mk id sl r il)
      (strct [fInt id, fStrs nl, fBool r, fBool il]) iprop(sl ↦*{dqs} nl) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, HR⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
  )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t4 id
    by_cases h1 : id = W64 0 <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t4 id _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t13 sl dqs nl $$ [$HR] as HR
    by_cases h2 : nl = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t13 sl dqs nl _ _ $$ [$Hb $Hcap $HR] as %b2 ⟨Hb, Hcap, HR⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t16 r
    cases h3 : r)
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t16 _ _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t16 il
    cases h4 : il)
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t16 _ _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t8 (id : w64) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t8 #(replica.defs.GetLeaderReply.mk id)
      (strct [fInt id]) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
  )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t4 id
    by_cases h1 : id = W64 0 <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t4 id _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t12 (sr sa : GoSlice) (dqr dqa : DFrac) (rl : List GoString) (al : List Bool) (r : Bool) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t12 #(replica.defs.GetReplicaListReply.mk sr sa r)
      (strct [fStrs rl, fBools al, fBool r]) iprop(sr ↦*{dqr} rl ∗ sa ↦*{dqa} al) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, HR1, HR2⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
  )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t13 sr dqr rl $$ [$HR1] as HR1
    by_cases h1 : rl = [] <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t13 sr dqr rl _ _ $$ [$Hb $Hcap $HR1] as %b2 ⟨Hb, Hcap, HR1⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t15 sa dqa al $$ [$HR2] as HR2
    by_cases h2 : al = [] <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t15 sa dqa al _ _ $$ [$Hb $Hcap $HR2] as %b2 ⟨Hb, Hcap, HR2⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t16 r
    cases h3 : r)
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t16 _ _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t86 (l nl : w32) :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t86 #(replica.defs.BeTheLeaderReply.mk l nl)
      (strct [fI32 l, fI32 nl]) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
  )
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t26 l
    by_cases h1 : l = W32 0 <;> simp only [h1, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t26 l _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    wp_apply wp_rpcSent_t26 nl
    by_cases h2 : nl = W32 0 <;> simp only [h2, ne_eq, not_true_eq_false, not_false_eq_true, decide_false, decide_true])
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
    (try (wp_apply wp_rpcEnc_t26 nl _ _ $$ [$Hb $Hcap] as %b2 ⟨Hb, Hcap, -⟩)))
  all_goals (
    (try wp_auto)
    enc_close)

theorem wp_rpcEnc_t90 :
    encFn (GF := GF) examples.epaxosnet.rpcEnc_t90 #(replica.defs.PingReply.mk)
      (strct []) iprop(True) := by
  intro b bs
  wp_start as ⟨Hb, Hcap, -⟩
  all_goals (
    (try wp_auto)
    wp_apply wp_slice_literal (V := w8) _
    isplitr
    · ipureintro; rfl
    iintro %sl1 ⟨Hsl1, -⟩
    wp_apply wp_slice_append $$ [$Hb $Hcap $Hsl1] as %b' ⟨Hb, Hcap, -⟩
    (try wp_auto)
  )
  all_goals (
    (try wp_auto)
    enc_close)

theorem enc_RegisterReply : enc_RegisterReply.spec (GF := GF) := by
  intro p dq id sl dqs nl r il Ψ
  iintro ⟨Hp, Hsl, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t20 id sl dqs nl r il _ _ $$ [$Hb $Hcap $Hsl] as %b' ⟨Hb, Hcap, Hsl⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encRegisterReply, tagged, tRegisterReply] at HΨ
  iapply HΨ $$ Hp Hsl

theorem enc_GetLeaderReply : enc_GetLeaderReply.spec (GF := GF) := by
  intro p dq id Ψ
  iintro ⟨Hp, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t8 id _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encGetLeaderReply, tagged, tGetLeaderReply] at HΨ
  iapply HΨ $$ Hp

theorem enc_GetReplicaListReply : enc_GetReplicaListReply.spec (GF := GF) := by
  intro p dq sr sa dqr dqa rl al r Ψ
  iintro ⟨Hp, Hr, Ha, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t12 sr sa dqr dqa rl al r _ _ $$ [$Hb $Hcap $Hr $Ha] as %b' ⟨Hb, Hcap, Hr, Ha⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encGetReplicaListReply, tagged, tGetReplicaListReply] at HΨ
  iapply HΨ $$ Hp Hr Ha

theorem enc_BtlReply : enc_BtlReply.spec (GF := GF) := by
  intro p dq l nl Ψ
  iintro ⟨Hp, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t86 l nl _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encBtlReply, tagged, tBeTheLeaderReply] at HΨ
  iapply HΨ $$ Hp

theorem enc_PingReply : enc_PingReply.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold epCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t90 _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encPingReply, tagged, tPingReply] at HΨ
  iapply HΨ $$ Hp

/-- The server side's codec lemmas, proved. -/
theorem epSrvCodecLaws : SrvCodecLaws (GF := GF) where
  decA_RegisterArgs := decA_RegisterArgs
  decA_GetLeaderArgs := decA_GetLeaderArgs
  decA_GetReplicaListArgs := decA_GetReplicaListArgs
  decA_BtlArgs := decA_BtlArgs
  decA_PingArgs := decA_PingArgs
  enc_RegisterReply := enc_RegisterReply
  enc_GetLeaderReply := enc_GetLeaderReply
  enc_GetReplicaListReply := enc_GetReplicaListReply
  enc_BtlReply := enc_BtlReply
  enc_PingReply := enc_PingReply

/-- A decoding's bytes are in a slice: their length is below `2^63`. -/
theorem epDecLen : decLen.spec (GF := GF) := by
  intro bs ptr Ψ
  unfold epCodec
  iintro H %data %dq %Φ Hd HΦ
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  have hb : bs.length < 2 ^ 63 := by
    have : sint.Z data.len < 2 ^ 63 := by word
    omega
  iapply H $$ %hb Hd
  iintro !> %err %ok Hd %Herr HΨ Hif
  iapply HΦ $$ Hd %Herr [HΨ] Hif
  dsimp only
  iframe
  ipureintro; exact hb

end proof

/-! ## Injectivity of the argument encodings -/

theorem tagged_inj {t b b' : List w8} (h : tagged t b = tagged t b') : b = b' :=
  List.append_cancel_left h

theorem encRegisterArgs_inj' (a a' : GoString) (p p' : w64) :
    (encRegisterArgs a p).length < 2 ^ 63 →
    encRegisterArgs a p = encRegisterArgs a' p' → a = a' ∧ p = p' := by
  intro hl h
  have hl' : (encRegisterArgs a' p').length < 2 ^ 63 := h ▸ hl
  have bnd : ∀ a p, (encRegisterArgs a p).length < 2 ^ 63 → a.length < 2 ^ 64 := by
    intro a p hl
    have h1 := len_fStr a
    have h2 : (fStr a).length ≤ (encRegisterArgs a p).length := by
      simp [encRegisterArgs, tagged, strct]; omega
    omega
  have e1 := decRA_enc a p (bnd a p hl)
  rw [tagged_inj h, decRA_enc a' p' (bnd a' p' hl')] at e1
  cases e1; exact ⟨rfl, rfl⟩

theorem encPingArgs_inj' (x x' : w8) : encPingArgs x = encPingArgs x' → x = x' := by
  intro h
  have e1 := decPA_enc x
  rw [tagged_inj h, decPA_enc x'] at e1
  cases e1; rfl

/-- The argument encodings are injective. -/
theorem epArgFacts : ArgFacts where
  encRegisterArgs_inj := encRegisterArgs_inj'
  encPingArgs_inj := encPingArgs_inj'

end github_com.imdea_software.swiftpaxos_epaxos

end Perennial
