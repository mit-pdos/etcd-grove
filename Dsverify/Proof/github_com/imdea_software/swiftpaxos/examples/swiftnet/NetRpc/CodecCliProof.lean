/-
The swiftpaxos client's codec lemmas beyond dsv-epaxos's (`NetRpc/CodecCli.lean`'s
`CliCodecLaws`), proved (`swiftCliCodecLaws`): the `GetLeader`/`GetReplicaList` arguments' encoders
give `RpcWire.lean`'s bytes, and decoding their replies into a fresh zero value is safe and, on
success, gives back the encoded value. As `NetRpc/CodecProof.lean`.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecCli
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.NetRpc.CodecSrvProof

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open github_com.imdea_software.swiftpaxos.netrpcw

namespace github_com.imdea_software.swiftpaxos

/-! ## Pure decoders -/

/-- The pure `rpcDec_t8` (`GetLeaderReply`), into the zero value. -/
def decGLR (bs : List w8) : Option (w64 × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld getU64 (W64 0) r with
    | none => none
    | some (id, r) => some (id, r)

/-- `k` more booleans, after `acc`. -/
def decBoolsGo : Nat → List Bool → List w8 → Option (List Bool × List w8)
  | 0, acc, r => some (acc, r)
  | k + 1, acc, r =>
    match decBool r with
    | none => none
    | some (x, r') => decBoolsGo k (acc ++ [x]) r'

/-- The pure `rpcDec_t15` (`[]bool`). -/
def decBools (bs : List w8) : Option (List Bool × List w8) :=
  match getU64 bs with
  | none => none
  | some (n, r) => if uint.nat n ≤ r.length then decBoolsGo (uint.nat n) [] r else none

/-- The pure `rpcDec_t12` (`GetReplicaListReply`), into the zero value. -/
def decGRL (bs : List w8) : Option ((List GoString × List Bool × Bool) × List w8) :=
  match decHdr bs with
  | none => none
  | some r =>
    match decFld decStrs [] r with
    | none => none
    | some (rl, r) =>
      match decFld decBools [] r with
      | none => none
      | some (al, r) =>
        match decFld decBool false r with
        | none => none
        | some (rd, r) => some ((rl, al, rd), r)

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.swiftnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

/-! ## Encoding the arguments -/

theorem wp_rpcEnc_t6 :
    encFn (GF := GF) examples.swiftnet.rpcEnc_t6 #replica.defs.GetLeaderArgs.mk
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

theorem wp_rpcEnc_t10 :
    encFn (GF := GF) examples.swiftnet.rpcEnc_t10 #replica.defs.GetReplicaListArgs.mk
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

theorem enc_GetLeaderArgs : enc_GetLeaderArgs.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold swiftCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t6 _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encGetLeaderArgs, tagged, tGetLeaderArgs] at HΨ
  iapply HΨ $$ Hp

theorem enc_GetReplicaListArgs : enc_GetReplicaListArgs.spec (GF := GF) := by
  intro p dq Ψ
  iintro ⟨Hp, HΨ⟩
  unfold swiftCodec
  iintro %Φ HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  rw [decide_eq_false Hnn]
  wp_auto
  wp_apply wp_rpcPutTag _ as %b ⟨Hb, Hcap⟩
  (try wp_auto)
  wp_apply wp_rpcEnc_t10 _ _ $$ [$Hb $Hcap] as %b' ⟨Hb, Hcap, -⟩
  (try wp_auto)
  iapply HΦ $$ Hb Hcap
  isimp only [encGetReplicaListArgs, tagged, tGetReplicaListArgs] at HΨ
  iapply HΨ $$ Hp

/-! ## `GetLeaderReply` -/

set_option hygiene false in
/-- Close a `GetLeaderReply` decoder's proof. -/
macro "glr_close" : tactic => `(tactic| (
  iapply HΦ
  simp only [decGLR, decHdr, decFld, ↓reduceIte, *]
  iframe
  (try iexists _)
  iapply typedPointsto_combine _ _ _ Hnn
  simp only [TypedPointsto.typedPointstoDef]
  iframe))

theorem wp_rpcDec_t8 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ replica.defs.GetLeaderReply.mk (W64 0) -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decGLR bs with
          | some (id, rest) => ⌜ok = true⌝ ∗ p ↦ replica.defs.GetLeaderReply.mk id ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ id, p ↦ replica.defs.GetLeaderReply.mk id) ∗
              b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.swiftnet.rpcDec_t8)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step_with decGLR (glr_close)
  all_goals fld_step wp_rpcDec_t4 getU64 LeaderId fail glr_close
  all_goals ((try wp_auto); glr_close)

end proof

theorem decGLR_enc (id : w64) : decGLR (strct [fInt id]) = some (id, []) := by
  have e : strct [fInt id] = W8 1 :: (fInt id ++ []) := by simp [strct]
  rw [e]
  simp only [decGLR, decHdr, ↓reduceIte, decFld_fInt]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.swiftnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem dec_GetLeaderReply : dec_GetLeaderReply.spec (GF := GF) := by
  intro p rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold swiftCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data rep dq $$ Hd
  iintro %t %r %ok H
  rcases hg : getTag rep with _ | ⟨t', rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hd⟩
    subst Hok
    wp_auto
    ihave HΨ0 := HΨ $$ %false [Hp]
    · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t8 r rest dq p $$ Hr Hp
    iintro %r2 %ok2 H2
    rcases hd : decGLR rest with _ | ⟨id, rest2⟩
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%id1, Hp⟩, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
      dec_fail
    · simp only [hd]
      icases H2 with ⟨%Hok, Hp, Hr2, Hback2⟩
      subst Hok
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
      wp_auto
      ihave Hd := Hback $$ [Hback2 Hr2]
      · iapply Hback2 $$ Hr2
      by_cases h0 : rest2 = []
      · subst h0
        rw [show r2.len = W64 0 by simp at Hl2; word]
        wp_auto
        iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp]
        · iapply HΨ
          simp only [ite_true]
          iexists id
          iframe
          ipureintro
          intro id' he
          subst he
          rw [encGetLeaderReply, getTag_tagged _ _ (by decide)] at hg
          cases hg
          rw [decGLR_enc] at hd
          cases hd
          rfl
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
        dec_fail

/-! ## `[]bool` -/

theorem wp_rpcDec_t15 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ slice.nil -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decBools bs with
          | some (x, rest) => ⌜ok = true⌝ ∗ (∃ sl : GoSlice, p ↦ sl ∗ sl ↦* x) ∗ r ↦*{dq} rest ∗
              (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗ (∃ sl : GoSlice, p ↦ sl) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.swiftnet.rpcDec_t15)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetU64 b bs dq $$ Hb
  iintro %x %r %ok H
  unfold decBools
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
    wp_auto
    have hxs : sint.Z x = uint.Z x := by word
    rw [if_pos hn]
    by_cases hx0 : x = W64 0
    rw [decide_eq_false (by rw [hx0]; decide)]
    wp_auto
    rw [if_pos (by rw [hx0]; decide)]
    wp_auto
    ihave Hn := ownSlice_nil (V := Bool) (DFrac.own 1)
    ihave Hs : (slice.slice slice.nil Bool (W64 0) x ↦* List.replicate (uint.nat x) false) $$ [Hn]
    · subst hx0
      icases (ownSlice_slice (V := Bool) (W64 0) (W64 0) slice.nil (DFrac.own 1) []
        ⟨by decide, by decide, by decide⟩).1 $$ Hn with ⟨-, Hs, -⟩
      have e : subslice (sint.nat (W64 0)) (sint.nat (W64 0)) ([] : List Bool) =
          List.replicate (uint.nat (W64 0)) false := by simp [subslice]
      rw [e]
      iexact Hs
    generalize slice.slice slice.nil Bool (W64 0) x = sl at *
    iclear Hn
    rotate_left
    rw [decide_eq_true (show uint.Z (0 : w64) < uint.Z x by
      have : uint.Z x ≠ 0 := fun h => hx0 (by word)
      have : (0 : Int) ≤ uint.Z x := by word
      show (0 : Int) < uint.Z x
      omega)]
    wp_auto
    wp_apply wp_slice_make2 (V := Bool) x
    · ipureintro; word
    iintro %sl ⟨Hs, -⟩
    rw [show sint.nat x = uint.nat x by word, show zero_val Bool = false from rfl]
    wp_auto
    rotate_left
    all_goals
      ihave %hsl := ownSlice_len _ _ _ $$ Hs
      simp only [List.length_replicate] at hsl
      ihave HI : (∃ (i : w64) (R : GoSlice) (acc : List Bool) (cur : List w8),
          "i" ∷ i_ptr ↦ i ∗ "r" ∷ r_ptr ↦ R ∗ "ok" ∷ ok_ptr ↦ true ∗ "Hr" ∷ R ↦*{dq} cur ∗
          "Hback" ∷ (R ↦*{dq} cur -∗ b ↦*{dq} bs) ∗
          "Hs" ∷ sl ↦* (acc ++ List.replicate (uint.nat x - uint.nat i) false) ∗
          "%Hi" ∷ ⌜acc.length = uint.nat i ∧ uint.nat i ≤ uint.nat x ∧
            decBoolsGo (uint.nat x - uint.nat i) acc cur = decBoolsGo (uint.nat x) [] rest⌝ : IProp GF)
          $$ [i r ok Hr Hback Hs]
      · iexists W64 0, r, [], rest
        simp only [show uint.nat (W64 0) = 0 from rfl, Nat.sub_zero, List.nil_append]
        iframe
        ipureintro
        simp
      wp_for HI
      wp_if_destruct
      · have hi : uint.Z i < uint.Z x := by
          exact Hif
        have hk : uint.nat x - uint.nat i = (uint.nat x - uint.nat i - 1) + 1 := by word
        rw [if_pos (show 0 ≤ sint.Z i ∧ sint.Z i < sint.Z sl.len by
          have := hsl.1; have := hsl.2
          have h2 : ((sint.Z sl.len).toNat : Int) = sint.Z sl.len := Int.toNat_of_nonneg hsl.2
          rw [show sint.nat sl.len = (sint.Z sl.len).toNat from rfl] at *
          word)]
        have hlk : (acc ++ List.replicate (uint.nat x - uint.nat i) false)[(sint.Z i).toNat]? =
            some false := by
          rw [show (sint.Z i).toNat = acc.length by word, hk]
          simp
        icases ownSlice_elem_acc (sint.Z i) false sl _ _ (by word) hlk $$ Hs with ⟨He, Hs⟩
        wp_apply wp_rpcDec_t16 R cur dq _ _ $$ Hr He
        iintro %R2 %ok2 Hd
        rcases hd : decBool cur with _ | ⟨v, cur2⟩
        · simp only [hd]
          icases Hd with ⟨%Hok, He, Hr⟩
          subst Hok
          ihave Hs := Hs $$ He
          wp_auto
          rw [forPostcondition_unseal]; unfold forPostconditionDef; iright; iright; iright; ileft
          iexists #()
          isplitr
          · ipureintro; rfl
          dsimp only
          wp_auto
          have hres : decBoolsGo (uint.nat x) [] rest = none := by
            rw [← Hi.2.2, hk]; simp [decBoolsGo, hd]
          iapply HΦ
          rw [hres]
          dsimp only
          ihave Hb := Hback $$ Hr
          iframe
          ipureintro; rfl
        · simp only [hd]
          icases Hd with ⟨%Hok, He, Hr, Hback2⟩
          subst Hok
          ihave Hs := Hs $$ He
          wp_auto
          wp_for_post
          ihave Hback := wand_trans _ _ _ $$ Hback2 Hback
          have hi1 : uint.nat (i + W64 1) = uint.nat i + 1 := by word
          have hset : (acc ++ List.replicate (uint.nat x - uint.nat i) false).set (sint.Z i).toNat v =
              (acc ++ [v]) ++ List.replicate (uint.nat x - uint.nat (i + W64 1)) false := by
            rw [show (sint.Z i).toNat = acc.length by word, hk, hi1,
              show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
            simp [List.replicate_succ]
          rw [hset]
          iframe
          iexists i + W64 1, R2, acc ++ [v], cur2
          iframe
          ipureintro
          refine ⟨by rw [List.length_append, Hi.1, hi1]; rfl, by rw [hi1]; omega, ?_⟩
          rw [← Hi.2.2, hk, hi1, show uint.nat x - (uint.nat i + 1) = uint.nat x - uint.nat i - 1 by omega]
          simp [decBoolsGo, hd]
      · (try wp_auto)
        have hix : uint.nat x - uint.nat i = 0 := by
          have : ¬ uint.Z i < uint.Z x := by
            exact Hif
          word
        have hres : decBoolsGo (uint.nat x) [] rest = some (acc, cur) := by
          rw [← Hi.2.2, hix]; rfl
        iapply HΦ
        rw [hres]
        dsimp only
        rw [hix, List.replicate_zero, List.append_nil]
        iframe
        ipureintro; rfl


/-! ## `GetReplicaListReply` -/

set_option hygiene false in
/-- Close a `GetReplicaListReply` decoder's proof (its slice fields in any of their states). -/
macro "grl_close" : tactic => `(tactic| (
  iapply HΦ
  simp only [decGRL, decHdr, decFld, ↓reduceIte, *]
  iframe
  (first
    | icases ReplicaList with ⟨%slR, ReplicaList, HslR⟩
    | icases ReplicaList with ⟨%slR, ReplicaList⟩
    | ihave HslR := ownSlice_nil (V := GoString) (DFrac.own 1))
  (first
    | icases AliveList with ⟨%slA, AliveList, HslA⟩
    | icases AliveList with ⟨%slA, AliveList⟩
    | ihave HslA := ownSlice_nil (V := Bool) (DFrac.own 1))
  first
  | (iexists _, _, _
     iapply typedPointsto_combine _ _ _ Hnn
     simp only [TypedPointsto.typedPointstoDef]
     iframe; done)
  | (iexists _, _
     isplitr [HslR HslA]
     · iapply typedPointsto_combine _ _ _ Hnn
       simp only [TypedPointsto.typedPointstoDef]
       iframe
     iframe
     all_goals ((try isplitl []) <;> first | iexact HslR | iexact HslA)
     done)))

set_option maxHeartbeats 4000000 in
theorem wp_rpcDec_t12 (b : GoSlice) (bs : List w8) (dq : DFrac) (p : Loc)
    (Φ : val → IProp GF) :
    b ↦*{dq} bs -∗ p ↦ replica.defs.GetReplicaListReply.mk slice.nil slice.nil false -∗
    ▷ (∀ (r : GoSlice) (ok : Bool),
        (match decGRL bs with
          | some ((rl, al, rd), rest) => ⌜ok = true⌝ ∗
              (∃ s1 s2 : GoSlice, p ↦ replica.defs.GetReplicaListReply.mk s1 s2 rd ∗
                s1 ↦* rl ∗ s2 ↦* al) ∗
              r ↦*{dq} rest ∗ (r ↦*{dq} rest -∗ b ↦*{dq} bs)
          | none => ⌜ok = false⌝ ∗
              (∃ s1 s2 rd, p ↦ replica.defs.GetReplicaListReply.mk s1 s2 rd) ∗ b ↦*{dq} bs) -∗
        Φ (PairV #r #ok)) -∗
    WP (App (App (Val (@! examples.swiftnet.rpcDec_t12)) (Val #b)) (Val #p)) {{ Φ }} := by
  iintro Hb Hp HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  iStructNamed Hp
  hdr_step_with decGRL (grl_close)
  all_goals fld_step wp_rpcDec_t13 decStrs ReplicaList fail grl_close
  all_goals fld_step wp_rpcDec_t15 decBools AliveList fail grl_close
  all_goals fld_step wp_rpcDec_t16 decBool Ready fail grl_close
  all_goals ((try wp_auto); grl_close)

end proof

/-! ### `GetReplicaListReply` round trip -/

theorem decBool_enc (x : Bool) (rest : List w8) : decBool (encBool x ++ rest) = some (x, rest) := by
  cases x <;> simp [encBool, decBool, show uint.Z (W8 1) = 1 from rfl,
    show uint.Z (W8 0) = 0 from rfl] <;> decide

theorem decBoolsGo_enc (xs acc : List Bool) (rest : List w8) :
    decBoolsGo xs.length acc ((xs.map encBool).flatten ++ rest) = some (acc ++ xs, rest) := by
  induction xs generalizing acc with
  | nil => simp [decBoolsGo]
  | cons x xs ih =>
    simp only [List.length_cons, List.map_cons, List.flatten_cons, List.append_assoc, decBoolsGo,
      decBool_enc, ih (acc ++ [x])]
    simp

theorem len_flatten_encBool (xs : List Bool) : (xs.map encBool).flatten.length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [encBool, ih]

theorem decBools_enc (xs : List Bool) (rest : List w8) (hb : xs.length < 2 ^ 64) :
    decBools (encBools xs ++ rest) = some (xs, rest) := by
  unfold decBools encBools
  rw [List.append_assoc, getU64_enc']
  have hn : uint.nat (W64 xs.length) = xs.length := by
    show (BitVec.ofNat 64 xs.length).toNat = xs.length
    simp only [BitVec.toNat_ofNat]; omega
  have hle : xs.length ≤ ((xs.map encBool).flatten ++ rest).length := by
    simp only [List.length_append, len_flatten_encBool]; omega
  simp only [hn, hle, ↓reduceIte, decBoolsGo_enc xs [] rest, List.nil_append]

theorem decFld_fBools (xs : List Bool) (rest : List w8) (hb : xs.length < 2 ^ 64) :
    decFld decBools [] (fBools xs ++ rest) = some (xs, rest) := by
  apply decFld_fld
  · intro h; simpa using h
  · intro _; exact decBools_enc xs rest hb

theorem decGRL_enc (rl : List GoString) (al : List Bool) (r : Bool)
    (hb : (encGetReplicaListReply rl al r).length < 2 ^ 63) :
    decGRL (strct [fStrs rl, fBools al, fBool r]) = some ((rl, al, r), []) := by
  have hlen := hb
  simp only [encGetReplicaListReply, tagged, strct, List.flatten_cons, List.flatten_nil,
    List.length_append, List.length_cons, List.length_nil] at hlen
  have hs : (encStrs rl).length < 2 ^ 63 := by
    by_cases h : rl = []
    · subst h; simp [encStrs, u64Le_length]
    · have : (fStrs rl).length = (encStrs rl).length + 1 := by
        simp [fStrs, fld, h]
      omega
  have ha : al.length < 2 ^ 64 := by
    by_cases h : al = []
    · subst h; simp
    · have : (fBools al).length = (encBools al).length + 1 := by
        simp [fBools, fld, h]
      have : (encBools al).length = 8 + al.length := by
        simp only [encBools, List.length_append, u64Le_length, len_flatten_encBool]
      omega
  have e : strct [fStrs rl, fBools al, fBool r] =
      W8 1 :: (fStrs rl ++ (fBools al ++ (fBool r ++ []))) := by
    simp [strct]
  rw [e]
  simp only [decGRL, decHdr, ↓reduceIte, decFld_fStrs rl _ hs, decFld_fBools al _ ha, decFld_fBool]

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [net.rpc.Assumptions] [π : NetProtoGS]
variable [examples.swiftnet.Assumptions]
variable [bvi : go.BasicIntoValInj]

set_option goose.wp.extras true

theorem dec_GetReplicaListReply : dec_GetReplicaListReply.spec (GF := GF) := by
  intro p rep Ψ
  iintro ⟨%Htag, Hp, HΨ⟩
  unfold swiftCodec
  iintro %data %dq %Φ Hd HΦ
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hp
  ihave %Hlen := ownSlice_lenZ _ _ _ $$ Hd
  wp_func_call
  wp_call
  wp_auto
  wp_apply wp_rpcGetTag data rep dq $$ Hd
  iintro %t %r %ok H
  rcases hg : getTag rep with _ | ⟨t', rest⟩
  · simp only [hg]
    icases H with ⟨%Hok, Hd⟩
    subst Hok
    wp_auto
    ihave HΨ0 := HΨ $$ %false [Hp]
    · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
    dec_fail
  · simp only [hg]
    icases H with ⟨%Hok, Hr, Hback⟩
    obtain ⟨rfl, rfl⟩ := Hok
    have ht := Htag _ _ hg
    subst ht
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcDec_t12 r rest dq p $$ Hr Hp
    iintro %r2 %ok2 H2
    rcases hd : decGRL rest with _ | ⟨⟨rl, al, rd⟩, rest2⟩
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%s1, %s2, %rd1, Hp⟩, Hr⟩
      subst Hok
      wp_auto
      ihave Hd := Hback $$ Hr
      ihave HΨ0 := HΨ $$ %false [Hp]
      · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
      dec_fail
    · simp only [hd]
      icases H2 with ⟨%Hok, ⟨%s1, %s2, Hp, Hs1, Hs2⟩, Hr2, Hback2⟩
      subst Hok
      ihave %Hl2 := ownSlice_len _ _ _ $$ Hr2
      wp_auto
      ihave Hd := Hback $$ [Hback2 Hr2]
      · iapply Hback2 $$ Hr2
      by_cases h0 : rest2 = []
      · subst h0
        rw [show r2.len = W64 0 by simp at Hl2; word]
        wp_auto
        iapply HΦ $$ %interface.nil %true Hd %(by simp) [HΨ Hp Hs1 Hs2]
        · iapply HΨ
          simp only [ite_true]
          iexists s1, s2, rl, al, rd
          iframe
          ipureintro
          intro rl' al' r' he
          subst he
          have h3 : sint.Z data.len < 2 ^ 63 := by word
          have hb : (encGetReplicaListReply rl' al' r').length < 2 ^ 63 := by omega
          rw [encGetReplicaListReply, getTag_tagged _ _ (by decide)] at hg
          cases hg
          rw [decGRL_enc rl' al' r' hb] at hd
          cases hd
          exact ⟨rfl, rfl, rfl⟩
        simp only [ite_true]
        ipureintro; trivial
      · rw [decide_eq_false (show ¬ r2.len = W64 0 by
          intro h; rw [h] at Hl2; exact h0 (List.eq_nil_of_length_eq_zero (Hl2.1.trans (by rfl))))]
        wp_auto
        ihave HΨ0 := HΨ $$ %false [Hp]
        · simp only [Bool.false_eq_true, ite_false]; iexists _; iexact Hp
        dec_fail

/-- The client's codec lemmas beyond `CodecLaws`, proved. -/
theorem swiftCliCodecLaws : CliCodecLaws (GF := GF) where
  enc_GetLeaderArgs := enc_GetLeaderArgs
  enc_GetReplicaListArgs := enc_GetReplicaListArgs
  dec_GetLeaderReply := dec_GetLeaderReply
  dec_GetReplicaListReply := dec_GetReplicaListReply

end proof

end github_com.imdea_software.swiftpaxos

end Perennial
