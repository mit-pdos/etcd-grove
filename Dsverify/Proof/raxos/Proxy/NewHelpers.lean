/-
Package `proxy`: helpers for `NewProxy`'s proof (`NewProxy.lean`): new bag channels, the
configuration's strings, `Init` (mode 0) and `RegisterRPC`.
-/
module

public import Dsverify.Proof.raxos.Proxy.Store
public import Dsverify.Proof.raxos.Proxy.Defs
public import Dsverify.Proof.raxos.Hyp
public import Perennial.Proof.time.Link
public import Perennial.Proof.time.Results
public import Dsverify.Proof.raxos.Hyp

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos


open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open Perennial.raxos.pure Perennial.raxos.msg
open raxos.replica.src

/-! ## The configuration's strings -/

theorem np_digitChar_1 : Nat.digitChar 1 = '1' := Nat.digitChar_eq_one.2 rfl
theorem np_digitChar_2 : Nat.digitChar 2 = '2' := Nat.digitChar_eq_two.2 rfl
theorem np_digitChar_3 : Nat.digitChar 3 = '3' := Nat.digitChar_eq_three.2 rfl
theorem np_digitChar_4 : Nat.digitChar 4 = '4' := Nat.digitChar_eq_four.2 rfl
theorem np_digitChar_5 : Nat.digitChar 5 = '5' := Nat.digitChar_eq_five.2 rfl

theorem np_decStr_1 : decStr 1 = go!"1" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), np_digitChar_1]
  decide +kernel
theorem np_decStr_2 : decStr 2 = go!"2" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), np_digitChar_2]
  decide +kernel
theorem np_decStr_3 : decStr 3 = go!"3" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), np_digitChar_3]
  decide +kernel

theorem np_decStr_4 : decStr 4 = go!"4" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), np_digitChar_4]
  decide +kernel
theorem np_decStr_5 : decStr 5 = go!"5" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_lt_base (by omega), np_digitChar_5]
  decide +kernel

theorem np_decStr_small (k : Nat) (hk1 : 1 ≤ k) (hk5 : k ≤ 5) :
    hyp.strconv.smallDigits (decStr k) ∧ hyp.strconv.decVal (decStr k) = k := by
  rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 by omega) with rfl | rfl | rfl | rfl | rfl
  · rw [np_decStr_1]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [np_decStr_2]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [np_decStr_3]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [np_decStr_4]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [np_decStr_5]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide

theorem np_digitChar_6 : Nat.digitChar 6 = '6' := Nat.digitChar_eq_six.2 rfl

theorem np_decStr_21 : decStr 21 = go!"21" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_base_le (by omega) (by omega), Nat.toDigits_of_lt_base (by omega)]
  simp only [show 21 / 10 = 2 by rfl, show 21 % 10 = 1 by rfl, np_digitChar_2,
    np_digitChar_1]
  decide +kernel

theorem np_decStr_22 : decStr 22 = go!"22" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_base_le (by omega) (by omega), Nat.toDigits_of_lt_base (by omega)]
  simp only [show 22 / 10 = 2 by rfl, show 22 % 10 = 2 by rfl, np_digitChar_2,
    np_digitChar_2]
  decide +kernel

theorem np_decStr_23 : decStr 23 = go!"23" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_base_le (by omega) (by omega), Nat.toDigits_of_lt_base (by omega)]
  simp only [show 23 / 10 = 2 by rfl, show 23 % 10 = 3 by rfl, np_digitChar_2,
    np_digitChar_3]
  decide +kernel

theorem np_decStr_24 : decStr 24 = go!"24" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_base_le (by omega) (by omega), Nat.toDigits_of_lt_base (by omega)]
  simp only [show 24 / 10 = 2 by rfl, show 24 % 10 = 4 by rfl, np_digitChar_2,
    np_digitChar_4]
  decide +kernel

theorem np_decStr_25 : decStr 25 = go!"25" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_base_le (by omega) (by omega), Nat.toDigits_of_lt_base (by omega)]
  simp only [show 25 / 10 = 2 by rfl, show 25 % 10 = 5 by rfl, np_digitChar_2,
    np_digitChar_5]
  decide +kernel

theorem np_decStr_26 : decStr 26 = go!"26" := by
  simp only [decStr, Nat.toString_eq_ofList_toDigits, String.toUTF8_eq_toByteArray,
    String.toByteArray_ofList]
  rw [Nat.toDigits_of_base_le (by omega) (by omega), Nat.toDigits_of_lt_base (by omega)]
  simp only [show 26 / 10 = 2 by rfl, show 26 % 10 = 6 by rfl, np_digitChar_2,
    np_digitChar_6]
  decide +kernel

/-- Client `c`'s name, as `NewProxy`'s `strconv.Atoi` reads it. -/
theorem np_decStr_client (c : Nat) (hc : c < 6) :
    hyp.strconv.smallDigits (decStr (21 + c)) ∧ hyp.strconv.decVal (decStr (21 + c)) = 21 + c := by
  rcases c with _ | _ | _ | _ | _ | _ | c
  · rw [show 21 + 0 = 21 from rfl, np_decStr_21]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [show 21 + (0 + 1) = 22 from rfl, np_decStr_22]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [show 21 + (0 + 1 + 1) = 23 from rfl, np_decStr_23]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [show 21 + (0 + 1 + 1 + 1) = 24 from rfl, np_decStr_24]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [show 21 + (0 + 1 + 1 + 1 + 1) = 25 from rfl, np_decStr_25]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · rw [show 21 + (0 + 1 + 1 + 1 + 1 + 1) = 26 from rfl, np_decStr_26]; unfold hyp.strconv.smallDigits hyp.strconv.decVal; decide
  · omega

theorem w64_21_inj (a b : Nat) (ha : a < 6) (hb : b < 6) :
    W64 (21 + (a : Int)) = W64 (21 + (b : Int)) ↔ a = b := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp [W64] at this
    omega
  · rintro rfl; rfl

/-- Client `c`'s address, as `NewProxy` builds it. -/
theorem np_clientAddr (c : Nat) : ipOf (1 + c) ++ go!":" ++ decStr (7601 + c) = clientAddr c := by
  unfold clientAddr portAddr ipOf
  simp only [List.append_assoc]
  rfl

theorem np_strOk_nil : strOk go!"nil" := by unfold strOk; decide

theorem np_nilBatch_ok' : batchOk nilBatch := by
  refine ⟨?_, np_strOk_nil, ?_⟩
  · unfold i64Ok nilBatch; simp only; omega
  · intro m hm; simp [nilBatch] at hm

theorem np_nilBatch_ok : batchFit nilBatch := ⟨np_nilBatch_ok', by decide +kernel⟩

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]

set_option goose.wp.extras true

/-- A new bag channel of capacity `n`. -/
theorem wp_make_bag_n {V : Type} [Pos.Countable V] [ZeroVal V] [TypedPointsto (GF := GF) V]
    {t : go.GoType} [IntoValTyped (GF := GF) V t] (P : V → IProp GF) (n : w64)
    (hn : 0 ≤ sint.Z n ∧ sint.Z n < 2 ^ 32) :
    {{ (True : IProp GF) }}
      (App (Val #(functions go.make2 [go.GoType.ChannelType go.ChanDir.sendrecv t]))
        (Val #n))
    {{ (ch : Loc), RET #ch; ∃ γc, isChanBag γc ch P }} := by
  iintro %Φ - HΦ
  iapply wp_fupd
  wp_apply (chan.wp_make2 (V := V) n) as %ch %γc ⟨#Hch, -, Hoc⟩
  · ipureintro; exact hn
  have Hs : match (if n = W64 0 then ChanState.Idle else ChanState.Buffered ([] : List V)) with
      | .Idle | .Buffered [] => True | _ => False := by
    by_cases h : n = W64 0
    · rw [if_pos h]; trivial
    · rw [if_neg h]; trivial
  imod start_bag P _ ch γc Hs $$ Hch Hoc with #Hbag
  imodintro
  iapply HΦ
  iexists γc; iexact Hbag

/-- The genesis batch `{Sender: -1, Messages: nil, Id: "nil"}`'s value. -/
theorem np_repCB_nil (v : raxos.proto.client.ClientBatch) (h1 : v.Sender' = W64 (-1))
    (h2 : v.Messages' = slice.nil) (h3 : v.Id' = go!"nil") :
    ⊢ repCBVal (GF := GF) v .discard nilBatch := by
  unfold repCBVal
  iexists []
  isplitr
  · ipureintro; rw [h1, h3]; exact ⟨rfl, rfl⟩
  rw [h2]
  isplitl
  · iapply ownSlice_nil
  unfold repList
  isplitl
  · ipureintro; rfl
  iapply BigSepL.bigSepL_nil.2; iempintro

variable [raxos.replica.src.Assumptions]

/-- `Init(0, name, 8, 8)`: the resident store, empty. -/
theorem wp_Init_0 (name : w32) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src }}
      (App (App (App (App (Val (@! raxos.replica.src.Init)) (Val #(W64 0))) (Val #name))
        (Val #(W64 8))) (Val #(W64 8)))
    {{ (bm : Loc), RET #bm; ∃ kvm : Loc, bm.[Benchmark, go!"mode"] ↦□ W64 0 ∗
        bm.[Benchmark, go!"keyLen"] ↦□ W64 8 ∗ bm.[Benchmark, go!"KVStore"] ↦□ kvm ∗
        kvm ↦$ (∅ : GMap GoString GoString) }} := by
  wp_start
  iapply wp_fupd
  wp_auto
  wp_apply (wp_map_make1 (K := GoString) (V := GoString)) as %kvm Hkvm
  iStructNamed b
  ipersist mode
  ipersist keyLen
  ipersist KVStore
  imodintro
  iapply HΦ
  iexists kvm
  iframe Hkvm
  iframe #

/-- `pr.RegisterRPC(obj, code)`: a new pair in the table. -/
theorem wp_RegisterRPC (pr rt : Loc) (RT : GMap w8 Loc) (obj : GoInterface) (code : w8) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.raxos.replica.src ∗
        pr.[Proxy, go!"rpcTable"] ↦□ rt ∗ rt ↦$ RT }}
      (App (App (Val (pr @!! go.GoType.PointerType Proxy.ty @!! go!"RegisterRPC")) (Val #obj))
        (Val #code))
    {{ (rp : Loc), RET #(); rt ↦$ (<[code := rp]> RT) ∗
        rp ↦ raxos.common.RPCPair.mk code obj }} := by
  wp_start as ⟨#Hrt, Hm⟩
  wp_auto
  wp_apply wp_mapInsert $$ Hm as Hm
  iapply HΦ
  iframe

end proofs

end Perennial.raxos
