/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Enc.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The codec's encoders (`rpcEnc_*`): each appends its value's encoding (`Spec/swift/Wire.lean`'s
`cU64`, `cI32`, `cBytes`, `cList`, ...) to a fully owned byte slice.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Sync
public import Perennial.Proof.github_com.mit_pdos.perennial.goose.model.strings.Base

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

open sp

/-- A fully owned byte slice holding `bs`, with its capacity. -/
abbrev bytesOwn (b : GoSlice) (bs : List w8) : IProp GF :=
  iprop(b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1))

theorem bytesOwn_intro (b : GoSlice) (bs : List w8) :
    (b ↦* bs ∗ ownSliceCap w8 b (DFrac.own 1) : IProp GF) ⊢ bytesOwn b bs := by
  iintro H; iexact H

theorem wp_rpcEnc_int (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_int)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cU64 x) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb Hcap] as %b' ⟨Hb, Hcap⟩
  · iframe
  iapply HΦ; unfold bytesOwn; iframe

theorem wp_rpcEnc_int32 (b : GoSlice) (bs : List w8) (x : w32) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_int32)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cI32 x) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb Hcap] as %b' ⟨Hb, Hcap⟩
  · iframe
  iapply HΦ; unfold bytesOwn; iframe

theorem wp_rpcEnc_uint8 (b : GoSlice) (bs : List w8) (x : w8) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_uint8)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cU64 (BitVec.zeroExtend 64 x)) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb Hcap] as %b' ⟨Hb, Hcap⟩
  · iframe
  have : cU64 (BitVec.zeroExtend 64 x) = u64Le (W64 (uint.Z x)) := by
    simp only [cU64]; congr 1; apply BitVec.eq_of_toNat_eq; simp
  iapply HΦ; unfold bytesOwn; rw [this]; iframe

theorem wp_rpcEnc_int64 (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_int64)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cU64 x) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb Hcap] as %b' ⟨Hb, Hcap⟩
  · iframe
  iapply HΦ; unfold bytesOwn; iframe

theorem wp_rpcEnc_bool (b : GoSlice) (bs : List w8) (x : Bool) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_bool)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cBool x) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  cases x
  · wp_auto
    wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 0]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
    · iframe
    iapply HΦ; unfold bytesOwn; iframe
  · wp_auto
    wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 1]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
    · iframe
    wp_auto
    iapply HΦ; unfold bytesOwn; iframe

theorem wp_rpcEnc_string (b : GoSlice) (bs : List w8) (x : GoString) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_string)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cBytes x) }} := by
  wp_start as ⟨Hb, Hcap⟩
  wp_auto
  wp_apply github_com.mit_pdos.perennial.goose.model.strings.wp_string_len as %Hlen
  wp_apply wp_rpcPutU64 $$ [Hb Hcap] as %b1 ⟨Hb, Hcap⟩
  · iframe
  try wp_auto
  wp_apply wp_string_to_bytes as %sl ⟨Hsl, -⟩
  wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
  · iframe
  iapply HΦ; unfold bytesOwn
  simp only [cBytes, cU64, List.append_assoc]
  iframe

theorem wp_rpcEnc_S_string (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac)
    (xs : List GoString) :
    {{ (bytesOwn b bs ∗ v ↦*{dq} xs : IProp GF) }}
      (App (App (Val (@! rpcEnc_S_string)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cList cBytes xs) ∗ v ↦*{dq} xs }} := by
  wp_start as ⟨Hb, Hv⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb] as %b1 Hb
  · iframe
  try wp_auto
  ihave HI : (∃ (i : w64) (x : GoString) (bi : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ x ∗ "b" ∷ b_ptr ↦ bi ∗
      "Hb" ∷ bytesOwn bi (bs ++ u64Le v.len ++ ((xs.take (sint.nat i)).map cBytes).flatten) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.len⌝ : IProp GF) $$ [i x b Hb]
  · iexists W64 0, _, b1
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.flatten_nil,
      List.append_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · list_elem xs (sint.nat i) as y
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index v (sint.Z i) xs dq y Hi.1 $$ [Hv] as Hv
    · iframe; ipureintro; exact Hy_lookup
    wp_apply wp_rpcEnc_string $$ Hb as %b2 Hb
    wp_for_post
    iframe
    iexists i + W64 1, y, b2
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, Hy_lookup]
    simp only [Option.toList_some, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    iframe
    ipureintro; word
  · have hi : sint.nat i = xs.length := by word
    rw [hi, List.take_length]
    iapply HΦ
    iframe
    simp only [cList, cU64, List.append_assoc]
    have : W64 xs.length = v.len := by word
    rw [this]
    iframe

theorem wp_rpcEnc_S_bool (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac)
    (xs : List Bool) :
    {{ (bytesOwn b bs ∗ v ↦*{dq} xs : IProp GF) }}
      (App (App (Val (@! rpcEnc_S_bool)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cList cBool xs) ∗ v ↦*{dq} xs }} := by
  wp_start as ⟨Hb, Hv⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb] as %b1 Hb
  · iframe
  try wp_auto
  ihave HI : (∃ (i : w64) (x : Bool) (bi : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ x ∗ "b" ∷ b_ptr ↦ bi ∗
      "Hb" ∷ bytesOwn bi (bs ++ u64Le v.len ++ ((xs.take (sint.nat i)).map cBool).flatten) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.len⌝ : IProp GF) $$ [i x b Hb]
  · iexists W64 0, _, b1
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.flatten_nil,
      List.append_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · list_elem xs (sint.nat i) as y
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index v (sint.Z i) xs dq y Hi.1 $$ [Hv] as Hv
    · iframe; ipureintro; exact Hy_lookup
    wp_apply wp_rpcEnc_bool $$ Hb as %b2 Hb
    wp_for_post
    iframe
    iexists i + W64 1, y, b2
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, Hy_lookup]
    simp only [Option.toList_some, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    iframe
    ipureintro; word
  · have hi : sint.nat i = xs.length := by word
    rw [hi, List.take_length]
    iapply HΦ
    iframe
    simp only [cList, cU64, List.append_assoc]
    have : W64 xs.length = v.len := by word
    rw [this]
    iframe

theorem wp_rpcEnc_swift_CommandId (b : GoSlice) (bs : List w8) (x : swift.CommandId) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_swift_CommandId)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cCmdId (goCmdIdC x)) }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcEnc_int32 $$ Hb as %b1 Hb
  wp_apply wp_rpcEnc_int32 $$ Hb as %b2 Hb
  iapply HΦ
  simp only [cCmdId, goCmdIdC, List.append_assoc]
  iexact Hb

theorem wp_rpcEnc_S_swift_CommandId (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac)
    (xs : List swift.CommandId) :
    {{ (bytesOwn b bs ∗ v ↦*{dq} xs : IProp GF) }}
      (App (App (Val (@! rpcEnc_S_swift_CommandId)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cList (fun c => cCmdId (goCmdIdC c)) xs) ∗ v ↦*{dq} xs }} := by
  wp_start as ⟨Hb, Hv⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb] as %b1 Hb
  · iframe
  try wp_auto
  ihave HI : (∃ (i : w64) (x : swift.CommandId) (bi : GoSlice),
      "i" ∷ i_ptr ↦ i ∗ "x" ∷ x_ptr ↦ x ∗ "b" ∷ b_ptr ↦ bi ∗
      "Hb" ∷ bytesOwn bi (bs ++ u64Le v.len ++ ((xs.take (sint.nat i)).map (fun c => cCmdId (goCmdIdC c))).flatten) ∗
      "%Hi" ∷ ⌜0 ≤ sint.Z i ∧ sint.Z i ≤ sint.Z v.len⌝ : IProp GF) $$ [i x b Hb]
  · iexists W64 0, _, b1
    iframe
    simp only [show sint.nat (W64 0) = 0 from rfl, List.take_zero, List.map_nil, List.flatten_nil,
      List.append_nil]
    iframe
    ipureintro; word
  wp_for HI
  wp_if_destruct
  · list_elem xs (sint.nat i) as y
    simp only [Hi.1, Hif, and_self, ↓reduceIte]
    wp_apply wp_load_slice_index v (sint.Z i) xs dq y Hi.1 $$ [Hv] as Hv
    · iframe; ipureintro; exact Hy_lookup
    wp_apply wp_rpcEnc_swift_CommandId $$ Hb as %b2 Hb
    wp_for_post
    iframe
    iexists i + W64 1, y, b2
    rw [show sint.nat (i + W64 1) = sint.nat i + 1 by word, List.take_add_one, Hy_lookup]
    simp only [Option.toList_some, List.map_append, List.flatten_append, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc]
    iframe
    ipureintro; word
  · have hi : sint.nat i = xs.length := by word
    rw [hi, List.take_length]
    iapply HΦ
    iframe
    simp only [cList, cU64, List.append_assoc]
    have : W64 xs.length = v.len := by word
    rw [this]
    iframe

theorem wp_rpcEnc_S_byte (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac) (xs : List w8) :
    {{ (bytesOwn b bs ∗ v ↦*{dq} xs : IProp GF) }}
      (App (App (Val (@! rpcEnc_S_byte)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cBytes xs) ∗ v ↦*{dq} xs }} := by
  wp_start as ⟨Hb, Hv⟩
  ihave %Hl := ownSlice_len _ _ _ $$ Hv
  wp_auto
  wp_apply wp_rpcPutU64 $$ [Hb] as %b1 ⟨Hb, Hcap⟩
  · iframe
  try wp_auto
  wp_apply wp_slice_append $$ [Hb Hcap Hv] as %b' ⟨Hb, Hcap, Hv⟩
  · iframe
  iapply HΦ
  iframe
  simp only [cBytes, cU64, List.append_assoc]
  have : W64 xs.length = v.len := by word
  rw [this]
  unfold bytesOwn
  iframe

theorem wp_rpcEnc_state_Operation (b : GoSlice) (bs : List w8) (x : w8) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_state_Operation)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cU64 (BitVec.zeroExtend 64 x)) }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcEnc_uint8 $$ Hb as %b' Hb
  iapply HΦ $$ Hb

theorem wp_rpcEnc_state_Key (b : GoSlice) (bs : List w8) (x : w64) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_state_Key)) (Val #b)) (Val #x))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cU64 x) }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcEnc_int64 $$ Hb as %b' Hb
  iapply HΦ $$ Hb

theorem wp_rpcEnc_state_Value (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac) (xs : List w8) :
    {{ (bytesOwn b bs ∗ v ↦*{dq} xs : IProp GF) }}
      (App (App (Val (@! rpcEnc_state_Value)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cBytes xs) ∗ v ↦*{dq} xs }} := by
  wp_start as ⟨Hb, Hv⟩
  wp_auto
  wp_apply wp_rpcEnc_S_byte $$ [Hb Hv] as %b' ⟨Hb, Hv⟩
  · iframe
  iapply HΦ; iframe

theorem wp_rpcEnc_state_Command (b : GoSlice) (bs : List w8) (c : state.Command) (dq : DFrac)
    (x : Cmd) :
    {{ (bytesOwn b bs ∗ cmdOwnC c dq x : IProp GF) }}
      (App (App (Val (@! rpcEnc_state_Command)) (Val #b)) (Val #c))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cCmd x) ∗ cmdOwnC c dq x }} := by
  wp_start as ⟨Hb, Hc⟩
  unfold cmdOwnC
  icases Hc with ⟨%Hc, Hv⟩
  obtain ⟨op, k, vv⟩ := c
  simp only at Hc
  obtain ⟨rfl, rfl⟩ := Hc
  wp_auto
  wp_apply wp_rpcEnc_state_Operation $$ Hb as %b1 Hb
  wp_apply wp_rpcEnc_state_Key $$ Hb as %b2 Hb
  wp_apply wp_rpcEnc_state_Value $$ [Hb Hv] as %b3 ⟨Hb, Hv⟩
  · iframe
  try wp_auto
  iapply HΦ
  simp only [cCmd, List.append_assoc]
  iframe
  ipureintro; simp

theorem wp_rpcEnc_swift_Dep (b : GoSlice) (bs : List w8) (v : GoSlice) (dq : DFrac)
    (xs : List swift.CommandId) :
    {{ (bytesOwn b bs ∗ v ↦*{dq} xs : IProp GF) }}
      (App (App (Val (@! rpcEnc_swift_Dep)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ cList (fun c => cCmdId (goCmdIdC c)) xs) ∗
        v ↦*{dq} xs }} := by
  wp_start as ⟨Hb, Hv⟩
  wp_auto
  wp_apply wp_rpcEnc_S_swift_CommandId $$ [Hb Hv] as %b' ⟨Hb, Hv⟩
  · iframe
  iapply HΦ; iframe

theorem wp_rpcEnc_defs_RegisterArgs (b : GoSlice) (bs : List w8) (a : GoString) (pt : w64) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_RegisterArgs)) (Val #b)) (Val #(⟨a, pt⟩ : replica.defs.RegisterArgs)))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody (.registerArgs a pt)) }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcEnc_string $$ Hb as %b1 Hb
  wp_apply wp_rpcEnc_int $$ Hb as %b2 Hb
  iapply HΦ; simp only [kitBody, List.append_assoc]; iexact Hb

theorem wp_rpcEnc_defs_RegisterReply (b : GoSlice) (bs : List w8) (i : w64) (sl : GoSlice)
    (r l : Bool) (dq : DFrac) (ns : List GoString) :
    {{ (bytesOwn b bs ∗ sl ↦*{dq} ns : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_RegisterReply)) (Val #b))
        (Val #(⟨i, sl, r, l⟩ : replica.defs.RegisterReply)))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody (.registerReply i ns r l)) ∗ sl ↦*{dq} ns }} := by
  wp_start as ⟨Hb, Hns⟩
  wp_auto
  wp_apply wp_rpcEnc_int $$ Hb as %b1 Hb
  wp_apply wp_rpcEnc_S_string $$ [Hb Hns] as %b2 ⟨Hb, Hns⟩
  · iframe
  try wp_auto
  wp_apply wp_rpcEnc_bool $$ Hb as %b3 Hb
  wp_apply wp_rpcEnc_bool $$ Hb as %b4 Hb
  iapply HΦ; simp only [kitBody, List.append_assoc]; iframe

theorem wp_rpcEnc_defs_GetLeaderReply (b : GoSlice) (bs : List w8) (i : w64) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_GetLeaderReply)) (Val #b)) (Val #(⟨i⟩ : replica.defs.GetLeaderReply)))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody (.getLeaderReply i)) }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcEnc_int $$ Hb as %b1 Hb
  iapply HΦ; simp only [kitBody]; iexact Hb

theorem wp_rpcEnc_defs_GetReplicaListReply (b : GoSlice) (bs : List w8) (s1 s2 : GoSlice) (r : Bool)
    (dq dq2 : DFrac) (rs : List GoString) (al : List Bool) :
    {{ (bytesOwn b bs ∗ s1 ↦*{dq} rs ∗ s2 ↦*{dq2} al : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_GetReplicaListReply)) (Val #b))
        (Val #(⟨s1, s2, r⟩ : replica.defs.GetReplicaListReply)))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody (.getReplicaListReply rs al r)) ∗
        s1 ↦*{dq} rs ∗ s2 ↦*{dq2} al }} := by
  wp_start as ⟨Hb, H1, H2⟩
  wp_auto
  wp_apply wp_rpcEnc_S_string $$ [Hb H1] as %b1 ⟨Hb, H1⟩
  · iframe
  try wp_auto
  wp_apply wp_rpcEnc_S_bool $$ [Hb H2] as %b2 ⟨Hb, H2⟩
  · iframe
  try wp_auto
  wp_apply wp_rpcEnc_bool $$ Hb as %b3 Hb
  iapply HΦ; simp only [kitBody, List.append_assoc]; iframe

theorem wp_rpcEnc_defs_PingArgs (b : GoSlice) (bs : List w8) (a : w8) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_PingArgs)) (Val #b)) (Val #(⟨a⟩ : replica.defs.PingArgs)))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody (.pingArgs a)) }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcEnc_uint8 $$ Hb as %b1 Hb
  iapply HΦ; simp only [kitBody]; iexact Hb

theorem wp_rpcEnc_defs_BeTheLeaderReply (b : GoSlice) (bs : List w8) (l n : w32) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_BeTheLeaderReply)) (Val #b))
        (Val #(⟨l, n⟩ : replica.defs.BeTheLeaderReply)))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody (.beTheLeaderReply l n)) }} := by
  wp_start as Hb
  wp_auto
  wp_apply wp_rpcEnc_int32 $$ Hb as %b1 Hb
  wp_apply wp_rpcEnc_int32 $$ Hb as %b2 Hb
  iapply HΦ; simp only [kitBody, List.append_assoc]; iexact Hb

theorem wp_rpcEnc_defs_GetLeaderArgs (b : GoSlice) (bs : List w8) (v : replica.defs.GetLeaderArgs) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_GetLeaderArgs)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody .getLeaderArgs) }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ; simp only [kitBody, List.append_nil]; iexact Hb

theorem wp_rpcEnc_defs_GetReplicaListArgs (b : GoSlice) (bs : List w8) (v : replica.defs.GetReplicaListArgs) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_GetReplicaListArgs)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody .getReplicaListArgs) }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ; simp only [kitBody, List.append_nil]; iexact Hb

theorem wp_rpcEnc_defs_PingReply (b : GoSlice) (bs : List w8) (v : replica.defs.PingReply) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_PingReply)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody .pingReply) }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ; simp only [kitBody, List.append_nil]; iexact Hb

theorem wp_rpcEnc_defs_BeTheLeaderArgs (b : GoSlice) (bs : List w8) (v : replica.defs.BeTheLeaderArgs) :
    {{ (bytesOwn b bs : IProp GF) }}
      (App (App (Val (@! rpcEnc_defs_BeTheLeaderArgs)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; bytesOwn b' (bs ++ kitBody .beTheLeaderArgs) }} := by
  wp_start as Hb
  wp_auto
  iapply HΦ; simp only [kitBody, List.append_nil]; iexact Hb

theorem wp_rpcEnc_map_swift_CommandId_int (b : GoSlice) (bs : List w8) (mp : GoMap) (dq : DFrac)
    (l : List (CmdId × w64)) :
    {{ (bytesOwn b bs ∗ mapOwnC (V := w64) mp dq (fun v a => iprop(⌜v = a⌝)) (some l) : IProp GF) }}
      (App (App (Val (@! rpcEnc_map_swift_CommandId_int)) (Val #b)) (Val #mp))
    {{ (b' : GoSlice), RET #b'; ∃ l' : List (CmdId × w64), ⌜l'.Perm l⌝ ∗
        bytesOwn b' (bs ++ cList (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) l') ∗
        mapOwnC (V := w64) mp dq (fun v a => iprop(⌜v = a⌝)) (some l) }} := by
  wp_start as ⟨Hb, Hm⟩
  unfold mapOwnC
  icases Hm with ⟨%mv, %ps, Hm, %Hrep, Hbig⟩
  obtain ⟨rfl, Hnd, Hkeys⟩ := Hrep
  have hlen : ps.length = l.length := by
    have := congrArg List.length Hkeys; simpa using this
  wp_auto
  wp_apply (wp_rawMap_len (V := w64) mp dq ps) $$ [Hm] as ⟨Hm, %Hpl⟩
  · unfold rawMap; iexact Hm
  wp_apply wp_rpcPutU64 $$ [Hb] as %b1 Hb
  · iframe
  try wp_auto
  simp only
  wp_apply (wp_rawMap_for_range (V := w64)
    (fun keys i => iprop(∃ (bi : GoSlice) (x : swift.CommandId) (y : w64),
      b_ptr ↦ bi ∗ x_ptr ↦ x ∗ y_ptr ↦ y ∗
      bytesOwn bi (bs ++ u64Le (W64 ps.length) ++
        (((keys.take i).filterMap (entryAt ps l)).map
          (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2)).flatten) ∗
      [∗list] i ↦ e ∈ l, ∃ p : swift.CommandId × w64, ⌜ps[i]? = some p⌝ ∗ ⌜p.2 = e.2⌝))
    _ go.int mp dq ps) $$ [Hm]
  · iexact Hm
  iintro %keys %hk
  isplitl [Hbig Hb b y x]
  · iexists b1, _, _
    iframe
    simp only [List.take_zero, List.filterMap_nil, List.map_nil, List.flatten_nil, List.append_nil]
    iframe
  isplitr
  · iintro !> %i %key %v ⟨%hki, %hv⟩ ⟨%bi, %x', %y', Hbp, Hx, Hy, Hb, Hbig⟩
    obtain ⟨j, hj⟩ := lookupL_getElem ps key v hv
    have hjl : j < l.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨e, he⟩ : ∃ e, l[j]? = some e := ⟨l[j], List.getElem?_eq_getElem hjl⟩
    have hent : entryAt ps l key = some e := by
      rw [show key = (key, v).1 from rfl, entryAt_getElem ps l Hnd j (key, v) hj, he]
    have he1 : e.1 = goCmdIdC key := by
      have h1 : (ps.map (fun p => goCmdIdC p.1))[j]? = some (goCmdIdC key) := by simp [hj]
      rw [Hkeys] at h1
      simp [he] at h1
      exact h1
    icases (BigSepL.bigSepL_lookup_acc he).1 $$ Hbig with ⟨⟨%p, %hp, %hpe⟩, Hback⟩
    rw [hj] at hp
    cases hp
    ihave Hbig := Hback $$ %e [] 
    · iexists (key, v); iframe; ipureintro; exact ⟨hj, hpe⟩
    rw [list_set_lookup_self l j e he]
    wp_auto
    wp_apply wp_rpcEnc_swift_CommandId $$ Hb as %b2 Hb
    wp_apply wp_rpcEnc_int $$ Hb as %b3 Hb
    isplitr
    · ipureintro; rfl
    iexists b3, key, v
    iframe
    rw [filterMap_take_succ ps l keys i key e hki hent]
    have : e = (goCmdIdC key, v) := Prod.ext he1 hpe.symm
    subst this
    simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]
    iframe
  · iintro ⟨%bi, %x', %y', Hbp, Hx, Hy, Hb, Hbig⟩ Hm
    wp_auto
    iapply HΦ
    iexists keys.filterMap (entryAt ps l)
    isplitr
    · ipureintro; exact perm_filterMap_entryAt ps l Hnd hlen keys hk
    rw [List.take_of_length_le (Nat.le_refl _)]
    simp only [cList, cU64, List.append_assoc]
    rw [show (keys.filterMap (entryAt ps l)).length = ps.length by
      rw [(perm_filterMap_entryAt ps l Hnd hlen keys hk).length_eq, hlen]]
    iframe
    unfold rawMap
    iframe
    ipureintro; exact ⟨rfl, Hnd, Hkeys⟩

theorem wp_rpcEnc_map_swift_CommandId_state_Command (b : GoSlice) (bs : List w8) (mp : GoMap) (dq : DFrac)
    (l : List (CmdId × Cmd)) :
    {{ (bytesOwn b bs ∗ mapOwnC (V := state.Command) mp dq (fun c x => cmdOwnC c dq x) (some l) : IProp GF) }}
      (App (App (Val (@! rpcEnc_map_swift_CommandId_state_Command)) (Val #b)) (Val #mp))
    {{ (b' : GoSlice), RET #b'; ∃ l' : List (CmdId × Cmd), ⌜l'.Perm l⌝ ∗
        bytesOwn b' (bs ++ cList (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2) l') ∗
        mapOwnC (V := state.Command) mp dq (fun c x => cmdOwnC c dq x) (some l) }} := by
  wp_start as ⟨Hb, Hm⟩
  unfold mapOwnC
  icases Hm with ⟨%mv, %ps, Hm, %Hrep, Hbig⟩
  obtain ⟨rfl, Hnd, Hkeys⟩ := Hrep
  have hlen : ps.length = l.length := by
    have := congrArg List.length Hkeys; simpa using this
  wp_auto
  wp_apply (wp_rawMap_len (V := state.Command) mp dq ps) $$ [Hm] as ⟨Hm, %Hpl⟩
  · unfold rawMap; iexact Hm
  wp_apply wp_rpcPutU64 $$ [Hb] as %b1 Hb
  · iframe
  try wp_auto
  simp only
  wp_apply (wp_rawMap_for_range (V := state.Command)
    (fun keys i => iprop(∃ (bi : GoSlice) (x : swift.CommandId) (y : state.Command),
      b_ptr ↦ bi ∗ x_ptr ↦ x ∗ y_ptr ↦ y ∗
      bytesOwn bi (bs ++ u64Le (W64 ps.length) ++
        (((keys.take i).filterMap (entryAt ps l)).map
          (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2)).flatten) ∗
      [∗list] i ↦ e ∈ l, ∃ p : swift.CommandId × state.Command, ⌜ps[i]? = some p⌝ ∗ cmdOwnC p.2 dq e.2))
    _ state.Command.ty mp dq ps) $$ [Hm]
  · iexact Hm
  iintro %keys %hk
  isplitl [Hbig Hb b y x]
  · iexists b1, _, _
    iframe
    simp only [List.take_zero, List.filterMap_nil, List.map_nil, List.flatten_nil, List.append_nil]
    iframe
  isplitr
  · iintro !> %i %key %v ⟨%hki, %hv⟩ ⟨%bi, %x', %y', Hbp, Hx, Hy, Hb, Hbig⟩
    obtain ⟨j, hj⟩ := lookupL_getElem ps key v hv
    have hjl : j < l.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨e, he⟩ : ∃ e, l[j]? = some e := ⟨l[j], List.getElem?_eq_getElem hjl⟩
    have hent : entryAt ps l key = some e := by
      rw [show key = (key, v).1 from rfl, entryAt_getElem ps l Hnd j (key, v) hj, he]
    have he1 : e.1 = goCmdIdC key := by
      have h1 : (ps.map (fun p => goCmdIdC p.1))[j]? = some (goCmdIdC key) := by simp [hj]
      rw [Hkeys] at h1
      simp [he] at h1
      exact h1
    icases (BigSepL.bigSepL_lookup_acc he).1 $$ Hbig with ⟨⟨%p, %hp, Hr⟩, Hback⟩
    rw [hj] at hp
    cases hp

    wp_auto
    wp_apply wp_rpcEnc_swift_CommandId $$ Hb as %b2 Hb
    wp_apply wp_rpcEnc_state_Command $$ [Hb Hr] as %b3 ⟨Hb, Hr⟩
    · iframe
    try wp_auto

    ihave Hbig := Hback $$ %e [Hr]
    · iexists (key, v); iframe; ipureintro; exact hj
    rw [list_set_lookup_self l j e he]
    isplitr
    · ipureintro; rfl
    iexists b3, key, v
    iframe
    rw [filterMap_take_succ ps l keys i key e hki hent]
    obtain ⟨e1, e2⟩ := e
    simp only at he1
    subst he1
    simp only [List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]
    iframe
  · iintro ⟨%bi, %x', %y', Hbp, Hx, Hy, Hb, Hbig⟩ Hm
    wp_auto
    iapply HΦ
    iexists keys.filterMap (entryAt ps l)
    isplitr
    · ipureintro; exact perm_filterMap_entryAt ps l Hnd hlen keys hk
    rw [List.take_of_length_le (Nat.le_refl _)]
    simp only [cList, cU64, List.append_assoc]
    rw [show (keys.filterMap (entryAt ps l)).length = ps.length by
      rw [(perm_filterMap_entryAt ps l Hnd hlen keys hk).length_eq, hlen]]
    iframe
    unfold rawMap
    iframe
    ipureintro; exact ⟨rfl, Hnd, Hkeys⟩

theorem wp_rpcEnc_map_swift_CommandId_swift_Dep (b : GoSlice) (bs : List w8) (mp : GoMap) (dq : DFrac)
    (l : List (CmdId × List CmdId)) :
    {{ (bytesOwn b bs ∗ mapOwnC (V := GoSlice) mp dq (fun sl d => iprop(∃ ids : List swift.CommandId, sl ↦*{dq} ids ∗ ⌜ids.map goCmdIdC = d⌝)) (some l) : IProp GF) }}
      (App (App (Val (@! rpcEnc_map_swift_CommandId_swift_Dep)) (Val #b)) (Val #mp))
    {{ (b' : GoSlice), RET #b'; ∃ l' : List (CmdId × List CmdId), ⌜l'.Perm l⌝ ∗
        bytesOwn b' (bs ++ cList (fun p : CmdId × List CmdId => cCmdId p.1 ++ cList cCmdId p.2) l') ∗
        mapOwnC (V := GoSlice) mp dq (fun sl d => iprop(∃ ids : List swift.CommandId, sl ↦*{dq} ids ∗ ⌜ids.map goCmdIdC = d⌝)) (some l) }} := by
  wp_start as ⟨Hb, Hm⟩
  unfold mapOwnC
  icases Hm with ⟨%mv, %ps, Hm, %Hrep, Hbig⟩
  obtain ⟨rfl, Hnd, Hkeys⟩ := Hrep
  have hlen : ps.length = l.length := by
    have := congrArg List.length Hkeys; simpa using this
  wp_auto
  wp_apply (wp_rawMap_len (V := GoSlice) mp dq ps) $$ [Hm] as ⟨Hm, %Hpl⟩
  · unfold rawMap; iexact Hm
  wp_apply wp_rpcPutU64 $$ [Hb] as %b1 Hb
  · iframe
  try wp_auto
  simp only
  wp_apply (wp_rawMap_for_range (V := GoSlice)
    (fun keys i => iprop(∃ (bi : GoSlice) (x : swift.CommandId) (y : GoSlice),
      b_ptr ↦ bi ∗ x_ptr ↦ x ∗ y_ptr ↦ y ∗
      bytesOwn bi (bs ++ u64Le (W64 ps.length) ++
        (((keys.take i).filterMap (entryAt ps l)).map
          (fun p : CmdId × List CmdId => cCmdId p.1 ++ cList cCmdId p.2)).flatten) ∗
      [∗list] i ↦ e ∈ l, ∃ p : swift.CommandId × GoSlice, ⌜ps[i]? = some p⌝ ∗ (∃ ids : List swift.CommandId, p.2 ↦*{dq} ids ∗ ⌜ids.map goCmdIdC = e.2⌝)))
    _ swift.Dep.ty mp dq ps) $$ [Hm]
  · iexact Hm
  iintro %keys %hk
  isplitl [Hbig Hb b y x]
  · iexists b1, _, _
    iframe
    simp only [List.take_zero, List.filterMap_nil, List.map_nil, List.flatten_nil, List.append_nil]
    iframe
  isplitr
  · iintro !> %i %key %v ⟨%hki, %hv⟩ ⟨%bi, %x', %y', Hbp, Hx, Hy, Hb, Hbig⟩
    obtain ⟨j, hj⟩ := lookupL_getElem ps key v hv
    have hjl : j < l.length := by rw [← hlen]; exact (List.getElem?_eq_some_iff.1 hj).1
    obtain ⟨e, he⟩ : ∃ e, l[j]? = some e := ⟨l[j], List.getElem?_eq_getElem hjl⟩
    have hent : entryAt ps l key = some e := by
      rw [show key = (key, v).1 from rfl, entryAt_getElem ps l Hnd j (key, v) hj, he]
    have he1 : e.1 = goCmdIdC key := by
      have h1 : (ps.map (fun p => goCmdIdC p.1))[j]? = some (goCmdIdC key) := by simp [hj]
      rw [Hkeys] at h1
      simp [he] at h1
      exact h1
    icases (BigSepL.bigSepL_lookup_acc he).1 $$ Hbig with ⟨⟨%p, %hp, Hr⟩, Hback⟩
    rw [hj] at hp
    cases hp
    icases Hr with ⟨%ids, Hr, %Hids⟩
    wp_auto
    wp_apply wp_rpcEnc_swift_CommandId $$ Hb as %b2 Hb
    wp_apply wp_rpcEnc_swift_Dep $$ [Hb Hr] as %b3 ⟨Hb, Hr⟩
    · iframe
    try wp_auto
    ihave Hr : (∃ ids : List swift.CommandId, v ↦*{dq} ids ∗ ⌜ids.map goCmdIdC = e.2⌝ : IProp GF) $$ [Hr]
    · iexists ids; iframe; ipureintro; exact Hids
    ihave Hbig := Hback $$ %e [Hr]
    · iexists (key, v); iframe; ipureintro; exact hj
    rw [list_set_lookup_self l j e he]
    isplitr
    · ipureintro; rfl
    iexists b3, key, v
    iframe
    rw [filterMap_take_succ ps l keys i key e hki hent]
    obtain ⟨e1, e2⟩ := e
    simp only at he1 Hids
    subst he1 Hids
    simp only [cList_map, List.map_append, List.map_cons, List.map_nil, List.flatten_append, List.flatten_cons,
      List.flatten_nil, List.append_nil, List.append_assoc]
    iframe
  · iintro ⟨%bi, %x', %y', Hbp, Hx, Hy, Hb, Hbig⟩ Hm
    wp_auto
    iapply HΦ
    iexists keys.filterMap (entryAt ps l)
    isplitr
    · ipureintro; exact perm_filterMap_entryAt ps l Hnd hlen keys hk
    rw [List.take_of_length_le (Nat.le_refl _)]
    simp only [cList, cU64, List.append_assoc]
    rw [show (keys.filterMap (entryAt ps l)).length = ps.length by
      rw [(perm_filterMap_entryAt ps l Hnd hlen keys hk).length_eq, hlen]]
    iframe
    unfold rawMap
    iframe
    ipureintro; exact ⟨rfl, Hnd, Hkeys⟩

theorem mapOwnC_some_nonnull {V A : Type} [ZeroVal V] (mp : GoMap) (dq : DFrac)
    (R : V → A → IProp GF) (l : List (CmdId × A)) :
    mapOwnC mp dq R (some l) ⊢ ⌜mp ≠ map.nil⌝ := by
  unfold mapOwnC
  iintro ⟨%mv, %ps, Hm, -⟩
  ihave %H := heapPointsto_non_null _ _ _ $$ Hm
  ipureintro; exact H

theorem Option.Rel.symm_perm {A : Type} {o o' : Option (List A)} (h : Option.Rel List.Perm o o') :
    Option.Rel List.Perm o' o := by
  cases h with
  | none => exact Option.Rel.none
  | some h => exact Option.Rel.some h.symm

/-- The Go value of an `MSync` holds the wire value `m` (its maps with the fraction `dq`). -/
def syncValOwn (v : swift.MSync) (dq : DFrac) (m : SyncWire) : IProp GF :=
  iprop(⌜v.Replica' = m.rep ∧ v.Ballot' = m.bal⌝ ∗
    mapOwnC (V := w64) v.Phases' dq (fun v a => iprop(⌜v = a⌝)) m.phases ∗
    mapOwnC (V := state.Command) v.Cmds' dq (fun c x => cmdOwnC c dq x) m.cmds ∗
    mapOwnC (V := swift.Dep) v.Deps' dq
      (fun sl d => iprop(∃ ids : List swift.CommandId, sl ↦*{dq} ids ∗ ⌜ids.map goCmdIdC = d⌝)) m.deps)

theorem wp_rpcEnc_swift_MSync (b : GoSlice) (bs : List w8) (v : swift.MSync) (dq : DFrac)
    (m : SyncWire) :
    {{ (bytesOwn b bs ∗ syncValOwn v dq m : IProp GF) }}
      (App (App (Val (@! rpcEnc_swift_MSync)) (Val #b)) (Val #v))
    {{ (b' : GoSlice), RET #b'; ∃ m' : SyncWire, ⌜KitVal.equivC (.msync m) (.msync m')⌝ ∗
        bytesOwn b' (bs ++ kitBody (.msync m')) ∗ syncValOwn v dq m }} := by
  wp_start as ⟨Hb, Hv⟩
  unfold syncValOwn
  icases Hv with ⟨%Hrb, Hph, Hcm, Hdp⟩
  obtain ⟨vrep, vbal, vph, vcm, vdp⟩ := v
  simp only at Hrb
  obtain ⟨rfl, rfl⟩ := Hrb
  wp_auto
  wp_apply wp_rpcEnc_int32 $$ Hb as %b1 Hb
  wp_apply wp_rpcEnc_int32 $$ Hb as %b2 Hb
  simp only
  wp_join iprop(∃ (bi : GoSlice) (o : Option (List (CmdId × w64))),
      b_ptr ↦ bi ∗
      bytesOwn bi (bs ++ cI32 m.rep ++ cI32 m.bal ++
        cMapOpt (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) o) ∗
      ⌜Option.Rel List.Perm o m.phases⌝ ∗
      mapOwnC (V := w64) vph dq (fun v a => iprop(⌜v = a⌝)) m.phases ∗
      v_ptr ↦ (⟨m.rep, m.bal, vph, vcm, vdp⟩ : swift.MSync))
    with [b Hb Hph v] as ⟨%bi, %o, b, Hb, %Ho, Hph, v⟩
  · -- nil map
    icases Hb with ⟨Hb, Hcap⟩
    wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 0]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
    · iframe
    try wp_auto
    ihave Hb := bytesOwn_intro $$ [Hb Hcap]
    · iframe
    wp_join_done
    cases hm : m.phases with
    | some l =>
      ihave %Hnn := mapOwnC_some_nonnull _ _ _ _ $$ Hph
      exact absurd rfl Hnn
    | none =>
      iexists b', none
      simp only [cMapOpt]
      iframe
      ipureintro; exact Option.Rel.none
  · -- a map
    cases hm : m.phases with
    | none =>
      simp only [mapOwnC]
      icases Hph with %Hn
      exact absurd Hn Hif
    | some l =>
      icases Hb with ⟨Hb, Hcap⟩
      wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 1]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
      · iframe
      try wp_auto
      ihave Hb := bytesOwn_intro $$ [Hb Hcap]
      · iframe
      wp_apply (wp_rpcEnc_map_swift_CommandId_int b' (bs ++ cI32 m.rep ++ cI32 m.bal ++ [W8 1]) vph dq l)
        $$ [Hb Hph] as %b'' ⟨%l', %Hp, Hb, Hph⟩
      · iframe
      try wp_auto
      wp_join_done
      iexists b'', some l'
      iframe
      simp only [cMapOpt, cList, List.append_assoc, List.cons_append, List.nil_append]
      isplitl [Hb]
      · iexact Hb
      ipureintro; exact Option.Rel.some Hp
  wp_join iprop(∃ (bi : GoSlice) (o2 : Option (List (CmdId × Cmd))),
      b_ptr ↦ bi ∗
      bytesOwn bi (bs ++ cI32 m.rep ++ cI32 m.bal ++
        cMapOpt (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) o ++ cMapOpt (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2) o2) ∗
      ⌜Option.Rel List.Perm o2 m.cmds⌝ ∗
      mapOwnC (V := state.Command) vcm dq (fun c x => cmdOwnC c dq x) m.cmds ∗
      v_ptr ↦ (⟨m.rep, m.bal, vph, vcm, vdp⟩ : swift.MSync))
    with [b Hb Hcm v] as ⟨%bi, %o2, b, Hb, %Ho2, Hcm, v⟩
  · -- nil map
    icases Hb with ⟨Hb, Hcap⟩
    wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 0]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
    · iframe
    try wp_auto
    ihave Hb := bytesOwn_intro $$ [Hb Hcap]
    · iframe
    wp_join_done
    cases hm : m.cmds with
    | some l =>
      ihave %Hnn := mapOwnC_some_nonnull _ _ _ _ $$ Hcm
      exact absurd rfl Hnn
    | none =>
      iexists b', none
      simp only [cMapOpt]
      iframe
      ipureintro; exact Option.Rel.none
  · -- a map
    cases hm : m.cmds with
    | none =>
      simp only [mapOwnC]
      icases Hcm with %Hn
      exact absurd Hn Hif
    | some l =>
      icases Hb with ⟨Hb, Hcap⟩
      wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 1]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
      · iframe
      try wp_auto
      ihave Hb := bytesOwn_intro $$ [Hb Hcap]
      · iframe
      wp_apply (wp_rpcEnc_map_swift_CommandId_state_Command b' (bs ++ cI32 m.rep ++ cI32 m.bal ++ cMapOpt (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) o ++ [W8 1]) vcm dq l)
        $$ [Hb Hcm] as %b'' ⟨%l', %Hp, Hb, Hcm⟩
      · iframe
      try wp_auto
      wp_join_done
      iexists b'', some l'
      iframe
      simp only [cMapOpt, cList, List.append_assoc, List.cons_append, List.nil_append]
      isplitl [Hb]
      · iexact Hb
      ipureintro; exact Option.Rel.some Hp
  wp_join iprop(∃ (bi : GoSlice) (o3 : Option (List (CmdId × List CmdId))),
      b_ptr ↦ bi ∗
      bytesOwn bi (bs ++ cI32 m.rep ++ cI32 m.bal ++
        cMapOpt (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) o ++ cMapOpt (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2) o2 ++ cMapOpt (fun p : CmdId × List CmdId => cCmdId p.1 ++ cList cCmdId p.2) o3) ∗
      ⌜Option.Rel List.Perm o3 m.deps⌝ ∗
      mapOwnC (V := swift.Dep) vdp dq
        (fun sl d => iprop(∃ ids : List swift.CommandId, sl ↦*{dq} ids ∗ ⌜ids.map goCmdIdC = d⌝)) m.deps ∗
      v_ptr ↦ (⟨m.rep, m.bal, vph, vcm, vdp⟩ : swift.MSync))
    with [b Hb Hdp v] as ⟨%bi, %o3, b, Hb, %Ho3, Hdp, v⟩
  · -- nil map
    icases Hb with ⟨Hb, Hcap⟩
    wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 0]
    isplitr
    · ipureintro; rfl
    iintro %sl ⟨Hsl, -⟩
    wp_auto
    wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
    · iframe
    try wp_auto
    ihave Hb := bytesOwn_intro $$ [Hb Hcap]
    · iframe
    wp_join_done
    cases hm : m.deps with
    | some l =>
      ihave %Hnn := mapOwnC_some_nonnull _ _ _ _ $$ Hdp
      exact absurd rfl Hnn
    | none =>
      iexists b', none
      simp only [cMapOpt]
      iframe
      ipureintro; exact Option.Rel.none
  · -- a map
    cases hm : m.deps with
    | none =>
      simp only [mapOwnC]
      icases Hdp with %Hn
      exact absurd Hn Hif
    | some l =>
      icases Hb with ⟨Hb, Hcap⟩
      wp_apply wp_slice_literal (V := w8) (t := go.byte) [W8 1]
      isplitr
      · ipureintro; rfl
      iintro %sl ⟨Hsl, -⟩
      wp_auto
      wp_apply wp_slice_append $$ [Hb Hcap Hsl] as %b' ⟨Hb, Hcap, -⟩
      · iframe
      try wp_auto
      ihave Hb := bytesOwn_intro $$ [Hb Hcap]
      · iframe
      wp_apply (wp_rpcEnc_map_swift_CommandId_swift_Dep b' (bs ++ cI32 m.rep ++ cI32 m.bal ++ cMapOpt (fun p : CmdId × w64 => cCmdId p.1 ++ cU64 p.2) o ++ cMapOpt (fun p : CmdId × Cmd => cCmdId p.1 ++ cCmd p.2) o2 ++ [W8 1]) vdp dq l)
        $$ [Hb Hdp] as %b'' ⟨%l', %Hp, Hb, Hdp⟩
      · iframe
      try wp_auto
      wp_join_done
      iexists b'', some l'
      iframe
      simp only [cMapOpt, cList, List.append_assoc, List.cons_append, List.nil_append]
      isplitl [Hb]
      · iexact Hb
      ipureintro; exact Option.Rel.some Hp
  iapply HΦ
  iexists ⟨m.rep, m.bal, o, o2, o3⟩
  isplitr
  · ipureintro
    refine ⟨rfl, rfl, ?_, ?_, ?_⟩ <;> rename_i h <;> first
      | exact Option.Rel.symm_perm Ho | exact Option.Rel.symm_perm Ho2 | exact Option.Rel.symm_perm Ho3
  simp only [kitBody, SyncWire.cEnc, List.append_assoc]
  iframe
  ipureintro; trivial

theorem optionRel_perm_refl {A : Type} (o : Option (List A)) : Option.Rel List.Perm o o := by
  cases o with
  | none => exact Option.Rel.none
  | some l => exact Option.Rel.some (List.Perm.refl l)

theorem equivC_refl (x : KitVal) : KitVal.equivC x x := by
  cases x <;> simp only [KitVal.equivC] <;> first | trivial |
    exact ⟨trivial, trivial, optionRel_perm_refl _, optionRel_perm_refl _, optionRel_perm_refl _⟩

theorem structOwnC_msync (ty : go.GoType) (p : Loc) (dq : DFrac) (m : SyncWire) :
    structOwnC (GF := GF) ty p dq (.msync m) ⊣⊢ (⌜ty = swift.MSync.ty⌝ ∗
      ∃ ph cm dp : GoMap, p ↦{dq} (⟨m.rep, m.bal, ph, cm, dp⟩ : swift.MSync) ∗
        syncValOwn ⟨m.rep, m.bal, ph, cm, dp⟩ dq m) := by
  simp only [structOwnC, syncValOwn]
  constructor
  · iintro ⟨%H, %ph, %cm, %dp, Hs, H1, H2, H3⟩
    iframe %H
    iexists ph, cm, dp
    iframe
    ipureintro; exact ⟨trivial, trivial⟩
  · iintro ⟨%H, %ph, %cm, %dp, Hs, -, H1, H2, H3⟩
    iframe %H
    iexists ph, cm, dp
    iframe

set_option maxHeartbeats 2000000 in
/-- `rpcEncode`'s result: the encoding of the value up to its maps' order, the value back. -/
theorem wp_rpcEncode (v : GoInterface) (dq : DFrac) (x : KitVal) :
    {{ (kitValOwnC v dq x : IProp GF) }}
      (App (Val (@! rpcEncode)) (Val #v))
    {{ (s : GoSlice), RET #s; ∃ x' : KitVal, ⌜KitVal.equivC x x'⌝ ∗ s ↦* x'.encode ∗
        kitValOwnC v dq x }} := by
  wp_start as Hv
  unfold kitValOwnC
  icases Hv with ⟨%ty, %p, %Hp, Hs⟩
  obtain ⟨rfl, Hnn⟩ := Hp
  ihave Hnil := bytesOwn_intro slice.nil [] $$ [] 
  · isplitr
    · iapply ownSlice_nil
    iapply ownSliceCap_nil
  cases x
  case registerArgs a pt =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, Hs⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_RegisterArgs $$ Hb as %b1 Hb
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    iframe
    ipureintro; exact ⟨⟨rfl, Hnn⟩, rfl⟩
  case registerReply i ns r l =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, ⟨%sl, Hs, Hns⟩⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_RegisterReply $$ [Hb Hns] as %b1 ⟨Hb, Hns⟩
    · iframe
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iexists sl; iframe
  case getLeaderArgs =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, ⟨%sv, Hs⟩⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_GetLeaderArgs $$ Hb as %b1 Hb
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iexists sv; iframe
  case getLeaderReply i =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, Hs⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_GetLeaderReply $$ Hb as %b1 Hb
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iframe
  case getReplicaListArgs =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, ⟨%sv, Hs⟩⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_GetReplicaListArgs $$ Hb as %b1 Hb
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iexists sv; iframe
  case getReplicaListReply rs al r =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, ⟨%s1, %s2, Hs, H1, H2⟩⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_GetReplicaListReply $$ [Hb H1 H2] as %b1 ⟨Hb, H1, H2⟩
    · iframe
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iexists s1, s2; iframe
  case pingArgs a =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, Hs⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_PingArgs $$ Hb as %b1 Hb
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iframe
  case pingReply =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, ⟨%sv, Hs⟩⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_PingReply $$ Hb as %b1 Hb
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iexists sv; iframe
  case beTheLeaderArgs =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, ⟨%sv, Hs⟩⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_BeTheLeaderArgs $$ Hb as %b1 Hb
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iexists sv; iframe
  case beTheLeaderReply l n =>
    simp only [structOwnC]
    icases Hs with ⟨%Hty, Hs⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_defs_BeTheLeaderReply $$ Hb as %b1 Hb
    try wp_auto
    iapply HΦ
    iexists _
    isplitr
    · ipureintro; exact equivC_refl _
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    simp only [structOwnC]
    isplitr
    · ipureintro; trivial
    iframe
  case msync m =>
    icases (structOwnC_msync _ _ _ _).1 $$ Hs with ⟨%Hty, %ph, %cm, %dp, Hs, Hv⟩
    subst Hty
    wp_auto
    rw [decide_eq_false Hnn]
    wp_auto
    wp_apply wp_rpcPutU64 $$ [Hnil] as %b0 Hb
    · iexact Hnil
    try wp_auto
    wp_apply wp_rpcEnc_swift_MSync b0 _ ⟨m.rep, m.bal, ph, cm, dp⟩ dq m $$ [Hb Hv]
      as %b1 ⟨%m', %Hm', Hb, Hv⟩
    · iframe
    try wp_auto
    iapply HΦ
    iexists .msync m'
    isplitr
    · ipureintro; exact Hm'
    rw [encode_eq]
    simp only [KitVal.tag, cU64, List.nil_append]
    icases Hb with ⟨Hb, -⟩
    iframe Hb
    iexists _, p
    isplitr
    · ipureintro; exact ⟨rfl, Hnn⟩
    iapply (structOwnC_msync _ _ _ _).2
    isplitr
    · ipureintro; rfl
    iexists ph, cm, dp
    iframe

end wps

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
