/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/Addr.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
kit.go's address helpers on the deployment's addresses: `Addrs`, `host`, `port`, `at`,
`digits`, `nodeConfig` (specs in `ServersSpecs.lean`).
-/
module

public import Perennial.Proof.fmt
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ServersSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp
  GooseGlobalGS.gooseInvGS netShaExts_has netShaExts_hasSha256

/-- Node `i`'s first port, as text (four digits). -/
def portStr (i : Nat) : GoString :=
  [W8 (48 + nodePort i / 1000), W8 (48 + nodePort i / 100 % 10), W8 (48 + nodePort i / 10 % 10),
   W8 (48 + nodePort i % 10)]

theorem split_addr (i : Nat) (a : GoString) (ha : addrs[i]? = some a) :
    strings.split a go!":" = [nodeHost i, portStr i] := by
  match i, ha with
  | 0, ha | 1, ha | 2, ha | 3, ha | 4, ha | 5, ha | 6, ha | 7, ha | 8, ha | 9, ha | 10, ha
  | 11, ha | 12, ha =>
    simp only [addrs, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at ha
    subst ha
    simp [strings.split, strings.splitAux, nodeHost, portStr, nodePort]

/-- The value `port` computes from the digits `s`. -/
def digitsVal (s : List w8) : w64 :=
  s.foldl (fun n c => n * W64 10 + W64 (uint.Z (c - W8 48))) (W64 0)

theorem digitsVal_take_succ (s : List w8) (n : Nat) (c : w8) (h : s[n]? = some c) :
    digitsVal (s.take (n + 1)) = digitsVal (s.take n) * W64 10 + W64 (uint.Z (c - W8 48)) := by
  unfold digitsVal
  rw [List.take_add_one, h]
  simp [List.foldl_append]

theorem portStr_length (i : Nat) : (portStr i).length = 4 := rfl

theorem digitsVal_portStr (i : Nat) (hi : i < 13) :
    digitsVal (portStr i) = W64 (nodePort i) := by
  match i, hi with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ | 10, _ | 11, _
  | 12, _ => simp [digitsVal, portStr, nodePort]

theorem addrs_lt (i : Nat) (a : GoString) (ha : addrs[i]? = some a) : i < 13 := by
  have := (List.getElem?_eq_some_iff.mp ha).1; simpa [addrs] using this

section sprintf
variable [GooseExts] [GoGlobalContext] [GoSemanticsFunctions] [go.string ↓u go.string]

theorem IntArgValue.uniq_uint64' [go.IntoValInj w64] (n : w64) :
    ∀ z', fmt.IntArgValue (interface.mk go.uint64 #n) z' → z' = uint.Z n := by
  intro z' h
  obtain ⟨n', hv, rfl⟩ := fmt.IntArgValue.of_uint64 h
  rw [go.intoVal_inj hv]

/-- `Sprintf("%s:%d", x, n)` for a string `x` and a `uint64` `n` is exactly `x:n`. -/
theorem SprintfOut.str_colon_d_uint64 [go.IntoValInj GoString] [go.IntoValInj w64]
    (x : GoString) (n : w64) (out : GoString)
    (h : fmt.SprintfOut go!"%s:%d" [interface.mkOk go.string #x, interface.mkOk go.uint64 #n] out) :
    out = x ++ go!":" ++ fmt.decimal (uint.Z n) := by
  have hfmt : go!"%s:%d" = W8 37 :: W8 115 :: W8 58 :: W8 37 :: [W8 100] := rfl
  rw [hfmt] at h
  obtain ⟨o1, rfl, h1⟩ := fmt.SprintfOut.str_inv h
  obtain ⟨o2, rfl, h2⟩ := fmt.SprintfOut.byte_inv (by decide) h1
  obtain ⟨o3, rfl, h3⟩ := fmt.SprintfOut.int_inv (w := 0) (rest := []) (by decide)
    (fmt.IntArgValue.uint64 n) (IntArgValue.uniq_uint64' n) h2
  rw [fmt.SprintfOut.done_inv h3, fmt.decimalPad_zero]
  simp

end sprintf

section proof
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [SwiftNetPkgState GF] [examples.swiftnet.Assumptions]

set_option goose.wp.extras true

theorem wp_host : host.spec (GF := GF) := by
  intro i a ha
  wp_start
  wp_auto
  wp_apply strings.wp_Split a go!":" (by decide) as %sl ⟨Hsl, -⟩
  rw [split_addr i a ha]
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  have hlen : sint.Z sl.len = 2 := by
    have h1 := Hl.1; simp only [List.length_cons, List.length_nil] at h1; word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hlen]; decide⟩)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 0)) _ _ (nodeHost i) (by decide) $$ [$Hsl] as Hsl
  · ipureintro; rfl
  wp_end

theorem wp_port : port.spec (GF := GF) := by
  intro i a ha
  have hi := addrs_lt i a ha
  wp_start
  wp_auto
  wp_apply strings.wp_Split a go!":" (by decide) as %sl ⟨Hsl, -⟩
  rw [split_addr i a ha]
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  have hlen : sint.Z sl.len = 2 := by
    have h1 := Hl.1; simp only [List.length_cons, List.length_nil] at h1; word
  rw [ite_eq_left_of_eq_true _ _ (eq_true ⟨by decide, by rw [hlen]; decide⟩)]
  wp_apply wp_load_slice_index sl (sint.Z (W64 1)) _ _ (portStr i) (by decide) $$ [$Hsl] as Hsl
  · ipureintro; rfl
  ihave HI : (∃ j : w64, "i" ∷ i_ptr ↦ j ∗ "n" ∷ n_ptr ↦ digitsVal ((portStr i).take (sint.nat j)) ∗
      "%Hj" ∷ ⌜0 ≤ sint.Z j ∧ sint.Z j ≤ 4⌝ : IProp GF) $$ [«i» n]
  · iexists W64 0; iframe; ipureintro; decide
  wp_for HI
  wp_apply _root_.Perennial.github_com.mit_pdos.perennial.goose.model.strings.wp_string_len
    (portStr i) as %-
  rw [portStr_length]
  wp_if_destruct
  · have hj4 : sint.Z j < 4 := by
      have h := go.intoVal_inj Hif; simp only [decide_eq_true_eq] at h
      rw [show sint.Z (W64 ((4 : Nat) : Int)) = 4 from rfl] at h; exact h
    have hsn : sint.nat j = (sint.Z j).toNat := rfl
    have hlt : sint.nat j < (portStr i).length := by rw [portStr_length]; omega
    list_elem (portStr i) (sint.nat j) as c
    simp only [Hj.1, ite_true, Hc_lookup]
    wp_auto
    wp_for_post
    iframe
    iexists j + W64 1
    have hs1 : sint.nat (j + W64 1) = sint.nat j + 1 := by
      have : sint.nat (j + W64 1) = (sint.Z (j + W64 1)).toNat := rfl
      rw [this, hsn]; word
    rw [hs1, digitsVal_take_succ _ _ c Hc_lookup]
    iframe
    ipureintro; word
  · have hj4 : sint.Z j = 4 := by
      have h : ¬ sint.Z j < 4 := by
        intro h'; apply Hif
        rw [show sint.Z (W64 ((4 : Nat) : Int)) = 4 from rfl, decide_eq_true h']
      omega
    rw [ite_eq_right (by rw [hj4]; decide)]
    wp_auto
    have : sint.nat j = 4 := by
      have : sint.nat j = (sint.Z j).toNat := rfl
      rw [this, hj4]; rfl
    rw [this, ← portStr_length i, List.take_length, digitsVal_portStr i hi]
    wp_end

theorem wp_Addrs_servers : Addrs.spec (GF := GF) := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) addrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit_ptr ⟨Hlit, -⟩
  wp_auto
  iapply HΦ
  iexact Hlit

/-- `digits(n)`: some string (its value is not needed here). -/
theorem wp_digits (n : w64) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.imdea_software.swiftpaxos.examples.swiftnet }}
      (App (Val (@! examples.swiftnet.digits)) (Val #n))
    {{ (s : GoString), RET #s; True }} := by
  induction h : uint.nat n using Nat.strongRecOn generalizing n with
  | _ k ih =>
  wp_start
  wp_auto
  wp_if_destruct
  · wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.byte))))
      (Val (LiteralValueV _)))
    iapply wp_slice_literal (V := w8) (t := go.byte) [W8 (uint.Z (W64 48 + n))]
    wp_auto
    isplitl []
    · ipureintro; rfl
    iintro %lit_ptr ⟨Hlit, -⟩
    wp_apply wp_bytes_to_string _ [W8 (uint.Z (W64 48 + n))] $$ [$Hlit] as -
    wp_end
  · wp_apply ih (uint.nat (n / W64 10)) (by rw [← h]; word) (n / W64 10) rfl as %s1 -
    wp_apply ih (uint.nat (n % W64 10)) (by rw [← h]; word) (n % W64 10) rfl as %s2 -
    wp_end

theorem wp_at : at.spec (GF := GF) := by
  intro sl dq id off hid
  wp_start as Hsl
  ihave %Hl := ownSlice_len _ _ _ $$ Hsl
  have hlen : sint.Z sl.len = 13 := by
    have h1 := Hl.1; simp only [addrs, List.length_cons, List.length_nil] at h1; word
  obtain ⟨a, ha⟩ : ∃ a, addrs[uint.nat id]? = some a :=
    ⟨_, List.getElem?_eq_getElem (by simp [addrs]; omega)⟩
  have hsid : (sint.Z id).toNat = uint.nat id := by
    have : sint.Z id = uint.Z id := by word
    rw [this]; rfl
  have hb : 0 ≤ sint.Z id ∧ sint.Z id < sint.Z sl.len := by rw [hlen]; constructor <;> word
  wp_auto
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  wp_apply wp_load_slice_index sl (sint.Z id) _ _ a hb.1 $$ [$Hsl] as Hsl
  · ipureintro; rw [hsid]; exact ha
  wp_apply wp_host (uint.nat id) a ha
  rw [ite_eq_left_of_eq_true _ _ (eq_true hb)]
  wp_apply wp_load_slice_index sl (sint.Z id) _ _ a hb.1 $$ [$Hsl] as Hsl
  · ipureintro; rw [hsid]; exact ha
  wp_apply wp_port (uint.nat id) a ha
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.GoType.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.string #(nodeHost (uint.nat id)),
     interface.mkOk go.uint64 #(W64 (nodePort (uint.nat id) : Int) + off)]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %lit_ptr ⟨Hlit, -⟩
  wp_auto
  wp_apply fmt.wp_Sprintf_argsWf _ _ _ _
    (fmt.ArgsWf.cons_string _ _ (fmt.ArgsWf.cons_int _ _ _ (fmt.IntArgValue.uint64 _) fmt.ArgsWf.nil))
    $$ [$Hlit] as %str ⟨-, %Hout⟩
  rw [SprintfOut.str_colon_d_uint64 _ _ _ Hout,
    show nodeHost (uint.nat id) ++ go!":" ++
        fmt.decimal (uint.Z (W64 (nodePort (uint.nat id) : Int) + off))
      = atStr (uint.nat id) off from rfl]
  iapply HΦ
  iexact Hsl

theorem wp_nodeConfig : nodeConfig.spec (GF := GF) := by
  intro id port v
  wp_start
  wp_auto
  wp_apply +noauto wp_digits id as %al -
  iapply Iris.wp_fupd
  wp_auto
  ihave ⟨Hc, %Hcn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$r0»
  ihave ⟨Hp, %Hpn⟩ := typedPointsto_not_null_dup _ _ _ $$ «$v7»
  ipersist Hc
  ipersist Hp
  imodintro
  iapply HΦ
  iframe Hc
  unfold config.plain
  iexists _, _
  iframe Hc Hp
  ipureintro
  refine ⟨Hcn, Hpn, rfl, rfl, rfl, rfl, rfl, rfl⟩

end proof

end Perennial.github_com.imdea_software.swiftpaxos
