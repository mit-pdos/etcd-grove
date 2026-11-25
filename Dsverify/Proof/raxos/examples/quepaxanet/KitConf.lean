/-
The kit's configuration helpers (`kit.go`), shared by the orchestrator's and the machines' proofs:
the address lists (`CfgAddrs`, `ClientAddrs`, `Addrs`, `RecAddrs`: `portAddr`s), the configuration's
Go value (`goConf`) and its functions `choose` (any valid configuration: `rand.Intn` is
arbitrary, `RandHyp`), `encode` (`encConf`), `decode` (its inverse on valid configurations),
`String` (the log's text), `log.Println` of a string (Perennial's model of `log.Println` does
nothing), and the configuration's protocols from the shared facts (`confProto_of_shared`).
-/
module

public import Dsverify.Proof.raxos.examples.quepaxanet.KitGen
public import Dsverify.Proof.raxos.Proposer.Strings
public import Dsverify.Proof.raxos.Hyp
public import Perennial.Proof.encoding.binary.Base
public import Perennial.Proof.log.Base
public import Perennial.Proof.strings.Base
public import Dsverify.Proof.math.rand.IntnPos

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace raxos.examples.quepaxanet

open EtcdGrove github_com.mit_pdos.etcd_grove.examples.lib.remote
open raxos raxos.pure

/-! ## Addresses -/

/-- The decimal string of a port `76xx`. -/
theorem decStr_76 (m : Nat) (hm : m < 100) :
    decStr (7600 + m) = [BitVec.ofNat 8 55, BitVec.ofNat 8 54, BitVec.ofNat 8 (48 + m / 10),
      BitVec.ofNat 8 (48 + m % 10)] := by
  rw [opid.decStr_eq, opid.bstr_toString_rec, if_neg (by omega),
    opid.bstr_toString_rec ((7600 + m) / 10), if_neg (by omega),
    opid.bstr_toString_rec ((7600 + m) / 10 / 10), if_neg (by omega),
    opid.bstr_toString_rec ((7600 + m) / 10 / 10 / 10), if_pos (by omega)]
  have h1 : (7600 + m) / 10 / 10 / 10 = 7 := by omega
  have h2 : (7600 + m) / 10 / 10 % 10 = 6 := by omega
  have h3 : (7600 + m) / 10 % 10 = m / 10 := by omega
  have h4 : (7600 + m) % 10 = m % 10 := by omega
  rw [h1, h2, h3, h4]
  rfl

/-- The configuration addresses (`CfgAddrs()`), node `n`'s at index `n`. -/
def cfgAddrsL : List GoString := (List.range 12).map (fun n => portAddr (7640 + n))

theorem cfgAddrsL_lit : cfgAddrsL = [go!"127.0.0.1:7640", go!"127.0.0.1:7641",
    go!"127.0.0.1:7642", go!"127.0.0.1:7643", go!"127.0.0.1:7644", go!"127.0.0.1:7645",
    go!"127.0.0.1:7646", go!"127.0.0.1:7647", go!"127.0.0.1:7648", go!"127.0.0.1:7649",
    go!"127.0.0.1:7650", go!"127.0.0.1:7651"] := by
  simp only [cfgAddrsL, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.cons_append, portAddr]
  simp only [show ∀ n, 7640 + n = 7600 + (40 + n) from fun n => by omega]
  rw [decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega)]

/-- Node `n`'s configuration address, `1 ≤ n ≤ 11`: a client machine's (`cconfAddr (n - 1)`) or a
server machine's (`confAddr (n - 6)`). -/
theorem cfgAddrsL_get (n : Nat) (hn : n < 12) : cfgAddrsL[n]? = some (portAddr (7640 + n)) := by
  simp [cfgAddrsL, hn]

theorem cconfAddr_eq (c : Nat) : cconfAddr c = portAddr (7640 + (1 + c)) := by
  unfold cconfAddr; congr 1; omega

theorem confAddr_eq (k : Nat) : confAddr k = portAddr (7640 + (6 + k)) := by
  unfold confAddr; congr 1; omega

/-- The proxies' addresses (`Addrs()`), node `n`'s at index `n`. -/
def addrsL : List GoString := (List.range 12).map (fun n => portAddr (7600 + n))

/-- The recorders' addresses (`RecAddrs()`), node `n`'s at index `n`. -/
def recAddrsL : List GoString := (List.range 12).map (fun n => portAddr (7620 + n))

theorem addrsL_lit : addrsL = [go!"127.0.0.1:7600", go!"127.0.0.1:7601",
    go!"127.0.0.1:7602", go!"127.0.0.1:7603", go!"127.0.0.1:7604", go!"127.0.0.1:7605",
    go!"127.0.0.1:7606", go!"127.0.0.1:7607", go!"127.0.0.1:7608", go!"127.0.0.1:7609",
    go!"127.0.0.1:7610", go!"127.0.0.1:7611"] := by
  simp only [addrsL, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.cons_append, portAddr]
  rw [decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega)]

theorem recAddrsL_lit : recAddrsL = [go!"127.0.0.1:7620", go!"127.0.0.1:7621",
    go!"127.0.0.1:7622", go!"127.0.0.1:7623", go!"127.0.0.1:7624", go!"127.0.0.1:7625",
    go!"127.0.0.1:7626", go!"127.0.0.1:7627", go!"127.0.0.1:7628", go!"127.0.0.1:7629",
    go!"127.0.0.1:7630", go!"127.0.0.1:7631"] := by
  simp only [recAddrsL, List.range_succ, List.range_zero, List.nil_append, List.map_append,
    List.map_cons, List.map_nil, List.cons_append, portAddr]
  simp only [show ∀ n, 7620 + n = 7600 + (20 + n) from fun n => by omega]
  rw [decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega),
    decStr_76 _ (by omega), decStr_76 _ (by omega), decStr_76 _ (by omega)]

theorem addrsL_get (n : Nat) (hn : n < 12) : addrsL[n]? = some (portAddr (7600 + n)) := by
  simp [addrsL, hn]

theorem recAddrsL_get (n : Nat) (hn : n < 12) : recAddrsL[n]? = some (portAddr (7620 + n)) := by
  simp [recAddrsL, hn]

theorem digit_ne_colon (m : Nat) (hm : m < 10) : BitVec.ofNat 8 (48 + m) ≠ (58#8 : w8) := by
  intro h
  have := congrArg BitVec.toNat h
  simp at this
  omega

/-- `strings.Split` of a port address at `":"`: the IP and the port's digits. -/
theorem split_portAddr (m : Nat) (hm : m < 100) :
    strings.split (portAddr (7600 + m)) go!":" = [go!"127.0.0.1", decStr (7600 + m)] := by
  unfold portAddr
  rw [decStr_76 m hm]
  have h1 := digit_ne_colon (m / 10) (by omega)
  have h2 := digit_ne_colon (m % 10) (by omega)
  simp [strings.split, strings.splitAux, h1, h2, Ne.symm h1, Ne.symm h2]

/-! ## The configuration's value -/

/-- A configuration's Go value (`Conf`). -/
def goConf [GooseExts] (c : QConf) : raxos.examples.quepaxanet.Conf :=
  ⟨W64 c.n, W64 c.se, W64 c.pipe, W64 c.ep, W64 c.tmo⟩

instance Conf.countable [GooseExts] : Pos.Countable raxos.examples.quepaxanet.Conf :=
  .ofInjective (fun v => Pos.Countable.encode (v.N', v.ServerMode', v.Pipeline', v.Epoch',
    v.TimeoutUs'))
    (by rintro ⟨⟩ ⟨⟩ h; have h := Pos.encode_inj h; simp_all)

theorem w8_small (x : Nat) (hx : x < 256) : uint.Z (W8 (x : Int)) = x := by
  simp only [uint.Z, W8, BitVec.toNat_ofInt]
  omega

/-- `decode`'s value of a valid configuration's bytes. -/
theorem decode_val [GooseExts] (c : QConf) (hc : c.ok) :
    raxos.examples.quepaxanet.Conf.mk (W64 (uint.Z (W8 (c.n : Int)))) (W64 (uint.Z (W8 (c.se : Int))))
      (W64 (uint.Z (W8 (c.pipe : Int)))) (W64 (uint.Z (W8 (c.ep : Int))))
      (W64 5000 * W64 (uint.Z (W8 ((c.tmo : Int) / 5000)))) = goConf c := by
  obtain ⟨hn, hse, hp1, hp2, he1, he2, ht1, ht2, ht3⟩ := hc
  have hn' : c.n < 256 := by omega
  have ht : ((c.tmo : Int) / 5000) = ((c.tmo / 5000 : Nat) : Int) := by omega
  unfold goConf
  rw [w8_small _ hn', w8_small _ (by omega), w8_small _ (by omega), w8_small _ (by omega), ht,
    w8_small _ (by omega)]
  congr 1
  have : c.tmo = 5000 * (c.tmo / 5000) := by omega
  conv => rhs; rw [this]
  word

theorem uZ1 : uint.Z (W64 1) = 1 := rfl
theorem uZ5 : uint.Z (W64 5) = 5 := rfl
theorem uZ5000 : uint.Z (W64 5000) = 5000 := rfl
theorem uZ40000 : uint.Z (W64 40000) = 40000 := rfl

open scoped encoding.binary

set_option hygiene false in
/-- `decode`'s checks of a valid configuration: each `if` takes its true branch. -/
local macro "dec_rest" : tactic => `(tactic|
  (repeat (wp_if_destruct <;> (try (exfalso; revert Hif; simp (disch := omega) only [hz, uZ1, uZ5, uZ5000, uZ40000]; omega)))))

section wps
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem' : raxos.examples.quepaxanet.Assumptions]

local notation "kpkg" => pkg_id.raxos.examples.quepaxanet

set_option goose.wp.extras true

/-- `Addrs()` returns a new slice of the proxies' addresses. -/
theorem wp_Addrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.Addrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* addrsL }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) addrsL
  wp_auto
  isplitl []
  · ipureintro; rw [addrsL_lit]; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `CfgAddrs()` returns a new slice of the configuration addresses. -/
theorem wp_CfgAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.CfgAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* cfgAddrsL }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) cfgAddrsL
  wp_auto
  isplitl []
  · ipureintro; rw [cfgAddrsL_lit]; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `ClientAddrs()` returns a new slice of the client machines' addresses. -/
theorem wp_ClientAddrs :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.ClientAddrs)) (Val #()))
    {{ (sl : GoSlice), RET #sl; sl ↦* clientAddrs }} := by
  wp_start as -
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.string))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoString) (t := go.string) clientAddrs
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iexact Hsl

/-- `attempt()`: some duration. -/
theorem wp_attempt :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.attempt)) (Val #()))
    {{ (d : w64), RET #d; True }} := by
  wp_start
  wp_auto
  iapply HΦ
  itrivial

/-- `choose()`: a valid configuration (`rand.Intn` is arbitrary). -/
theorem wp_choose [hr : hyp.RandHyp GF] :
    {{ isPkgInit (PROP := IProp GF) kpkg }}
      (App (Val (@! raxos.examples.quepaxanet.choose)) (Val #()))
    {{ (c : QConf), RET #(goConf c); ⌜c.ok⌝ }} := by
  wp_start
  ihave #Hr : isPkgInit (PROP := IProp GF) pkg_id.math.rand $$ []
  · iPkgInit
  wp_auto
  wp_apply _root_.Perennial.math.rand.wp_Intn_pos (GF := GF) (W64 2) (by decide) $$ [$Hr] as %x1 %Hx1
  have key : ∀ nv : w64, (nv = W64 3 ∨ nv = W64 5) → ∀ x2 x3 x4 x5 : w64,
      0 ≤ sint.Z x2 ∧ sint.Z x2 < sint.Z (W64 2) → 0 ≤ sint.Z x3 ∧ sint.Z x3 < sint.Z (W64 5) →
      0 ≤ sint.Z x4 ∧ sint.Z x4 < sint.Z (W64 5) → 0 ≤ sint.Z x5 ∧ sint.Z x5 < sint.Z (W64 8) →
      ∃ c : QConf, c.ok ∧ goConf c = ⟨nv, x2, W64 1 + x3, W64 1 + x4, W64 5000 + W64 5000 * x5⟩ := by
    intro nv hN x2 x3 x4 x5 h2 h3 h4 h5
    refine ⟨⟨uint.nat nv, uint.nat x2, 1 + uint.nat x3, 1 + uint.nat x4, 5000 + 5000 * uint.nat x5⟩, ?_, ?_⟩
    · unfold QConf.ok; simp only
      refine ⟨by rcases hN with rfl | rfl <;> decide, by word, by omega, by word, by omega, by word, by omega, by word, by omega⟩
    · unfold goConf; simp only
      congr 1 <;> word
  wp_if_destruct
  all_goals
    (try wp_auto)
    wp_apply _root_.Perennial.math.rand.wp_Intn_pos (GF := GF) (W64 2) (by decide) $$ [$Hr] as %x2 %Hx2
    wp_apply _root_.Perennial.math.rand.wp_Intn_pos (GF := GF) (W64 5) (by decide) $$ [$Hr] as %x3 %Hx3
    wp_apply _root_.Perennial.math.rand.wp_Intn_pos (GF := GF) (W64 5) (by decide) $$ [$Hr] as %x4 %Hx4
    wp_apply _root_.Perennial.math.rand.wp_Intn_pos (GF := GF) (W64 8) (by decide) $$ [$Hr] as %x5 %Hx5
  · obtain ⟨c, hc, hcv⟩ := key (W64 5) (by simp) x2 x3 x4 x5 Hx2 Hx3 Hx4 Hx5
    rw [← hcv]
    iapply HΦ; ipureintro; exact hc
  · obtain ⟨c, hc, hcv⟩ := key (W64 3) (by simp) x2 x3 x4 x5 Hx2 Hx3 Hx4 Hx5
    rw [← hcv]
    iapply HΦ; ipureintro; exact hc

/-- `c.encode()`: the configuration's five bytes. -/
theorem wp_encode (cp : Loc) (c : QConf) (hc : c.ok) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ cp ↦ goConf c }}
      (App (Val (cp @!! go.GoType.PointerType raxos.examples.quepaxanet.Conf.ty @!! go!"encode"))
        (Val #()))
    {{ (b : GoSlice), RET #b; cp ↦ goConf c ∗ b ↦* encConf c }} := by
  wp_start as Hc
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_slice_literal (V := w8) [W8 (uint.Z (W64 c.n)), W8 (uint.Z (W64 c.se)),
    W8 (uint.Z (W64 c.pipe)), W8 (uint.Z (W64 c.ep)), W8 (uint.Z (W64 c.tmo / W64 5000))]
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  have he : ([W8 (uint.Z (W64 c.n)), W8 (uint.Z (W64 c.se)),
    W8 (uint.Z (W64 c.pipe)), W8 (uint.Z (W64 c.ep)), W8 (uint.Z (W64 c.tmo / W64 5000))] : List w8)
      = encConf c := by
    obtain ⟨hn, hse, hp1, hp2, he1, he2, ht1, ht2, -⟩ := hc
    unfold encConf
    simp only [List.cons.injEq, and_true]
    refine ⟨by word, by word, by word, by word, ?_⟩
    have : W64 c.tmo / W64 5000 = W64 (c.tmo / 5000 : Nat) := by word
    rw [this]; word
  rw [he]
  iapply HΦ; iframe

/-- `c.String()`: some string. -/
theorem wp_String (cp : Loc) (c : QConf) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ cp ↦ goConf c }}
      (App (Val (cp @!! go.GoType.PointerType raxos.examples.quepaxanet.Conf.ty @!! go!"String"))
        (Val #()))
    {{ (s : GoString), RET #s; cp ↦ goConf c }} := by
  wp_start as Hc
  wp_auto
  wp_method_call
  wp_call
  wp_auto
  wp_apply wp_digits
  wp_apply wp_digits
  wp_apply wp_digits
  wp_apply wp_digits
  wp_apply wp_digits
  iapply HΦ; iframe

/-- `decode(b)` on a valid configuration's five bytes: the configuration, valid. -/
theorem wp_decode (c : QConf) (hc : c.ok) (b : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) kpkg ∗ b ↦* encConf c }}
      (App (Val (@! raxos.examples.quepaxanet.decode)) (Val #b))
    {{ RET (PairV #(goConf c) #true); b ↦* encConf c }} := by
  wp_start as Hb
  ihave %Hlen := ownSlice_len _ _ _ $$ Hb
  unfold encConf at Hlen ⊢
  simp only [List.length_cons, List.length_nil] at Hlen
  wp_auto
  idx_if
  wp_apply wp_load_slice_index b _ _ _ (W8 c.n) (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ _ (W8 c.se) (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ _ (W8 c.pipe) (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ _ (W8 c.ep) (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  idx_if
  wp_apply wp_load_slice_index b _ _ _ (W8 (c.tmo / 5000)) (by decide) $$ [Hb] with Hb
  · iframe Hb; ipureintro; rfl
  (try wp_auto)
  obtain ⟨hn, hse, hp1, hp2, he1, he2, ht1, ht2, ht3⟩ := hc
  have hb : ∀ x : Nat, x < 256 → W64 (uint.Z (W8 (x : Int))) = W64 (x : Int) := fun x hx => by
    rw [w8_small x hx]
  have htm : W64 5000 * W64 (uint.Z (W8 ((c.tmo : Int) / 5000))) = W64 (c.tmo : Int) := by
    have ht : ((c.tmo : Int) / 5000) = ((c.tmo / 5000 : Nat) : Int) := by omega
    rw [ht, w8_small _ (by omega)]
    have : c.tmo = 5000 * (c.tmo / 5000) := by omega
    conv => rhs; rw [this]
    word
  rw [hb c.n (by omega), hb c.se (by omega), hb c.pipe (by omega), hb c.ep (by omega), htm]
  have hz : ∀ x : Nat, x < 2 ^ 64 → uint.Z (W64 (x : Int)) = x := fun x hx => by
    simp only [uint.Z, W64, BitVec.toNat_ofInt]; omega
  have hn' : W64 (c.n : Int) = W64 3 ∨ W64 (c.n : Int) = W64 5 := by
    rcases hn with h | h <;> rw [h] <;> simp
  wp_if_destruct
  · dec_rest
    unfold goConf at *; iapply HΦ $$ Hb
  · have H3 := Hif
    wp_if_destruct
    · dec_rest
      unfold goConf at *; iapply HΦ $$ Hb
    · exfalso; rcases hn' with h | h
      · exact H3 h
      · exact Hif h
  done

/-- `log.Println(s)` of a string (Perennial's model of `log.Println` does nothing; Go formats a
string operand without calling any method). -/
theorem wp_log_Println [log.Assumptions] (s : GoString) (sl : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.log ∗ sl ↦* [interface.mkOk go.string #s] }}
      (App (Val (@! Perennial.log.Println)) (Val #sl))
    {{ RET #(); True }} := by
  wp_start as -
  wp_end

end wps

end raxos.examples.quepaxanet
end Perennial
