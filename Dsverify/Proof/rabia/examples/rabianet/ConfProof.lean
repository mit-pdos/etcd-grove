/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/examples/rabianet/{Configure,SendConf,
AwaitConf,New}.lean`, run `rabia-r1wake-1`, onto this kit's Go and `Net/`.)

The kit's configuration protocol (`kit.go`): `batchSize`, `batchMs`, `blocks`, `configure` (from
`Conf`'s points-to), `choose` (`math/rand.Intn`: any value), `encode`, `decode`, `digit(s)`,
`String`, `sendConf` (dial, write the five bytes, read the acknowledgment, close), `send`, `New`
(`setCfg`), `awaitConf` (listen, retrying; accept and answer every configuration it reads),
`waitConf`.
-/
module

public import Dsverify.Proof.rabia.examples.rabianet.Kit
public import Dsverify.Proof.rabia.examples.rabianet.ConnReadFull
public import Dsverify.Proof.rabia.internal.config.CalcConstants
public import Dsverify.Proof.math.rand.Spec
public import Dsverify.Proof.log.Spec
public import Net.Proof.net.Dial
public import Net.Proof.net.Listen
public import Net.Proof.net.Listener__Accept
public import Net.Proof.net.Conn__Write
public import Net.Proof.net.Conn__Close
public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.wire.Pkg
public import Perennial.Proof.time

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.rabia.examples.rabianet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode model Net rabia.internal.message
  rabia.internal.config rabia.internal.tcp rabia

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.examples.rabianet.Assumptions]
variable [math.rand.Hyps GF] [log.Hyps GF]
variable [_root_.Perennial.io.Assumptions] [net.Assumptions] [net.FieldAssumptions] [go.BasicIntoValInj]

def confPre (cf : RCfg) (ps : GoSlice) : Config :=
  { Role' := go!"svr", Id' := (zeroValDef : Config).Id', ControllerAddr' := (zeroValDef : Config).ControllerAddr',
    ProjectFolder' := go!"/tmp/rabia-net",
    LogLevel' := go!"warn", SvrIp' := (zeroValDef : Config).SvrIp', ProxyPort' := (zeroValDef : Config).ProxyPort',
    NetworkPort' := (zeroValDef : Config).NetworkPort', Peers' := ps,
    ProxyAddr' := (zeroValDef : Config).ProxyAddr', ClosedLoop' := true, NServers' := W64 cf.n,
    NFaulty' := W64 cf.f,
    NClients' := W64 6, NConcurrency' := W64 1, NClientRequests' := W64 8,
    ClientThinkTime' := W64 0, ClientBatchSize' := W64 1, ProxyBatchSize' := W64 cf.batchSize,
    ProxyBatchTimeout' := W64 cf.batchMs * W64 1000000, NetworkBatchSize' := W64 0,
    NetworkBatchTimeout' := W64 0, NMinusF' := (zeroValDef : Config).NMinusF', Majority' := (zeroValDef : Config).Majority',
    MajorityPlusF' := (zeroValDef : Config).MajorityPlusF', FaultyPlusOne' := (zeroValDef : Config).FaultyPlusOne',
    LenLedger' := (zeroValDef : Config).LenLedger',
    LenBlockArray' := (zeroValDef : Config).LenBlockArray', LenChannel' := (zeroValDef : Config).LenChannel',
    LenPQueue' := (zeroValDef : Config).LenPQueue',
    IoBufSize' := (zeroValDef : Config).IoBufSize', TcpBufSize' := (zeroValDef : Config).TcpBufSize', KeyLen' := (zeroValDef : Config).KeyLen',
    ValLen' := (zeroValDef : Config).ValLen', SvrLogInterval' := (zeroValDef : Config).SvrLogInterval',
    ClientLogInterval' := (zeroValDef : Config).ClientLogInterval', ClientTimeout' := W64 0,
    ConsensusStartAfter' := (zeroValDef : Config).ConsensusStartAfter', StorageMode' := (zeroValDef : Config).StorageMode',
    RedisAddr' := (zeroValDef : Config).RedisAddr' }

set_option goose.wp.extras true in
/-- `batchSize(i)`. -/
theorem batchSize.wp_proof (cf : RCfg) (hi : cf.batch < 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet }}
      (App (Val (@! rabia.examples.rabianet.batchSize)) (Val #(W64 cf.batch)))
    {{ RET #(W64 cf.batchSize); True }} := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [W64 1, W64 2, W64 3, W64 10]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hiz : sint.Z (W64 cf.batch) = cf.batch := by word
  obtain ⟨h1, h2⟩ := Hlen
  simp only [List.length_cons, List.length_nil] at h1 h2
  rw [ite_eq_left (by rw [hiz]; constructor <;> word)]
  wp_apply wp_load_slice_index _ _ _ _ (W64 cf.batchSize) (by word) $$ [$Hsl] as -
  · ipureintro; rw [hiz, Int.toNat_natCast]
    unfold RCfg.batchSize
    generalize cf.batch = i at hi ⊢
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  iapply HΦ; itrivial

set_option goose.wp.extras true in
/-- `batchMs(i)`. -/
theorem batchMs.wp_proof (cf : RCfg) (hi : cf.bms < 5) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet }}
      (App (Val (@! rabia.examples.rabianet.batchMs)) (Val #(W64 cf.bms)))
    {{ RET #(W64 cf.batchMs); True }} := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [W64 1, W64 2, W64 5, W64 10, W64 50]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hiz : sint.Z (W64 cf.bms) = cf.bms := by word
  obtain ⟨h1, h2⟩ := Hlen
  simp only [List.length_cons, List.length_nil] at h1 h2
  rw [ite_eq_left (by rw [hiz]; constructor <;> word)]
  wp_apply wp_load_slice_index _ _ _ _ (W64 cf.batchMs) (by word) $$ [$Hsl] as -
  · ipureintro; rw [hiz, Int.toNat_natCast]
    unfold RCfg.batchMs
    generalize cf.bms = i at hi ⊢
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with rfl | rfl | rfl | rfl | rfl <;> rfl
  iapply HΦ; itrivial

set_option goose.wp.extras true in
/-- `blocks(i)`. -/
theorem blocks.wp_proof (cf : RCfg) (hi : cf.blocks < 4) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet }}
      (App (Val (@! rabia.examples.rabianet.blocks)) (Val #(W64 cf.blocks)))
    {{ RET #(W64 cf.blockLen); True }} := by
  wp_start
  wp_auto
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.uint64)))) (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := w64) (t := go.uint64) [W64 2, W64 3, W64 5, W64 10]
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  ihave %Hlen := ownSlice_len _ _ _ $$ Hsl
  have hiz : sint.Z (W64 cf.blocks) = cf.blocks := by word
  obtain ⟨h1, h2⟩ := Hlen
  simp only [List.length_cons, List.length_nil] at h1 h2
  rw [ite_eq_left (by rw [hiz]; constructor <;> word)]
  wp_apply wp_load_slice_index _ _ _ _ (W64 cf.blockLen) (by word) $$ [$Hsl] as -
  · ipureintro; rw [hiz, Int.toNat_natCast]
    unfold RCfg.blockLen
    generalize cf.blocks = i at hi ⊢
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
  iapply HΦ; itrivial

/-- `CalcConstants`' fields at a configuration `choose` can pick, then `LenBlockArray`. -/
theorem confVal_eq (cf : RCfg) (hc : cf.Ok) (ps : GoSlice) :
    { confPre cf ps with
      NMinusF' := (confPre cf ps).NServers' - (confPre cf ps).NFaulty',
      Majority' := (confPre cf ps).NServers'.sdiv (W64 2) + W64 1,
      MajorityPlusF' := (confPre cf ps).NServers'.sdiv (W64 2) + (confPre cf ps).NFaulty' + W64 1,
      FaultyPlusOne' := (confPre cf ps).NFaulty' + W64 1,
      NClientRequests' := if (confPre cf ps).NClientRequests' = W64 0 then W64 10000000
        else (confPre cf ps).NClientRequests',
      LenLedger' := W32 10000, LenBlockArray' := W64 cf.blockLen, LenChannel' := W64 500000,
      IoBufSize' := W64 16384000, TcpBufSize' := W64 7000000, KeyLen' := W64 8,
      ValLen' := W64 8, SvrLogInterval' := W64 4000000000,
      ClientLogInterval' := W64 15000000000, ConsensusStartAfter' := W64 0,
      StorageMode' := W64 0 } = confVal cf ps := by
  obtain ⟨n, f, ba, bm, bl⟩ := cf
  simp only [RCfg.Ok] at hc
  obtain ⟨hnf, -, hbm, -⟩ := hc
  have hms : W64 (([1, 2, 5, 10, 50] : List Nat).getD bm 0 : Nat) * W64 1000000 =
      W64 ((([1, 2, 5, 10, 50] : List Nat).getD bm 0) * 1000000 : Nat) := by
    rcases (show bm = 0 ∨ bm = 1 ∨ bm = 2 ∨ bm = 3 ∨ bm = 4 by omega) with
      rfl | rfl | rfl | rfl | rfl <;> decide
  rcases hnf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [confPre, confVal, RCfg.q, RCfg.maj, RCfg.mpf, RCfg.fp1, RCfg.batchMs, hms] <;>
    rfl

set_option goose.wp.extras true in
theorem wp_configure (ps : GoSlice) (cf : RCfg) (hc : cf.Ok) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗
        (globalAddr rabia.internal.config.Conf ↦ (zeroValDef : rabia.internal.config.Config)) }}
      (App (App (Val (@! rabia.examples.rabianet.configure)) (Val #ps)) (Val #(confV cf)))
    {{ RET #(); globalAddr rabia.internal.config.Conf ↦ confVal cf ps }} := by
  wp_start as Hc
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hc
  iStructNamed Hc
  rw [show rabia.examples.rabianet.ProjectFolder = #(go!"/tmp/rabia-net") from rfl]
  wp_auto
  wp_apply batchSize.wp_proof cf hc.2.1
  wp_apply batchMs.wp_proof cf hc.2.2.1
  ihave Hc : globalAddr rabia.internal.config.Conf ↦ confPre cf ps $$ [-HΦ c conf]
  · iapply typedPointsto_combine _ _ _ Hnn
    dsimp only [TypedPointsto.typedPointstoDef, rabia.internal.config.Config.Config_typed_pointsto,
      confPre]
    iFrameNamed
  wp_apply Config.CalcConstants.wp_proof (globalAddr rabia.internal.config.Conf) (confPre cf ps) $$ [Hc] as Hc
  · iexact Hc
  wp_apply blocks.wp_proof cf hc.2.2.2
  iStructNamed Hc
  iapply HΦ
  rw [← confVal_eq cf hc ps]
  iapply typedPointsto_combine _ _ _ Hnn
  dsimp only [TypedPointsto.typedPointstoDef, rabia.internal.config.Config.Config_typed_pointsto,
    confPre]
  iFrameNamed
  iExactEq NClientRequests
  rfl

set_option goose.wp.extras true in
/-- `choose()`: some configuration `choose` can pick. -/
theorem choose.wp_proof :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet }}
      (App (Val (@! rabia.examples.rabianet.choose)) (Val #()))
    {{ (cf : RCfg), RET #(confV cf); ⌜cf.Ok⌝ }} := by
  wp_start
  wp_auto
  wp_apply math.rand.Intn.wp_proof (W64 3) (by decide) as %s %Hs
  have hs : s = W64 0 ∨ s = W64 1 ∨ s = W64 2 := by
    have h1 : sint.Z s = 0 ∨ sint.Z s = 1 ∨ sint.Z s = 2 := by
      have : sint.Z (W64 3) = 3 := rfl; omega
    rcases h1 with h | h | h
    · left; apply BitVec.eq_of_toInt_eq; exact h
    · right; left; apply BitVec.eq_of_toInt_eq; exact h
    · right; right; apply BitVec.eq_of_toInt_eq; exact h
  have key : ∀ (n f : Nat), ((n = 3 ∧ f = 1) ∨ (n = 5 ∧ f = 1) ∨ (n = 5 ∧ f = 2)) →
      ∀ (a b c : w64), (0 ≤ sint.Z a ∧ sint.Z a < 4) → (0 ≤ sint.Z b ∧ sint.Z b < 5) →
        (0 ≤ sint.Z c ∧ sint.Z c < 4) →
      ∃ cf : RCfg, cf.Ok ∧ confV cf = ⟨W64 (n : Int), W64 (f : Int), a, b, c⟩ := by
    intro n f hnf a b c ha hb hc
    refine ⟨⟨n, f, uint.nat a, uint.nat b, uint.nat c⟩, ?_, ?_⟩
    · simp only [RCfg.Ok]; refine ⟨hnf, ?_, ?_, ?_⟩ <;> word
    · simp only [confV]; congr 1 <;> word
  rcases hs with rfl | rfl | rfl
  all_goals
    wp_auto
    wp_apply math.rand.Intn.wp_proof (W64 4) (by decide) as %a %Ha
    wp_apply math.rand.Intn.wp_proof (W64 5) (by decide) as %b %Hb
    wp_apply math.rand.Intn.wp_proof (W64 4) (by decide) as %c %Hc
    rw [show sint.Z (W64 4) = 4 from rfl] at Ha Hc
    rw [show sint.Z (W64 5) = 5 from rfl] at Hb
    first
    | (obtain ⟨cf, hok, hv⟩ := key 3 1 (by decide) a b c Ha Hb Hc
       rw [show (⟨W64 3, W64 1, a, b, c⟩ : Conf) = confV cf from hv.symm]
       iapply HΦ; ipureintro; exact hok)
    | (obtain ⟨cf, hok, hv⟩ := key 5 1 (by decide) a b c Ha Hb Hc
       rw [show (⟨W64 5, W64 1, a, b, c⟩ : Conf) = confV cf from hv.symm]
       iapply HΦ; ipureintro; exact hok)
    | (obtain ⟨cf, hok, hv⟩ := key 5 2 (by decide) a b c Ha Hb Hc
       rw [show (⟨W64 5, W64 2, a, b, c⟩ : Conf) = confV cf from hv.symm]
       iapply HΦ; ipureintro; exact hok)

set_option goose.wp.extras true in
/-- `conf.encode()` (through `*Conf`): the five bytes `RCfg.enc`. -/
theorem encode.wp_proof (l : Loc) (cf : RCfg) (hc : cf.Ok) :
    {{ (l ↦ confV cf : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType Conf.ty @!! go!"encode")) (Val #()))
    {{ (sl : GoSlice), RET #sl; l ↦ confV cf ∗ sl ↦* cf.enc }} := by
  wp_start as Hl
  wp_auto
  wp_method_call
  wp_auto
  have hw8 : ∀ x : Nat, x < 256 → W8 (uint.Z (W64 (x : Int))) = BitVec.ofNat 8 x := by
    intro x hx; word
  have hok := hc
  simp only [RCfg.Ok] at hok
  rw [hw8 cf.n (by omega), hw8 cf.f (by omega), hw8 cf.batch (by omega), hw8 cf.bms (by omega),
    hw8 cf.blocks (by omega)]
  wp_apply wp_slice_literal (V := w8) (t := go.byte) cf.enc
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, -⟩
  wp_auto
  iapply HΦ
  iframe

set_option goose.wp.extras true in
theorem digit.wp_conf (n : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.digit)) (Val #n))
    {{ RET #([BitVec.ofNat 8 (48 + uint.nat n % 10)] : GoString); True }} := by
  wp_start
  wp_auto
  wp_apply wp_slice_literal (V := w8) (t := go.byte) _
  isplitr
  · ipureintro; rfl
  iintro %sl ⟨Hsl, _⟩
  wp_apply wp_bytes_to_string $$ Hsl as Hsl
  have e : W8 (uint.Z (W64 48 + n % W64 10)) = BitVec.ofNat 8 (48 + uint.nat n % 10) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat]
    word
  rw [e]
  iapply HΦ; itrivial

set_option goose.wp.extras true in
/-- `digits(n)`: some string (`n` in decimal; only logged). -/
theorem digits.wp_conf (n : w64) :
    {{ (True : IProp GF) }}
      (App (Val (@! rabia.examples.rabianet.digits)) (Val #n))
    {{ (s : GoString), RET #s; True }} := by
  induction h : uint.nat n using Nat.strongRecOn generalizing n with
  | ind m ih =>
  wp_start
  wp_auto
  wp_if_destruct
  · wp_apply digit.wp_conf
    iapply HΦ; itrivial
  · have hlt : uint.nat (n / W64 10) < m := by rw [← h]; simp at Hif; word
    wp_apply ih _ hlt (n / W64 10) rfl as %s1 -
    wp_apply digit.wp_conf
    iapply HΦ; itrivial

set_option goose.wp.extras true in
/-- `conf.String()` (through `*Conf`): some string (only logged). -/
theorem String.wp_proof (l : Loc) (cf : RCfg) (hc : cf.Ok) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗ (l ↦ confV cf : IProp GF) }}
      (App (Val (l @!! go.GoType.PointerType Conf.ty @!! go!"String")) (Val #()))
    {{ (s : GoString), RET #s; l ↦ confV cf }} := by
  wp_start as Hl
  wp_auto
  wp_method_call
  wp_auto
  wp_apply digits.wp_conf as %s1 -
  wp_apply digits.wp_conf as %s2 -
  wp_apply batchSize.wp_proof cf hc.2.1
  wp_apply digits.wp_conf as %s3 -
  wp_apply batchMs.wp_proof cf hc.2.2.1
  wp_apply digits.wp_conf as %s4 -
  wp_apply blocks.wp_proof cf hc.2.2.2
  wp_apply digits.wp_conf as %s5 -
  iapply HΦ
  iframe

set_option goose.wp.extras true in
/-- `decode(b)` of a recorded configuration's encoding: the configuration, accepted. -/
theorem decode.wp_proof (b : GoSlice) (dq : DFrac) (cf : RCfg) (hc : cf.Ok) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗ b ↦*{dq} cf.enc }}
      (App (Val (@! rabia.examples.rabianet.decode)) (Val #b))
    {{ RET (PairV #(confV cf) #true); b ↦*{dq} cf.enc }} := by
  wp_start as Hb
  obtain ⟨n, f, ba, bm, bl⟩ := cf
  have henc : RCfg.enc ⟨n, f, ba, bm, bl⟩ = [BitVec.ofNat 8 n, BitVec.ofNat 8 f, BitVec.ofNat 8 ba,
    BitVec.ofNat 8 bm, BitVec.ofNat 8 bl] := rfl
  rw [henc]
  ihave %Hbl := ownSlice_len _ _ _ $$ Hb
  have hl : sint.Z b.len = 5 := by have := Hbl.1; simp at this; word
  wp_auto
  rw [ite_eq_left (by rw [hl]; decide)]
  wp_apply wp_load_slice_index b _ _ dq (BitVec.ofNat 8 n) (by decide) $$ [$Hb] as Hb
  · ipureintro; rfl
  rw [ite_eq_left (by rw [hl]; decide)]
  wp_apply wp_load_slice_index b _ _ dq (BitVec.ofNat 8 f) (by decide) $$ [$Hb] as Hb
  · ipureintro; rfl
  rw [ite_eq_left (by rw [hl]; decide)]
  wp_apply wp_load_slice_index b _ _ dq (BitVec.ofNat 8 ba) (by decide) $$ [$Hb] as Hb
  · ipureintro; rfl
  rw [ite_eq_left (by rw [hl]; decide)]
  wp_apply wp_load_slice_index b _ _ dq (BitVec.ofNat 8 bm) (by decide) $$ [$Hb] as Hb
  · ipureintro; rfl
  rw [ite_eq_left (by rw [hl]; decide)]
  wp_apply wp_load_slice_index b _ _ dq (BitVec.ofNat 8 bl) (by decide) $$ [$Hb] as Hb
  · ipureintro; rfl
  have hw : ∀ x : Nat, x < 256 → W64 (uint.Z (BitVec.ofNat 8 x)) = W64 x := by
    intro x hx; word
  simp only [RCfg.Ok] at hc
  obtain ⟨hnf, hba, hbm, hbl⟩ := hc
  have hb3 : sint.Z (W64 ba) = ba := by word
  rw [hw ba (by omega), hw bm (by omega), hw bl (by omega)]
  have e1 : decide (uint.Z (W64 (ba : Int)) < uint.Z (W64 4)) = true := by
    rw [decide_eq_true_eq]; word
  have e2 : decide (uint.Z (W64 (bm : Int)) < uint.Z (W64 5)) = true := by
    rw [decide_eq_true_eq]; word
  have e3 : decide (uint.Z (W64 (bl : Int)) < uint.Z (W64 4)) = true := by
    rw [decide_eq_true_eq]; word
  rcases hnf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · rw [hw _ (by decide), hw _ (by decide)]
    wp_auto
    rw [e1]
    wp_auto
    rw [e2]
    wp_auto
    rw [e3]
    simp only [confV]
    iapply HΦ
    iexact Hb


/-- `configure(ps, conf)` (`configure.spec`). -/
theorem configure.wp_proof : configure.spec (GF := GF) := by
  intro ps cf
  iintro %Φ ⟨#Hpkg, %hc, HC, #Hps⟩ HΦ
  iapply wp_fupd
  wp_apply wp_configure ps cf hc $$ [$Hpkg $HC] as HC
  ipersist HC
  imodintro
  iapply HΦ
  unfold confRO
  isplitr
  · ipureintro; exact hc
  iexists ps
  iframe #

/-- `poll.ErrDeadlineExceeded`'s value, from the kit's initialization. -/
theorem kit_ed_init :
    isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  iintro #Hpkg
  ihave #Hpoll : (isPkgInit (PROP := IProp GF) pkg_id.internal.poll) $$ []
  · iPkgInit
  iapply github_com.mit_pdos.etcd_grove.examples.net.wire.ed_of_poll $$ Hpoll

/-- `c.Close()` of a connection's end: it returns. -/
theorem wp_closeConn (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    {{ net.connAt t cn s a la ra ∗ connIs (Gg := hG.goose_globalGS) cn }}
      (App (Val #(methods (go.GoType.PointerType net.TCPConn.ty) go!"Close" #t)) (Val #()))
    {{ (err : GoInterface), RET #err; True }} := by
  iintro %Φ ⟨#Hca, #Hconn⟩ HΦ
  iapply net.Conn.Close.wp_proof t cn s a la ra (fun _ => iprop(True)) $$ []
  · iframe Hca
    imod close_au cn s $$ Hconn with ⟨%st, %dd, Hst, Hdd, Hcl⟩
    imodintro
    iexists st, dd
    iframe Hst Hdd
    iintro %res %st' %d' %Hd' Hst Hdd
    imod Hcl $$ %res %st' %d' %Hd' Hst Hdd with -
    imodintro
    itrivial
  inext
  iintro %err -
  iapply HΦ; itrivial

set_option goose.wp.extras true in
/-- `sendConf(a, b)` of the recorded configuration's encoding at a configuration address `a`
(`cfgP`/`cfgQ`): it writes (a prefix of) `cf.enc` on a connection to `a`. -/
theorem sendConf.wp_proof (γ : Names) (a : GoString) (cf : RCfg) (b : GoSlice) :
    {{ isPkgInit (PROP := IProp GF) pkg_id.rabia.examples.rabianet ∗
        addrProto (Gg := hG.goose_globalGS) a (cfgP γ) cfgQ ∗ cfgIs γ.rab cf ∗ b ↦* cf.enc }}
      (App (App (Val (@! rabia.examples.rabianet.sendConf)) (Val #a)) (Val #b))
    {{ (ok : Bool), RET #ok; True }} := by
  wp_start as ⟨#Hproto, #Hcfg, Hb⟩
  ihave %Haok := addrTok_ok a $$ [Hproto]
  · iapply addrProto_tok $$ Hproto
  ihave ⟨%ed, #Hed⟩ := kit_ed_init $$ Hpkg
  ihave #Hio : (isPkgInit (PROP := IProp GF) pkg_id.io) $$ []
  · iPkgInit
  wp_auto
  wp_apply net.Dial.wp_proof go!"tcp" net.tcpNet_tcp a iprop(True)
      (fun cid => iprop(connEnd (Gg := hG.goose_globalGS) cid false (cfgP γ) cfgQ [] [] ∗
        connFresh (Gg := hG.goose_globalGS) cid false)) $$ []
    as %cv %err (⟨%Herr, %cid, #Hcl, ⟨Hend, -⟩⟩ | ⟨-, %x, -, #Herr⟩)
  · isplitr
    · ipureintro; exact Haok
    isplit
    · itrivial
    · iapply dial_au a (cfgP γ) cfgQ $$ Hproto
  · subst Herr
    wp_auto
    iunfold connEnd at Hend
    icases Hend with ⟨Hsend, Hrecv⟩
    ihave #Hconn := sendTok_connIs cid false _ _ $$ Hsend
    unfold net.isConn
    icases Hcl with ⟨%t, %la, %ra, %Hct, #Hca⟩
    subst Hct
    wp_auto
    ihave #HP : □ cfgP (GF := GF) γ cid ([] ++ cf.enc) $$ []
    · imodintro; unfold cfgP; iexists cf; iframe Hcfg; ipureintro; exact List.prefix_refl _
    wp_apply net.Conn.Write.wp_proof t cid false a la ra b cf.enc (DFrac.own 1) ed
        (writeP cid false (cfgP γ) []) $$ [Hb Hsend]
      as %nw %err ⟨%w, %res, Hsend, Hb, %Hw, #HE⟩
    · iframe Hca Hb Hed
      isplitl [Hsend]
      · iapply writeP_init $$ Hsend
      · iapply write_acc cid false (cfgP γ) [] cf.enc $$ HP
    icases net.resErr_netErr _ _ _ _ _ _ _ $$ HE with %Hne
    cases res with
    | some k =>
      obtain ⟨pe, rfl⟩ := Hne.2 (by simp)
      wp_auto
      wp_apply wp_closeConn t cid false a la ra $$ [] as %_ -
      · iframe #
      try wp_auto
      iapply HΦ; itrivial
    | none =>
      have herr := Hne.1 rfl
      subst herr
      wp_auto
      ihave Hsl := slice_array (V := w8) a_ptr 1 _ (by decide) $$ a
      ihave HRL := recvTok_L cid false cfgQ [] $$ Hrecv
      try wp_auto
      rw [show sint.Z (W64 0) = 0 from rfl, go.arrayIndexRef_0,
        show (W64 1 - W64 0 : w64) = W64 1 from rfl]
      wp_apply wp_connReadFull t cid false a la ra ed cfgQ [] _ _ $$ [$Hio $Hca $Hed $HRL $Hsl]
        as %n %err ⟨%data, %Hd, Hsl, Hrecv⟩
      obtain ⟨-, hdl, herr⟩ := Hd
      have hz : (zero_val (GoArray w8 1)).arr.length = 1 := rfl
      rw [hz] at hdl herr
      rcases err with e | _
      · dsimp only
        wp_auto
        wp_apply wp_closeConn t cid false a la ra $$ [] as %_ -
        · iframe #
        try wp_auto
        iapply HΦ; itrivial
      have hl1 : data.length = 1 := herr rfl
      obtain ⟨x, rfl⟩ : ∃ x, data = [x] := by
        rcases data with _ | ⟨x, _ | ⟨y, t⟩⟩ <;> simp at hl1; exact ⟨x, rfl⟩
      rw [show [x] ++ List.drop [x].length (List.replicate 1 (zero_val w8)) = [x] from rfl]
      icases (ownSlice_elem_acc (V := w8) 0 x _ _ [x] (by decide) rfl) $$ Hsl with ⟨Hx, -⟩
      wp_auto
      ihave Hx : arrayIndexRef w8 (sint.Z (W64 0)) a_ptr ↦ x $$ [Hx]
      · rw [show sint.Z (W64 0) = (0 : Int) from rfl]; unfold sliceIndexRef; iexact Hx
      wp_auto
      wp_if_destruct
      all_goals
        wp_apply wp_closeConn t cid false a la ra $$ [] as %_ -
        · iframe #
        try wp_auto
        iapply HΦ; itrivial
  · rcases err with e | _
    · wp_auto
      iapply HΦ; itrivial
    · icases net.resErr_netErr _ _ _ _ _ _ _ $$ Herr with %Hne
      exact absurd (Hne.2 (by simp)) (by intro h; obtain ⟨_, h⟩ := h; cases h)

end proof

end Perennial.rabia.examples.rabianet
