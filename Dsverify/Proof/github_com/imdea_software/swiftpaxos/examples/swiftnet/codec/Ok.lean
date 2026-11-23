/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/codec/Ok.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The harness's obligations on the kit's codec functions (`Harness/Proof/net/rpc/Defs.lean`:
`encOk`, `decOk`, `methodsOk`, `callOk`, `nameOk`), for `kitCodecC` (`Spec/swiftnet/Codec.lean`'s
`kitCodec` with the `C` copies of its definitions, and `dec` restricted to the targets the code
accepts, `decTarget`: HUB-REQUEST 2) and `kitNamesC` (its `kitNames`, on the receivers
`methods` admits: HUB-REQUEST 1). `Codec.lean` derives `kitCodecOk_holds` and `kitNameOk_holds`
from these.
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.codec.Enc

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section ok
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [package_sem : examples.swiftnet.Assumptions]

open sp

theorem kitFn_rpcEncode : net.rpc.kitFn go!"rpcEncode" = functions rpcEncode [] := rfl
theorem kitFn_rpcDecode : net.rpc.kitFn go!"rpcDecode" = functions rpcDecode [] := rfl
theorem kitFn_rpcMethods : net.rpc.kitFn go!"rpcMethods" = functions rpcMethods [] := rfl
theorem kitFn_rpcCall : net.rpc.kitFn go!"rpcCall" = functions rpcCall [] := rfl
theorem kitFn_rpcName : net.rpc.kitFn go!"rpcName" = functions rpcName [] := rfl

/-- `kitCodec` with the `C` copies, `dec` on the accepted targets only. -/
def kitCodecC : net.rpc.RpcCodec GF where
  enc v Ψ := iprop(∃ (dq : DFrac) (x : sp.KitVal), kitValOwnC v dq x ∗
    ∀ x' : sp.KitVal, ⌜sp.KitVal.equivC x x'⌝ -∗ kitValOwnC v dq x -∗ Ψ x'.encode)
  dec bs ptr Ψ := iprop(∃ x0 : sp.KitVal, kitValOwnC ptr (DFrac.own 1) x0 ∗ ⌜decTarget x0⌝ ∗
    ((∀ y : sp.KitVal, ⌜bs = y.encode ∧ y.tag = x0.tag ∧ sp.KitVal.wfC y⌝ -∗
        kitValOwnC ptr (DFrac.own 1) (sp.KitVal.mergeC x0 y) -∗ Ψ true) ∧
      (⌜∀ y : sp.KitVal, y.tag = x0.tag → sp.KitVal.wfC y → bs ≠ y.encode⌝ -∗
        ∀ ok : Bool, (∃ x1 : sp.KitVal, ⌜x1.tag = x0.tag⌝ ∗ kitValOwnC ptr (DFrac.own 1) x1) -∗
          Ψ ok)))
  call rcvr m bs Ψ := iprop(∀ (s : GoSlice) (dq : DFrac), s ↦*{dq} bs -∗
    WP (App (App (App (Val #(net.rpc.kitFn go!"rpcCall")) (Val #rcvr)) (Val #m)) (Val #s))
      {{ v, ∃ (rep : GoSlice) (rbs : List w8) (msg : GoString) (found : Bool),
        ⌜v = PairV (PairV #rep #msg) #found⌝ ∗ rep ↦* rbs ∗ Ψ rbs msg found }})
  methods rcvr := iprop(⌜∃ p : Loc,
    rcvr = interface.mkOk (go.GoType.PointerType master.Master.ty) #p ∨
    rcvr = interface.mkOk (go.GoType.PointerType swift.Replica.ty) #p⌝)

attribute [local instance] kitCodecC

theorem kitWf_wfC (y : KitVal) : kitWf y ↔ KitVal.wfC y := by
  cases y <;> rfl

variable [HasExt netConnExt] [net.Assumptions] [net.model.Assumptions] [net.rpc.Assumptions]

theorem encOkC : ⊢ net.rpc.encOk (GF := GF) (net.rpc.kitFn go!"rpcEncode") := by
  unfold net.rpc.encOk
  iintro !> %v %Ψ %Φ Henc HΦ
  unfold kitCodecC; dsimp only
  icases Henc with ⟨%dq, %x, Hown, Hk⟩
  rw [kitFn_rpcEncode]
  iapply (wp_rpcEncode v dq x) $$ [Hown]
  · iexact Hown
  inext
  iintro %s ⟨%x', %Heq, Hs, Hown⟩
  iapply HΦ $$ Hs
  iapply Hk $$ %x' %Heq Hown

theorem decOkC : ⊢ net.rpc.decOk (GF := GF) (net.rpc.kitFn go!"rpcDecode") := by
  unfold net.rpc.decOk
  iintro !> %data %dq %bs %ptr %Ψ %Φ Hd Hdec HΦ
  unfold kitCodecC; dsimp only
  icases Hdec with ⟨%x0, Hown, %Ht, Hdec⟩
  rw [kitFn_rpcDecode]
  iapply (wp_rpcDecode data dq bs ptr x0) $$ [Hd Hown]
  · iframe; ipureintro; exact Ht
  inext
  iintro %err Hpost
  unfold decodePost
  icases Hpost with ⟨Hd, %x1, Hown, %Htag, (⟨%Herr, %Hok⟩ | ⟨Herr, %Hne⟩)⟩
  · subst Herr
    have hns : net.rpc.notServerErr GoInterface.nil := fun e he => by cases he
    by_cases hy : ∃ y : KitVal, bs = y.encode ∧ y.tag = x0.tag ∧ KitVal.wfC y
    · obtain ⟨y, hb, hyt, hwf⟩ := hy
      have hx1 := Hok y hyt ((kitWf_wfC y).2 hwf) hb
      subst hx1
      icases Hdec with ⟨Ha, -⟩
      ihave Hpsi := Ha $$ %y %(⟨hb, hyt, hwf⟩ : bs = y.encode ∧ y.tag = x0.tag ∧ KitVal.wfC y) Hown
      iapply HΦ $$ %GoInterface.nil %true Hd %(by simp) %hns Hpsi
      simp only [↓reduceIte]; itrivial
    · icases Hdec with ⟨-, Hb⟩
      ihave Hpsi := Hb $$ %(fun y hyt hwf hb => hy ⟨y, hb, hyt, hwf⟩) %true [Hown]
      · iexists x1; iframe; ipureintro; exact Htag
      iapply HΦ $$ %GoInterface.nil %true Hd %(by simp) %hns Hpsi
      simp only [↓reduceIte]; itrivial
  · unfold decErr
    icases Herr with ⟨%Herr, %msg, #Hm⟩
    icases Hdec with ⟨-, Hb⟩
    ihave Hpsi := Hb $$ %(fun y hyt hwf hb => Hne y hyt ((kitWf_wfC y).2 hwf) hb) %false [Hown]
    · iexists x1; iframe; ipureintro; exact Htag
    iapply HΦ $$ %err %false Hd %(by simp [Herr.1]) %Herr.2 Hpsi
    simp only [Bool.false_eq_true, ↓reduceIte]
    iexists msg; iexact Hm

theorem methodsOkC : ⊢ net.rpc.methodsOk (GF := GF) (net.rpc.kitFn go!"rpcMethods") := by
  unfold net.rpc.methodsOk
  unfold kitCodecC; dsimp only
  iintro !> %rcvr %Φ %Hm HΦ
  rw [kitFn_rpcMethods]
  obtain ⟨p, rfl | rfl⟩ := Hm
  · wp_func_call; wp_call; wp_auto; iapply HΦ
  · wp_func_call; wp_call; wp_auto; iapply HΦ

theorem callOkC : ⊢ net.rpc.callOk (GF := GF) (net.rpc.kitFn go!"rpcCall") := by
  unfold net.rpc.callOk
  iintro !> %rcvr %m %args %dq %bs %Ψ %Φ Hargs Hcall HΦ
  unfold kitCodecC; dsimp only
  ihave Hwp := Hcall $$ %args %dq Hargs
  ihave Hwp := wp_frame_step_l'
    (e := App (App (App (Val #(net.rpc.kitFn go!"rpcCall")) (Val #rcvr)) (Val #m)) (Val #args))
    (R := iprop(∀ (rep : GoSlice) (rbs : List w8) (msg : GoString) (found : Bool),
        rep ↦* rbs -∗ Ψ rbs msg found -∗ Φ (PairV (PairV #rep #msg) #found))) rfl (fun _ h => h)
    $$ [HΦ Hwp]
  · iframe
  iapply wp_wand $$ Hwp
  iintro %v ⟨HΦ, %rep, %rbs, %msg, %found, %Hv, Hrep, HΨ⟩
  subst Hv
  iapply HΦ $$ Hrep HΨ

/-- `kitNames`' name (a copy). -/
def kitNameC (rcvr : GoInterface) : GoString := open Classical in
  if ∃ p : Loc, rcvr = interface.mkOk (go.GoType.PointerType master.Master.ty) #p then
    go!"Master"
  else if ∃ p : Loc, rcvr = interface.mkOk (go.GoType.PointerType swift.Replica.ty) #p then
    go!"Replica"
  else go!""

/-- `nameOk` on the receivers `rpcName` accepts (HUB-REQUEST 1: the harness's `nameOk` asks it of
every value, on which `rpcName` panics). -/
theorem nameOkC : ⊢ (□ ∀ (rcvr : GoInterface) (Φ : val → IProp GF),
    net.rpc.RpcCodec.methods rcvr -∗ ▷ Φ #(kitNameC rcvr) -∗
      WP (App (Val #(net.rpc.kitFn go!"rpcName")) (Val #rcvr)) {{ Φ }} : IProp GF) := by
  unfold kitCodecC; dsimp only
  iintro !> %rcvr %Φ %Hm HΦ
  rw [kitFn_rpcName]
  obtain ⟨p, rfl | rfl⟩ := Hm
  · have : kitNameC (interface.mkOk (go.GoType.PointerType master.Master.ty) #p) = go!"Master" := by
      unfold kitNameC; rw [if_pos ⟨p, rfl⟩]
    rw [this]
    wp_func_call; wp_call; wp_auto; iapply HΦ
  · have : kitNameC (interface.mkOk (go.GoType.PointerType swift.Replica.ty) #p) = go!"Replica" := by
      unfold kitNameC
      rw [if_neg, if_pos ⟨p, rfl⟩]
      rintro ⟨p', h⟩
      simp only [interface.mkOk, GoInterface.ok.injEq, GoInterfaceOk.mk.injEq,
        go.GoType.PointerType.injEq] at h
      have h1 := h.1
      simp only [gooseReduceGoTypeEq] at h1
    rw [this]
    wp_func_call; wp_call; wp_auto; iapply HΦ

end ok

end Perennial.github_com.imdea_software.swiftpaxos.examples.swiftnet
