/-
(Ported from dsverify-lab `examples/rabia/proof/Proof/rabia/roles/server/layers/network/Prologue.lean`, run `rabia-r1wake-1`.)

The proofs of `rabia/roles/server/layers/network.NetworkInit` and `(*Network).Prologue`, from tcp's
`NetTCPInit` and `NetTCP.Connect` specs (`tcp/Spec.lean`), taken as arguments (linked by the kit).
-/
module

public import Dsverify.Proof.rabia.roles.server.layers.network.Basics
public import Perennial.Proof.fmt.Printf
public import Dsverify.Proof.rabia.internal.tcp.Spec

@[expose] public section

noncomputable section

namespace Perennial.rabia.roles.server.layers.network

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode model Net rabia.internal.message
  rabia.internal.config rabia rabia.internal.tcp

set_option linter.unusedSectionVars false

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics] [π : NetProtoGS]
variable [package_sem : rabia.roles.server.layers.network.Assumptions]

set_option goose.wp.extras true

/-- The push logs' empty lower bounds (persistent). -/
theorem pushLbs_nil_fupd (E : CoPset) (γl : SrvNames) :
    ∀ L : List Nat, ⊢ |={E}=> [∗list] X ∈ L, pushLb (GF := GF) γl X [] := by
  intro L
  induction L with
  | nil =>
    imodintro
    iapply BigSepL.bigSepL_nil.2; iempintro
  | cons x L ih =>
    imod ih with H
    imod monoListLb_nil_fupd (GF := GF) (A := MsgV) E (γl.push x) with Hx
    imodintro
    iapply BigSepL.bigSepL_cons.2
    unfold pushLb
    iframe

set_option maxHeartbeats 4000000 in
theorem Network.Prologue.wp_of (hC : NetTCP.Connect.spec (GF := GF))
    (hP : fmt.Printf.spec (GF := GF)) :
    Network.Prologue.spec (GF := GF) := fun γ cf k γl ch n => by
  wp_start as ⟨#Hconf, #Hsh, #Hcfg, Hres⟩
  unfold networkInitOk
  icases Hres with ⟨%nv, %γr, %γts, %γsl, %Hf, Hn, #Hch, #Hrecv, Hcons, Hown, Hboot, #Hts, Hprod,
    Hconsu, Hsa, #Hslb⟩
  unfold networkBootRes
  icases Hboot with ⟨He2n, Hn2h, Hha, Hbc, Hpush⟩
  ipersist Hn
  iStructNamed Hn
  wp_auto
  wp_apply hC γ cf k γl γr nv.TCP' Hf.1 $$ [$Hrecv $Hown $Hpush $Hconf $Hsh $Hcfg] as
    ⟨%γs, #Hsend, Hprods⟩
  imod pushLbs_nil_fupd ⊤ γl (List.range cf.n) with #Hps
  imod monoListLb_nil_fupd (GF := GF) (A := MsgV) ⊤ γl.exlog with #Hex0
  wp_bind (App (Val (GoInstruction (CompositeLiteral (go.SliceType go.any))))
    (Val (LiteralValueV _)))
  iapply wp_slice_literal (V := GoInterface) (t := go.any)
    [interface.mkOk go.uint32 #nv.SvrId']
  wp_auto
  isplitl []
  · ipureintro; rfl
  iintro %args_sl ⟨Hargs, -⟩
  have hwf : fmt.ArgsWf [interface.mkOk go.uint32 #nv.SvrId'] :=
    fmt.ArgsWf.cons_int _ _ _ (.uint32 nv.SvrId') fmt.ArgsWf.nil
  wp_apply hP _ _ _ _ $$ [Hargs]
  · iframe Hargs
    iapply fmt.argsOk_of_argsWf hwf
  iintro %nn %err -
  wp_auto
  icases BigSepL.bigSepL_sep_eqv.1 $$ Hprods with ⟨Hp0s, Hp1s⟩
  iapply HΦ
  isplitl [Hcons Hprod He2n Hsa Hn2h Hha Hp1s]
  · unfold networkRouterRes
    iexists nv, γr, γts, γsl, γs
    iframe Hn Hch Hrecv Hsend Hts
    isplitr
    · ipureintro; exact Hf
    unfold routerLoop
    iexists List.replicate cf.n [], [], [], [], [], []
    have hrep : (List.replicate cf.n ([] : List MsgV)).map List.length = List.replicate cf.n 0 := by simp
    rw [hrep]
    iframe
    isplitr
    · ipureintro; simp
    isplitr
    · imodintro
      iintro %X %px %hx
      have hX : X < cf.n ∧ px = [] := by
        rw [List.getElem?_replicate] at hx
        by_cases h : X < cf.n
        · simp only [h, ↓reduceIte, Option.some.injEq] at hx; exact ⟨h, hx.symm⟩
        · simp [h] at hx
      obtain ⟨hX, rfl⟩ := hX
      have hr : (List.range cf.n)[X]? = some X := by simp [hX]
      iapply BigSepL.bigSepL_lookup hr $$ Hps
    isplitr
    · ipureintro; simp
    isplitr
    · ipureintro
      refine ⟨by simp, ?_⟩
      intro X px hx j hj
      rw [List.getElem?_replicate] at hx
      split at hx
      · simp only [Option.some.injEq] at hx; subst hx; simp [bcastPart] at hj
      · cases hx
    have hm : ∀ (_k : Nat) (x : OrdNames), (ordProd (GF := GF) x 1 0) ⊢ ∃ c : Nat, ordProd x 1 c :=
      fun _ x => by iintro H; iexists 0; iexact H
    iapply BigSepL.bigSepL_mono_of_forall (fun {k x} => hm k x) $$ Hp1s
  · unfold networkSerRes
    iexists nv, γts, γsl, γs
    iframe Hn Hsend Hts
    isplitr
    · ipureintro; exact Hf.1
    unfold serLoop
    iexists [], [], [], []
    iframe
    isplitr
    · iexact Hslb
    isplitr
    · ipureintro; simp
    isplitr
    · unfold exLb; iexact Hex0
    isplitr
    · ipureintro; exact ⟨⟨by simp, by simp, by simp⟩, by simp⟩
    isplitr
    · ipureintro; exact ⟨⟨by simp, by simp, by simp⟩, by simp⟩
    rw [List.filter_nil]
    iapply BigSepL.bigSepL_nil.2; iempintro

set_option maxHeartbeats 4000000 in
theorem NetworkInit.wp_of (hI : NetTCPInit.spec (GF := GF)) :
    NetworkInit.spec (GF := GF) := fun γ cf k γl ch id wg hid hk => by
  wp_start as ⟨#Hconf, #Hch, Haddr, Hboot⟩
  ihave ⟨%ps, #Hc⟩ := confRO_val $$ Hconf
  iStructNamed Hc
  wp_auto
  wp_apply chan.wp_make2 (V := Msg) (W64 500000) as %tsc %γc ⟨#Hchan, %Hcap, Hoc⟩
  · ipureintro; word
  iapply fupd_wp
  imod serLog_alloc ⊤ with ⟨%γsl, Hsa, #Hslb⟩
  imod start_spsc tsc (toSerP γ cf k γl γsl) (fun _ => iprop(False)) γc $$ Hchan [Hoc] with
    ⟨%γts, #Hts, Hprod, Hconsu⟩
  · iright; iexact Hoc
  imodintro
  wp_apply hI γ cf k γl id hid hk $$ [$Haddr $Hconf] as %t ⟨%γr, #Hrecv, Hcons, Hown⟩
  iapply HΦ
  unfold networkInitOk
  iexists _, γr, γts, γsl
  iframe «$r0»
  dsimp only
  isplitr
  · ipureintro; exact ⟨hk, rfl, rfl, rfl, rfl, rfl, rfl⟩
  iframe
  iframe Hch Hrecv Hts Hslb

/-- `Network.Prologue.spec`, from tcp's `NetTCP.Connect` (`fmt.Printf` linked). -/
theorem Network.Prologue.wp_proof (hC : NetTCP.Connect.spec (GF := GF)) :
    Network.Prologue.spec (GF := GF) :=
  Network.Prologue.wp_of hC fmt.Printf.wp_proof

end proof
end Perennial.rabia.roles.server.layers.network
