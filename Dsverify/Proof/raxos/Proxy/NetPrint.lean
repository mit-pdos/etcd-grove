/-
Package `proxy`: `fmt.Println` of arguments that are well-formed basic values or errors with some
message (`net.rpc.errAny`): `waitForConnections`'s `fmt.Println("TCP accept error:", err)`.
-/
module

public import Dsverify.Proof.raxos.Proxy.NetSpecs

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.raxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

section proofs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics] [π : NetProtoGS] [qv : hyp.QpVocab GF]
variable [fmt.Assumptions]

/-- An argument `touch` may format: a well-formed basic value, or an error with some message. -/
def printOk (x : GoInterface) : IProp GF :=
  iprop(⌜∀ ii, x = interface.ok ii → fmt.ArgWf ii⌝ ∨ net.rpc.errAny x)

instance printOk_persistent (x : GoInterface) : Persistent (printOk (GF := GF) x) := by
  unfold printOk; infer_instance

theorem wp_touch_ok (v : GoInterface) :
    {{ printOk (GF := GF) v }}
      (App (Val fmt.touch) (Val #v))
    {{ RET #(); True }} := by
  iintro %Φ Hv HΦ
  iunfold printOk at Hv
  icases Hv with (%Hwf | Herr)
  · iapply fmt.wp_touch v Hwf $$ [] HΦ
    itrivial
  unfold net.rpc.errAny
  icases Herr with ⟨%e, %He, %Hty, #Hwp⟩
  subst He
  unfold fmt.touch
  wp_auto
  simp only [Hty, ↓reduceIte]
  wp_auto
  wp_apply Hwp as %msg
  iapply HΦ; itrivial

/-- `touchAll(vs)` for arguments `printOk` allows. -/
theorem wp_touchAll_ok (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ (□ ([∗list] x ∈ xs, printOk x) ∗ arg ↦*{dq} xs : IProp GF) }}
      (App (Val fmt.touchAll) (Val #arg))
    {{ RET #(); arg ↦*{dq} xs }} := by
  iintro %Φ ⟨#Hok, Hs⟩ HΦ
  unfold fmt.touchAll
  wp_auto
  ihave %Hlen := ownSlice_len $$ Hs
  ihave IH : iprop(∃ (n : w64) (vv : GoInterface),
      "i" ∷ i_ptr ↦ n ∗ "v" ∷ v_ptr ↦ vv ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ∧ sint.Z n ≤ (xs.length : Int)⌝) $$ [i v]
  · iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  wp_for IH
  wp_if_destruct
  · have Hlt : (sint.Z n).toNat < xs.length := by word
    obtain ⟨x, Hx⟩ : ∃ x, xs[(sint.Z n).toNat]? = some x :=
      ⟨_, List.getElem?_eq_getElem Hlt⟩
    simp only [show 0 ≤ sint.Z n ∧ sint.Z n < sint.Z arg.len from ⟨Hn.1, Hif⟩]
    wp_apply wp_load_slice_index arg (sint.Z n) xs dq x Hn.1 $$ [Hs] as Hs
    · iframe; ipureintro; exact Hx
    ihave #Hx := BigSepL.bigSepL_lookup Hx $$ Hok
    wp_apply wp_touch_ok x $$ [$Hx]
    wp_for_post
    iframe
    iexists _, _
    iframe
    ipureintro
    exact ⟨by word, by word⟩
  · iapply HΦ
    iframe

/-- `Println(a...)` for arguments `printOk` allows. -/
theorem wp_Println_ok (arg : GoSlice) (xs : List GoInterface) (dq : DFrac) :
    {{ (□ ([∗list] x ∈ xs, printOk x) ∗ arg ↦*{dq} xs : IProp GF) }}
      (App (Val (@! fmt.Println)) (Val #arg))
    {{ (n : w64), RET (PairV #n #GoInterface.nil); arg ↦*{dq} xs }} := by
  wp_start as ⟨#Hok, Hs⟩
  wp_apply wp_touchAll_ok arg xs dq $$ [$Hok $Hs] as Hs
  wp_apply wp_ArbitraryInt as %a -
  iapply HΦ
  iframe

/-- The two arguments of `fmt.Println("...", err)`. -/
theorem printOk_str_err (s : GoString) (err : GoInterface) :
    net.rpc.errAny (GF := GF) err ⊢
      □ ([∗list] x ∈ [interface.mkOk go.string #s, err], printOk x) := by
  iintro #He
  imodintro
  isplitr
  · iunfold printOk; ileft; ipureintro
    intro ii hii
    exact fmt.ArgsWf.cons_string s [] fmt.ArgsWf.nil ii (by rw [hii]; simp)
  isplitl
  · iunfold printOk; iright; iexact He
  iempintro

end proofs

end Perennial.raxos
