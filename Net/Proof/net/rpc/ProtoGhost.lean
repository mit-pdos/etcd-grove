/-
The ghost updates of the rpc protocol (`Proto.lean`) a dialer uses: registering a new connection
(`rpc_register`: its names, its invariant with no request, the dialer's half of the request list
and the authority of the requests' names).
-/
module

public import Net.Proof.net.rpc.Proto

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net.rpc

section ghost
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [Gg : GooseGlobalGS hlc GF] [π : NetProtoGS]

include Gg

attribute [local instance] GooseGlobalGS.gooseInvGS

theorem ml_halves {A : Type} [Pos.Countable A] (γ : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ 1 l ⊣⊢
      monoListAuthOwn γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l := by
  have := (monoListAuthOwn_fractional (GF := GF) γ l).fractional (1 : Qp).half (1 : Qp).half
  rwa [Qp.half_add_half] at this

instance regInv_timeless' (W : RpcWorld GF) : Timeless (regInv (Gg := Gg) W) := by
  unfold regInv
  have : ∀ M : GMap Nat RpcConnNames,
      Timeless ([∗map] cn ↦ _n ∈ M, connFresh (Gg := Gg) cn false) :=
    fun _ => BigSepM.bigSepM_timeless (fun _ => inferInstance)
  infer_instance

/-- A dialer registers its new connection `cn` (with the fresh token of its end) in the world. -/
theorem rpc_register (W : RpcWorld GF) (a : GoString) (cn : Nat) :
    inv regN' (regInv (Gg := Gg) W) ∗ connFresh (Gg := Gg) cn false ⊢
      |={⊤}=> ∃ γ : RpcConnNames, isRpcConn (Gg := Gg) W a cn γ ∗
        monoListAuthOwn γ.reqs (1 : Qp).half ([] : List RpcReq) ∗
        ghostMapAuth γ.nm 1 (∅ : GMap Nat (GName × GName × GName)) := by
  iintro ⟨#Hreg, Hfresh⟩
  imod mono_list_own_alloc (GF := GF) ([] : List RpcReq) with ⟨%γr, Hr, -⟩
  icases (ml_halves γr ([] : List RpcReq)).1 $$ Hr with ⟨Hr1, Hr2⟩
  imod ghostVar_alloc (GF := GF) (0 : Nat) with ⟨%γc, Hc⟩
  icases (ghostVar_split_half γc 1 (0 : Nat)).1 $$ Hc with ⟨Hc1, Hc2⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := Option (GoString × List w8))
    with ⟨%γa, Ha⟩
  imod ghost_map_alloc_empty (GF := GF) (K := Nat) (V := GName × GName × GName)
    with ⟨%γn, Hn⟩
  let γ : RpcConnNames := (γr, γc, γa, γn)
  imod inv_alloc connN ⊤ (connInv (Gg := Gg) W a cn γ) $$ [Hr1 Hc1 Hc2 Ha] with #Hinv
  · inext
    iunfold connInv
    iexists [], 0, ∅
    iframe Hr1 Hc1 Ha
    isplitl [Hc2]
    · ileft; iexact Hc2
    isplitr
    · ipureintro; exact ⟨Nat.le_refl _, fun i h => by simp at h⟩
    simp only [List.drop_zero]
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    iapply BigSepM.bigSepM_empty.2; iempintro
  iinv Hreg with >Hi Hclose
  iunfold regInv at Hi
  icases Hi with ⟨%M, HM, HMs⟩
  cases hM : M.lookup cn with
  | some n =>
    ihave Hf := BigSepM.bigSepM_lookup (Φ := fun cn (_n : RpcConnNames) =>
      connFresh (Gg := Gg) cn false) (m := M) (i := cn) (x := n) (by rw [gmap_get?_eq, hM]) $$ HMs
    iexfalso
    iapply connFresh_excl $$ [$Hf $Hfresh]
  | none =>
    imod ghost_map_insert_persist cn γ hM $$ HM with ⟨HM, #He⟩
    imod Hclose $$ [HM HMs Hfresh] with -
    · inext
      iunfold regInv
      iexists M.insert cn γ
      iframe HM
      iapply (BigSepM.bigSepM_insert (Φ := fun cn (_n : RpcConnNames) =>
        connFresh (Gg := Gg) cn false) (by rw [gmap_get?_eq, hM])).2
      iframe Hfresh HMs
    imodintro
    iexists γ
    iframe Hr2 Hn
    iunfold isRpcConn
    iunfold regElem
    iframe He Hinv

end ghost

end net.rpc
end Perennial
