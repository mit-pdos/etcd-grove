/-
Ported from dsverify-lab examples/swiftpaxos/proof/Proof/swiftnet/ClientAU.lean (lab master 915f964, run swift-n2nofast-1; notes/dsv-swiftpaxos.md).
-/
/-
The adapter's linearization (`wp_Op`'s riskiest step): the driver's atomic update over
`ownState` (at `↑clientN`, from `σ` to `σ'` with `kv`'s step) passed into `BufferClient.Write`'s
and `Read`'s logically atomic specs (over `linOwn γ.lin` at `⊤ \ ↑sp.spN`). The update is
committed at the SwiftPaxos step that decides the command (inside `sp.inv`), with `kv`'s step:
a put of `lin.keyName key`, a get's value read at that point (its emptiness meaning "not
found": `ownState`'s values are non-empty).
-/
module

public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.examples.swiftnet.ClientNodeDefs
public import Dsverify.Proof.github_com.imdea_software.swiftpaxos.Hyps

@[expose] public section

noncomputable section

namespace Perennial.github_com.imdea_software.swiftpaxos

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Dsv

attribute [local instance] netShaExts netShaExtsSemantics netShaExtsInterp netShaExts_has netShaExts_hasSha256

namespace cnode

section au
variable [go_gctx : GoGlobalContext]
variable [hG : HeapGS HasLC.hasLC netDistGF] [sem : go.Semantics]

theorem clientN_sub_spN : (↑clientN : CoPset) ⊆ ⊤ \ ↑sp.spN := by
  unfold clientN sp.spN
  solve_ndisj

/-- The driver's atomic update for input `i`, with the client's commit postcondition `Q`. -/
abbrev driverAU (γ : SwiftNames netDistGF) (i : (kv GoString GoString).Input)
    (Q : (kv GoString GoString).State → (kv GoString GoString).State →
      (kv GoString GoString).Output → IProp netDistGF) : IProp netDistGF :=
  iprop(AU <{ ∃∃ σ, ownState γ σ }> @ ↑clientN, ∅
    <{ ∀∀ σ' o, ownState γ σ' ∗ ⌜(kv GoString GoString).step σ i σ' o⌝, COMM Q σ σ' o }>)

/-- The registrations (`sp.allPredsReg`, persistent), peeked from the driver's update: opened
and aborted at once. -/
theorem driverAU_peek (γ : SwiftNames netDistGF) (i : (kv GoString GoString).Input)
    (Q : (kv GoString GoString).State → (kv GoString GoString).State →
      (kv GoString GoString).Output → IProp netDistGF) :
    driverAU γ i Q ⊢ |={⊤}=> driverAU γ i Q ∗ sp.allPredsReg γ.sp γ.conf := by
  iintro HAU
  imod HAU with ⟨%σ, Hσ, Hclose⟩
  rcases σ with ⟨σ, ⟨⟩⟩
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  ihave #Hreg : sp.allPredsReg γ.sp γ.conf $$ [Hσ]
  · unfold ownState
    icases Hσ with ⟨-, -, #Hreg⟩
    iexact Hreg
  icases Hclose with ⟨Hab, -⟩
  imod Hab $$ Hσ with HAU
  imodintro
  iframe HAU Hreg

theorem put_step (σ : (kv GoString GoString).State) (key : w64) (v : List w8) :
    (kv GoString GoString).step σ (KvInput.put (lin.keyName key) v)
      (sp.lin.apply (sp.Cmd.put key v) σ).1 KvOutput.done := by
  simp only [kv, sp.lin.apply, sp.Cmd.put, sp.Cmd.isPut, beq_self_eq_true, ↓reduceIte, and_true]
  funext k
  by_cases h : k = lin.keyName key <;> simp [h]

theorem put_ne (σ : (kv GoString GoString).State) (key : w64) (v : List w8) (hv : v ≠ [])
    (Hne : ∀ k w, σ k = some w → w ≠ []) :
    ∀ k w, (sp.lin.apply (sp.Cmd.put key v) σ).1 k = some w → w ≠ [] := by
  intro k w h
  simp only [sp.lin.apply, sp.Cmd.put, sp.Cmd.isPut, beq_self_eq_true, ↓reduceIte] at h
  by_cases hk : k = lin.keyName key
  · simp [hk] at h; subst h; exact hv
  · simp [hk] at h; exact Hne k w h

/-- A put through `Write`'s atomic triple (any expression `e` with `Write`'s spec shape, its
private postcondition `P`): the driver's update committed with output `done`. -/
theorem put_of_au (γ : SwiftNames netDistGF) (key : w64) (v : List w8) (hv : v ≠ [])
    (Q : (kv GoString GoString).State → (kv GoString GoString).State →
      (kv GoString GoString).Output → IProp netDistGF) (e : Expr) (P : IProp netDistGF) :
    (<<{ ∀∀ σ, linOwn γ.lin σ }>> e @ ↑sp.spN
      <<{ linOwn γ.lin (sp.lin.apply (sp.Cmd.put key v) σ).1 | RET #(); P }>>) ⊢
    driverAU γ (.put (lin.keyName key) v) Q -∗
    WP e {{ r, ⌜r = #()⌝ ∗ P ∗ ∃ σ σ', Q σ σ' .done }} := by
  iintro Hwp HAU
  iunfold atomic_wp at Hwp
  iapply Hwp
  ihave HAU := atomic_update_mask_weaken clientN_sub_spN $$ HAU
  iauintro
  unfold atomic_acc
  imod HAU with ⟨%σ, Hσ, Hclose⟩
  rcases σ with ⟨σ, ⟨⟩⟩
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  unfold ownState
  icases Hσ with ⟨Hσ, %Hne, #Hreg⟩
  imodintro
  iexists (⟨σ, ⟨⟩⟩ : (Tele.cons fun _ : (kv GoString GoString).State => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  unfold lin.own
  iframe Hσ
  isplit
  · iintro Hσ
    icases Hclose with ⟨Hab, -⟩
    iapply Hab
    iframe Hσ Hreg
    ipureintro; exact Hne
  · iintro Hσ'
    icases Hclose with ⟨-, Hc⟩
    have hstep : (kv GoString GoString).step σ (KvInput.put (lin.keyName key) v)
        (sp.lin.apply (sp.Cmd.put key v) σ).1 KvOutput.done := put_step σ key v
    imod Hc $$ %(sp.lin.apply (sp.Cmd.put key v) σ).1 %KvOutput.done [Hσ'] with HQ
    · iframe Hσ' Hreg
      ipureintro
      exact ⟨put_ne σ key v hv Hne, hstep⟩
    imodintro
    iintro HP
    iframe HP
    isplitr
    · ipureintro; rfl
    iexists σ, (sp.lin.apply (sp.Cmd.put key v) σ).1
    iexact HQ

/-- A get through `Read`'s atomic triple: the driver's update committed with output
`got ov`, `ov` the key's value at the commit (never `some []`), whose `getD []` the returned
slice holds. -/
theorem get_of_au (γ : SwiftNames netDistGF) (key : w64)
    (Q : (kv GoString GoString).State → (kv GoString GoString).State →
      (kv GoString GoString).Output → IProp netDistGF) (e : Expr) (P : IProp netDistGF) :
    (<<{ ∀∀ σ, linOwn γ.lin σ }>> e @ ↑sp.spN
      <<{ linOwn γ.lin σ | (sl : GoSlice), RET #sl;
        sl ↦*□ (σ (lin.keyName key)).getD [] ∗ P }>>) ⊢
    driverAU γ (.get (lin.keyName key)) Q -∗
    WP e {{ r, ∃ (sl : GoSlice) (ov : Option GoString), ⌜r = #sl ∧ ov ≠ some []⌝ ∗
      sl ↦*□ ov.getD [] ∗ P ∗ ∃ σ σ', Q σ σ' (.got ov) }} := by
  iintro Hwp HAU
  iunfold atomic_wp at Hwp
  iapply Hwp
  ihave HAU := atomic_update_mask_weaken clientN_sub_spN $$ HAU
  iauintro
  unfold atomic_acc
  imod HAU with ⟨%σ, Hσ, Hclose⟩
  rcases σ with ⟨σ, ⟨⟩⟩
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  unfold ownState
  icases Hσ with ⟨Hσ, %Hne, #Hreg⟩
  imodintro
  iexists (⟨σ, ⟨⟩⟩ : (Tele.cons fun _ : (kv GoString GoString).State => Tele.nil).Arg)
  dsimp only [Tele.lam, Tele.app, Tele.bind, BI.tforall_cons, BI.tforall_nil, BIBase.wandM]
  unfold lin.own
  iframe Hσ
  isplit
  · iintro Hσ
    icases Hclose with ⟨Hab, -⟩
    iapply Hab
    iframe Hσ Hreg
    ipureintro; exact Hne
  · iintro Hσ'
    icases Hclose with ⟨-, Hc⟩
    imod Hc $$ %σ %(KvOutput.got (σ (lin.keyName key))) [Hσ'] with HQ
    · iframe Hσ' Hreg
      ipureintro
      exact ⟨Hne, rfl, rfl⟩
    imodintro
    iintro %sl ⟨Hsl, HP⟩
    iexists sl, σ (lin.keyName key)
    iframe Hsl HP
    isplitr
    · ipureintro
      refine ⟨rfl, fun h => Hne _ [] h rfl⟩
    iexists σ, σ
    iexact HQ

section calls
variable [SwiftNetPkgState netDistGF] [SwiftHyps netDistGF] [client.Assumptions]

/-- `b.Write(key, vsl)` with the driver's update for the put: the update's commit, client
ready at `s + 1`. -/
theorem wp_Write_au (wp_Write : client.BufferClient.Write.spec) (γ : SwiftNames netDistGF)
    (b : Loc) (cid : w32) (s : Nat) (key : w64) (vsl : GoSlice) (v : List w8)
    (hv : v ≠ []) (hlen : v.length < 2 ^ 16) (hs : s < 2 ^ 25)
    (Q : (kv GoString GoString).State → (kv GoString GoString).State →
      (kv GoString GoString).Output → IProp netDistGF) :
    ⊢ ∀ Φ : val → IProp netDistGF,
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin cid s ∗ vsl ↦*□ v ∗
        driverAU γ (.put (lin.keyName key) v) Q -∗
      (client.ready b γ.sp γ.conf γ.mem γ.lin cid (s + 1) -∗
        (∃ σ σ', Q σ σ' .done) -∗ Φ #()) -∗
      WP (App (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Write"))
        (Val #key)) (Val #vsl)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, Hready, #Hv, HAU⟩ HΦ
  ihave Hw := wp_Write b γ.sp γ.conf γ.mem γ.lin cid s key vsl v $$ Hpkg Hready Hv %(And.intro hlen hs)
  ihave Hwp := put_of_au γ key v hv Q _ _ $$ Hw HAU
  iapply wp_wand $$ Hwp
  iintro %r ⟨%Hr, HP, HQ⟩
  subst Hr
  iapply HΦ $$ HP HQ

/-- `b.Read(key)` with the driver's update for the get: the update's commit with output
`got ov`, the returned slice holding `ov.getD []`, client ready at `s + 1`. -/
theorem wp_Read_au (wp_Read : client.BufferClient.Read.spec) (γ : SwiftNames netDistGF)
    (b : Loc) (cid : w32) (s : Nat) (key : w64) (hs : s < 2 ^ 25)
    (Q : (kv GoString GoString).State → (kv GoString GoString).State →
      (kv GoString GoString).Output → IProp netDistGF) :
    ⊢ ∀ Φ : val → IProp netDistGF,
      isPkgInit (PROP := IProp netDistGF) pkg_id.github_com.imdea_software.swiftpaxos.client ∗
        client.ready b γ.sp γ.conf γ.mem γ.lin cid s ∗
        driverAU γ (.get (lin.keyName key)) Q -∗
      (∀ (sl : GoSlice) (ov : Option GoString), ⌜ov ≠ some []⌝ -∗ sl ↦*□ ov.getD [] -∗
        client.ready b γ.sp γ.conf γ.mem γ.lin cid (s + 1) -∗
        (∃ σ σ', Q σ σ' (.got ov)) -∗ Φ #sl) -∗
      WP (App (Val (b @!! go.GoType.PointerType client.BufferClient.ty @!! go!"Read"))
        (Val #key)) {{ Φ }} := by
  iintro %Φ ⟨#Hpkg, Hready, HAU⟩ HΦ
  ihave Hw := wp_Read b γ.sp γ.conf γ.mem γ.lin cid s key $$ Hpkg Hready %hs
  ihave Hwp := get_of_au γ key Q _ _ $$ Hw HAU
  iapply wp_wand $$ Hwp
  iintro %r ⟨%sl, %ov, %Hr, #Hsl, HP, HQ⟩
  obtain ⟨rfl, Hov⟩ := Hr
  iapply HΦ $$ %sl %ov %Hov Hsl HP HQ

end calls

end au

end cnode

end Perennial.github_com.imdea_software.swiftpaxos
