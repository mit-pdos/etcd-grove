/- Lean-first (no Rocq counterpart).

# `net/httpdriver`: the lemmas of `session`'s proof

* The package facts `session` reads, from the driver's `isPkgInit` (`drv_env`): net/http's `httpEnv`,
  `io`'s and `bufio`'s facts, `poll.ErrDeadlineExceeded`'s and `io.EOF`'s values.
* A request's slot (`DReq.slot`): its wire is the request's (`slotWire_dslot`), it is well-formed
  (`slotOk_dslot`), a request slot is the request's (`dslot_inl`), and its facts hold of the body saved
  at its ghost name (`slotFacts_dslot`). Slots that are all requests, followed by one more slot, are
  well-formed (`slotsOk_snoc`); what the client writes then meets `httpReqP` (`reqP_snoc`).
* What `check` takes of the answer at index `i`, from the client's knowledge of it (`drvQ_chk`): the
  `400`, or the handler's complete answer to the request at `i` (its body read whole).
* `Close`'s update with no outcome kept (`close_true`), a mono-list's authority in halves
  (`sess_ml_halves`) and its lower bound (`ml_auth_lb`).
-/
module

public import Net.Proof.github_com.mit_pdos.etcd_grove.examples.net.httpdriver.ClientStream

@[expose] public section

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net
open net.http (HReq HProto Resp RespSlot ReqSlot HdrLine HttpProtoGS)

namespace github_com.mit_pdos.etcd_grove.examples.net.httpdriver

/-! ## Slots and answers (pure) -/

theorem slotWire_dslot (d : DReq) (τ : GName) : net.http.slotWire (d.slot τ) = d.wire := by
  cases d <;> rfl

theorem slotOk_dslot (d : DReq) (hd : d.ok) (τ : GName) : net.http.slotOk (d.slot τ) := by
  cases d with
  | junk => exact junkWire_ok
  | echo m v b => exact DReq.reqOk _ hd nofun
  | status => exact DReq.reqOk _ hd nofun
  | nope w => exact DReq.reqOk _ hd nofun

theorem dslot_inl (d : DReq) (τ τ' : GName) (R : HReq) (B : List w8)
    (h : d.slot τ = .inl (R, τ', B)) : d ≠ .junk ∧ R = d.hreq ∧ τ' = τ ∧ B = d.body := by
  cases d with
  | junk => cases h
  | echo m v b => cases Sum.inl.inj h; exact ⟨nofun, rfl, rfl, rfl⟩
  | status => cases Sum.inl.inj h; exact ⟨nofun, rfl, rfl, rfl⟩
  | nope w => cases Sum.inl.inj h; exact ⟨nofun, rfl, rfl, rfl⟩

theorem slotsWire_snoc (L : List ReqSlot) (s : ReqSlot) :
    net.http.slotsWire (L ++ [s]) = net.http.slotsWire L ++ net.http.slotWire s := by
  simp [net.http.slotsWire]

theorem respsWire_snoc (A : List Resp) (ρ : Resp) :
    net.http.respsWire ((A ++ [ρ]).map RespSlot.ans) =
      net.http.respsWire (A.map RespSlot.ans) ++ net.http.respWire ρ := by
  simp [net.http.respsWire, net.http.respSlotWire]

/-- Request slots, then one well-formed slot: well-formed (junk only as the last). -/
theorem slotsOk_snoc (L : List ReqSlot) (s : ReqSlot)
    (hL : ∀ x ∈ L, net.http.slotOk x ∧ x.isLeft = true) (hs : net.http.slotOk s) :
    net.http.slotsOk (L ++ [s]) := by
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact (hL x hx).1
    · rw [List.mem_singleton] at hx
      subst hx
      exact hs
  · intro i j hij
    rw [List.length_append, List.length_singleton]
    rcases Nat.lt_or_ge i L.length with h | h
    · rw [List.getElem?_append_left h] at hij
      have hm : Sum.inr j ∈ L := List.mem_iff_getElem?.2 ⟨i, hij⟩
      have := (hL _ hm).2
      simp at this
    · rcases Nat.lt_or_ge i (L.length + 1) with h2 | h2
      · omega
      · rw [List.getElem?_eq_none (by rw [List.length_append, List.length_singleton]; omega)] at hij
        cases hij

section lemmas
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions] [field_sem : net.FieldAssumptions]
variable [π : NetProtoGS] [hπ : HttpProtoGS]

attribute [local instance] GooseGlobalGS.gooseInvGS

/-! ## The package facts -/

/-- `poll.ErrDeadlineExceeded`'s value, from `internal/poll`'s initialization. -/
theorem poll_ed :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢
      ∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed := by
  refine (isPkgInit_access (PROP := IProp GF) pkg_id.internal.poll).trans ?_
  show iprop((∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrNoDeadline) e DFrac.discard) ∗
    (∃ e : GoInterface, typedPointsto (globalAddr internal.poll.ErrDeadlineExceeded) e DFrac.discard) ∗
    (∃ x : Loc, typedPointsto (globalAddr internal.poll.ErrFileClosing)
      (interface.mkOk (go.GoType.PointerType _root_.Perennial.errors.errorString.ty) #x) DFrac.discard)) ⊢ _
  iintro ⟨-, #Hd, -⟩
  iexact Hd

/-- The package facts `session` reads. -/
theorem drv_env :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.net.httpdriver ⊢
      net.http.httpEnv (GF := GF) ∗ isPkgInit (PROP := IProp GF) pkg_id.io ∗
      isPkgInit (PROP := IProp GF) pkg_id.bufio ∗
      (∃ ed : GoInterface, globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed) ∗
      (∃ eof : GoInterface, globalAddr io.EOF ↦□ eof) := by
  iintro #Hpkg
  ihave #Hh : isPkgInit (PROP := IProp GF) pkg_id.net.http $$ []
  · iPkgInit
  ihave #Hio : isPkgInit (PROP := IProp GF) pkg_id.io $$ []
  · iPkgInit
  ihave #Hbufio : isPkgInit (PROP := IProp GF) pkg_id.bufio $$ []
  · iPkgInit
  ihave #Hpoll : isPkgInit (PROP := IProp GF) pkg_id.internal.poll $$ []
  · iPkgInit
  ihave #Henv := net.http.httpEnv_access $$ Hh
  ihave #Hed := poll_ed $$ Hpoll
  ihave #Hinit := _root_.Perennial.io.isInit_access $$ Hio
  icases Hinit with ⟨-, -, -, -, #HEOF, -⟩
  unfold errors.newVar
  icases HEOF with ⟨%xe, #Hxe, -⟩
  iframe Henv Hio Hbufio Hed
  iexists _
  iexact Hxe

/-! ## The client's requests -/

/-- A request's slot facts, its body saved at its ghost name (not junk). -/
theorem slotFacts_req (d : DReq) (hd : d.ok) (hj : d ≠ .junk) (τ : GName) :
    dghostVar τ DFrac.discard d.body ⊢
      net.http.slotFacts drvP (.inl (d.hreq, τ, d.body)) := by
  iintro #Hτ
  simp only [net.http.slotFacts, drvP]
  isplitr
  · imodintro
    iexists d.body
    iframe Hτ
    ipureintro
    exact ⟨d, hd, hj, rfl, rfl⟩
  isplitr
  · imodintro
    iintro %B' -
    itrivial
  · imodintro
    iexact Hτ

theorem slotFacts_dslot (d : DReq) (hd : d.ok) (τ : GName) :
    dghostVar τ DFrac.discard d.body ⊢
      net.http.slotFacts drvP (d.slot τ) := by
  cases d with
  | junk =>
    show dghostVar τ DFrac.discard DReq.junk.body ⊢ iprop(True)
    iintro -
    itrivial
  | echo m v b => exact slotFacts_req (.echo m v b) hd nofun τ
  | status => exact slotFacts_req .status hd nofun τ
  | nope w => exact slotFacts_req (.nope w) hd nofun τ

/-- What the client writes for the slot `d.slot τ` after the slots `L` (all requests) meets
`httpReqP`. -/
theorem reqP_snoc (cn : Nat) (γ : GName) (L : List ReqSlot) (d : DReq) (hd : d.ok) (τ : GName)
    (hL : ∀ x ∈ L, net.http.slotOk x ∧ x.isLeft = true) :
    net.http.httpConn (Gg := hG.goose_globalGS) cn γ ∗ monoListLbOwn γ (L ++ [d.slot τ]) ∗
      ([∗list] s ∈ L, net.http.slotFacts drvP s) ∗
      dghostVar τ DFrac.discard d.body ⊢
    □ net.http.httpReqP (Gg := hG.goose_globalGS) drvP cn (net.http.slotsWire L ++ d.wire) := by
  iintro ⟨#Hc, #Hlb, #Hfs, #Hτ⟩
  imodintro
  iunfold net.http.httpReqP
  iexists γ, L ++ [d.slot τ]
  iframe Hc Hlb
  isplitr
  · ipureintro
    refine ⟨slotsOk_snoc L _ hL (slotOk_dslot d hd τ), ⟨[], ?_⟩⟩
    rw [List.append_nil, slotsWire_snoc, slotWire_dslot]
  iapply BigSepL.bigSepL_snoc.2
  isplitl []
  · iexact Hfs
  iapply slotFacts_dslot d hd τ $$ Hτ

/-! ## The client's answers -/

/-- From the client's knowledge of the answer `ρ` at index `i` (the slot `d.slot τ` after `L`), its
body read `x` (the whole body, unless it is close-delimited): what `check` takes; and unless it is
the `400`, a handler's answer delimited by its `Content-Length`, of a request slot. -/
theorem drvQ_chk (L : List ReqSlot) (d : DReq) (τ : GName) (ρ : Resp) (x : List w8) (i : Nat)
    (hi : L.length = i) (hx : ρ.close = false → x = ρ.body) :
    dghostVar τ DFrac.discard d.body ∗ drvQ (L ++ [d.slot τ]) i ρ ⊢
      ⌜chkPre d ρ.st ρ.hc x ∧ (ρ ≠ net.http.badResp →
        net.http.respOk ρ ∧ ρ.close = false ∧ ∃ y, d.slot τ = .inl y)⌝ := by
  subst hi
  iintro ⟨#Hτ, #HQ⟩
  iunfold drvQ at HQ
  icases HQ with (%Hb | ⟨%R, %τ', %B, %hs, %Hall, #HE⟩)
  · subst Hb
    ipureintro
    exact ⟨Or.inl rfl, fun h => absurd rfl h⟩
  · obtain ⟨Hi, Hok, Hcl, Hv⟩ := Hall
    have Hi' : d.slot τ = .inl (R, τ', B) := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self] at Hi
      simpa using Hi
    obtain ⟨hj, rfl, rfl, rfl⟩ := dslot_inl d τ τ' R B Hi'
    simp only [drvP]
    icases HE with ⟨%B', #HB', %Hend⟩
    ihave %Hag := dghostVar_agree _ d.body DFrac.discard B' DFrac.discard $$ Hτ HB'
    subst Hag
    ipureintro
    refine ⟨Or.inr ⟨hj, hs, Hv, ?_⟩, fun _ => ⟨Hok, Hcl, _, Hi'⟩⟩
    rw [hx Hcl]
    exact Hend

/-! ## Ghost state -/

/-- `Close`'s update, its outcome dropped. -/
theorem close_true (cn : Nat) :
    connIs (Gg := hG.goose_globalGS) cn ⊢
      |={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false st ∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false d ∗
        ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗
          netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn false st' -∗
          netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn false d' ={∅,⊤}=∗
          (True : IProp GF) := by
  iintro #Hci
  imod close_au (Gg := hG.goose_globalGS) cn false $$ Hci with ⟨%st, %dd, Hst, Hd, Hk⟩
  imodintro
  iexists st, dd
  iframe Hst Hd
  iintro %res %st' %d' %Hco Hst' Hd'
  imod Hk $$ %res %st' %d' %Hco Hst' Hd' with -
  imodintro
  itrivial

theorem sess_ml_halves {A : Type} [Pos.Countable A] (γ : GName) (l : List A) :
    monoListAuthOwn (GF := GF) γ 1 l ⊣⊢
      monoListAuthOwn γ (1 : Qp).half l ∗ monoListAuthOwn γ (1 : Qp).half l := by
  have := (monoListAuthOwn_fractional (GF := GF) γ l).fractional (1 : Qp).half (1 : Qp).half
  rwa [Qp.half_add_half] at this

theorem ml_auth_lb {A : Type} [Pos.Countable A] (γ : GName) (q : Qp) (l : List A) :
    monoListAuthOwn (GF := GF) γ q l ⊢ monoListAuthOwn γ q l ∗ monoListLbOwn γ l :=
  persistent_entails_left (monoListLbOwn_get γ q l)

end lemmas

end github_com.mit_pdos.etcd_grove.examples.net.httpdriver
end Perennial
