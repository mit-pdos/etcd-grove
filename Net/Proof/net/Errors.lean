/-
The Go model's helpers and `netFD` methods (`models/net/model.go`, translated; over the primitive
stubs of `Net/TrustedCode/net.lean`), as WP lemmas the proofs of `net`'s specs use: the stubs
(`extAny*`), the errors (`closedErr`, `kindErr`, `codeErr`: `kindErr`'s and `resKind`'s predicates
of `Base.lean`), the addresses (`anyTCPAddr`: `netAddr`), `netOk`, the `netFD`s the model makes
(`modelFD`, `newConn`: `fdAt`, `isConn`), Go's `conn.ok`/`TCPListener.ok`, and `netFD`'s methods
(one lemma per model: the extension's operation, then the result's error).
-/
module

public import Net.Proof.net.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

/-! ### The primitive stubs that answer arbitrarily -/

theorem wp_extAnyString (Φ : val → IProp GF) :
    (∀ s : GoString, Φ #s) -∗ WP (App (Val (@! net.extAnyString)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyString
  iexact HΦ

theorem wp_extAnyW64 (Φ : val → IProp GF) :
    (∀ n : w64, Φ #n) -∗ WP (App (Val (@! net.extAnyW64)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyW64
  iexact HΦ

theorem wp_extAnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ #b) -∗ WP (App (Val (@! net.extAnyBool)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyBool
  iexact HΦ

theorem wp_extAnyErrno (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n ≠ 0⌝ -∗ Φ #n) -∗ WP (App (Val (@! net.extAnyErrno)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_net_AnyErrno
  iexact HΦ

/-! ### Errors (D14) -/

theorem wp_closedErr (Φ : val → IProp GF) :
    Φ #closedErr -∗ WP (App (Val (@! net.closedErr)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  wp_auto
  unfold closedErr
  iexact HΦ

/-- The `Err` of a failure of kind `k` (its code `c`), `name` the system call's. -/
theorem wp_kindErr (k : NetErr) (ed : Option GoInterface) (name : GoString)
    (nm : GoString → Prop) (hnm : nm name) {c : w64} (hc : c = errCode (some k))
    (Φ : val → IProp GF) :
    edAt (GF := GF) k ed -∗ (∀ e, kindErr (GF := GF) k ed nm e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.kindErr)) (Val #c)) (Val #name)) {{ Φ }} := by
  subst hc
  iintro Hed HΦ
  wp_func_call; wp_call
  cases k
  · wp_auto
    wp_apply wp_closedErr
    wp_auto
    iapply HΦ
    unfold kindErr
    ipureintro; rfl
  · cases ed with
    | none => unfold edAt; iexfalso; iexact Hed
    | some e =>
      unfold edAt
      wp_auto
      iapply HΦ
      unfold kindErr
      ipureintro; rfl
  · wp_auto
    wp_apply wp_extAnyErrno as %n %hn
    wp_alloc p as Hp
    ipersist Hp
    wp_auto
    iapply HΦ
    unfold kindErr sysErr
    iexists p, name, n
    isplitr
    · ipureintro; exact ⟨rfl, hnm, hn⟩
    iexact Hp

/-- `codeErr(c, name)`: `nil` for success, else the kind's error. -/
theorem wp_codeErr (res : Option NetErr) (ed : Option GoInterface) (name : GoString)
    (nm : GoString → Prop) (hnm : nm name) {c : w64} (hc : c = errCode res)
    (Φ : val → IProp GF) :
    (match res with | some k => edAt (GF := GF) k ed | none => iprop(True)) -∗
    (∀ e, resKind (GF := GF) res ed nm e -∗ Φ #e) -∗
    WP (App (App (Val (@! net.codeErr)) (Val #c)) (Val #name)) {{ Φ }} := by
  subst hc
  iintro Hed HΦ
  wp_func_call; wp_call
  cases res with
  | none =>
    wp_auto
    iapply HΦ
    unfold resKind
    ipureintro; rfl
  | some k =>
    have hk : errCode (some k) ≠ W64 0 := by cases k <;> decide
    wp_auto
    wp_apply wp_kindErr k ed name nm hnm rfl $$ Hed as %e #He
    wp_auto
    iapply HΦ
    unfold resKind
    iexact He

/-! ### Addresses (D18) and networks (D23) -/

theorem wp_anyTCPAddr (Φ : val → IProp GF) :
    (∀ x, netAddr (GF := GF) x -∗ Φ #x) -∗
    WP (App (Val (@! net.anyTCPAddr)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_extAnyString as %z
  wp_apply wp_string_to_bytes z as %sl ⟨-, -⟩
  wp_apply wp_extAnyW64 as %port
  wp_apply wp_extAnyString as %zone
  wp_alloc p as Hp
  ipersist Hp
  wp_auto
  iapply HΦ
  unfold netAddr
  iexists p, _
  isplitr
  · ipureintro; rfl
  iexact Hp

/-- D23. The networks the model accepts (`netOk`): `true` for `"tcp"` and `"tcp4"`. -/
theorem wp_netOk (nw : GoString) (hnw : tcpNet nw) (Φ : val → IProp GF) :
    Φ #true -∗ WP (App (Val (@! net.netOk)) (Val #nw)) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  rcases hnw with rfl | rfl
  · wp_auto; iexact HΦ
  · wp_auto; iexact HΦ

/-! ### The `netFD`s the model makes -/

/-- `modelFD(id, nw, la, ra)`: a new `netFD`, read-only for good. -/
theorem wp_modelFD (id : w64) (nw : GoString) (la ra : GoInterface) (Φ : val → IProp GF) :
    (∀ fd : Loc, fdAt (GF := GF) fd id nw la ra -∗ Φ #fd) -∗
    WP (App (App (App (App (Val (@! net.modelFD)) (Val #id)) (Val #nw)) (Val #la)) (Val #ra))
      {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  wp_auto
  wp_alloc fd as Hfd
  ipersist Hfd
  wp_auto
  iapply HΦ
  unfold fdAt
  iexists _
  iframe Hfd
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A new `*TCPConn` for the end `s` of `cn` on the network `nw`, with new addresses. -/
theorem wp_newConn (cn : Nat) (s : Bool) (a nw : GoString) (Φ : val → IProp GF) :
    ⌜tcpNet nw⌝ -∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
    (∀ c, isConn (GF := GF) c cn s a -∗ Φ #c) -∗
    WP (App (App (Val (@! net.newConn)) (Val #(endId cn s))) (Val #nw)) {{ Φ }} := by
  iintro %hnw #Hat HΦ
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_anyTCPAddr as %la #Hla
  wp_auto
  wp_apply wp_anyTCPAddr as %ra #Hra
  wp_auto
  wp_apply wp_modelFD as %fd #Hfd
  wp_alloc t as Ht
  ipersist Ht
  wp_auto
  iapply HΦ
  unfold isConn connAt connFd
  iexists t, la, ra
  isplitr
  · ipureintro; rfl
  iexists nw
  iframe Hat Hla Hra
  isplitr
  · ipureintro; exact hnw
  iexists fd
  iframe Ht Hfd

/-! ### `ok()`: Go's `c != nil && c.fd != nil` -/

/-- `(*conn).ok()` on a `conn` holding a non-nil `fd`: `true`. -/
theorem wp_conn_ok (c fd : Loc) (hfd : fd ≠ null) (Φ : val → IProp GF) :
    (c ↦□ (conn.mk fd) : IProp GF) -∗ Φ #true -∗
    WP (App (Val #(methods (go.GoType.PointerType conn.ty) go!"ok" #c)) (Val #())) {{ Φ }} := by
  iintro #Hc HΦ
  ihave %hc := typedPointsto_not_null _ _ _ $$ Hc
  wp_method_call; wp_call
  wp_auto
  trace_state
  sorry

/-! ### `netFD`'s methods (the model) -/

/-- D3. `fd.Close()`: the extension's `Close` of the end, then the result's error. -/
theorem wp_fd_Close (fd : Loc) (cn : Nat) (s : Bool) (a nw : GoString) (la ra : GoInterface)
    (Q : Option NetErr → IProp GF) (Φ : val → IProp GF) :
    fdAt (GF := GF) fd (endId cn s) nw la ra -∗
    netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a -∗
    (|={⊤,∅}=> ∃ st d, netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st ∗
      netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d ∗
      ∀ res st' d', ⌜CloseOutcome st d res st' d'⌝ -∗
        netEnd (extGlobalGS netExt (G := hG.goose_globalGS)) cn s st' -∗
        netDir (extGlobalGS netExt (G := hG.goose_globalGS)) cn s d' ={∅,⊤}=∗ Q res) -∗
    (∀ res e, Q res -∗ resKind (GF := GF) res none (· = go!"close") e -∗ Φ #e) -∗
    WP (App (Val #(methods (go.GoType.PointerType netFD.ty) go!"Close" #fd)) (Val #())) {{ Φ }} := by
  iintro #Hfd #Hat HAU HΦ
  unfold fdAt
  icases Hfd with ⟨%v, %hv, #Hv⟩
  obtain ⟨hid, -, -, -⟩ := hv
  wp_method_call; wp_call
  wp_auto
  trace_state
  sorry

end proof

end net
end Perennial
