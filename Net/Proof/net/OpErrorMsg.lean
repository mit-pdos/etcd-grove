/-
`(*OpError).Error()` over Go's own code (`OpError.Error.impl`, `net.go`), under `opErrOk` (D2,
precondition approved by Upamanyu): a message of Go's form, its operation, some string (the network
and the addresses), `": "`, the error's message (`opErrMsg`, `wp_OpError_Error`). The callees are
translated Go but for `TCPAddr.String` (the model's arbitrary string) and `syscall.Errno.Error`
(translated: some string, given `syscall`'s package fact, `errno_stringMethodSpecLe`; so
`errStr` is conditional on `syscall.errnoOk`, and so is `wp_OpError_Error`).
-/
module

public import Net.Proof.net.Errors
public import Proof.syscall.ErrorOk

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net

namespace net

/-- Go's form of an `*OpError`'s message (`OpError.Error`, `net.go`): the operation `op`, some
string (the network and the addresses), `": "`, some string (the error's message). -/
def opErrMsg (op msg : GoString) : Prop :=
  ∃ s1 s2 : GoString, msg = op ++ s1 ++ go!": " ++ s2

theorem opErrMsg_ne (op msg : GoString) (h : opErrMsg op msg) : msg ≠ [] := by
  obtain ⟨s1, s2, rfl⟩ := h
  simp

/-- `m` starts with `op`. -/
def opPrefix (op m : GoString) : Prop := ∃ s1 : GoString, m = op ++ s1

theorem opPrefix_self (op : GoString) : opPrefix op op := ⟨[], by simp⟩

theorem opPrefix_append {op m : GoString} (x : GoString) (h : opPrefix op m) :
    opPrefix op (m ++ x) := by
  obtain ⟨s1, rfl⟩ := h
  exact ⟨s1 ++ x, by simp⟩

theorem opErrMsg_of_prefix {op m : GoString} (s2 : GoString) (h : opPrefix op m) :
    opErrMsg op (m ++ (go!": " ++ s2)) := by
  obtain ⟨s1, rfl⟩ := h
  exact ⟨s1, s2, by simp⟩

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

/-- `syscall.Errno(n).Error()`: some string, given `syscall`'s package fact
(`errno_stringMethodSpecLe`). -/
private theorem wp_Errno_Error (n : w64) (Φ : val → IProp GF) :
    syscall.errnoOk (GF := GF) -∗ (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods syscall.Errno.ty go!"Error" #n)) (Val #())) {{ Φ }} := by
  iintro #Hok HΦ
  ihave #H := errno_stringMethodSpecLe (GF := GF) n $$ Hok
  iunfold EtcdGrove.stringMethodSpecLe at H
  iapply H
  inext
  iintro %s -
  iapply HΦ

/-- `TCPAddr.String`'s model: some string. -/
private theorem wp_TCPAddr_String (p : Loc) (Φ : val → IProp GF) :
    (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods (go.GoType.PointerType TCPAddr.ty) go!"String" #p)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_method_call
  unfold TCPAddr.String.impl
  wp_auto
  wp_apply wp_extAnyString as %s
  iapply HΦ

private theorem wp_errStr (ii : GoInterfaceOk) (Φ : val → IProp GF) :
    _root_.Perennial.fmt.stringMethodSpec (GF := GF) ii go!"Error" -∗ (∀ s : GoString, Φ #s) -∗
    WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }} := by
  iintro #H HΦ
  rw [_root_.Perennial.fmt.stringMethodSpec_unfold]
  iapply H
  inext
  iexact HΦ

/-- net's own errors (`netOwnErr`) have an `Error()` (translated Go, but for `Errno`'s). -/
theorem netOwnErr_errStr (e : GoInterface) : netOwnErr (GF := GF) e ⊢ errStr e := by
  unfold netOwnErr sysErr errStr
  haveI : go.NotInterface go.uintptr := ⟨by simp [go.uintptr]⟩
  iintro #He
  icases He with (%he | ⟨%p, %he⟩ | ⟨%p, %he⟩ | ⟨%p, %name, %n, %he, #Hp⟩)
  all_goals (first | (rw [he.1]; ihave #Hp2 := Hp; iStructNamed Hp2) | (rw [he]; (try unfold closedErr)))
  all_goals
    iexists _
    isplitr
    · ipureintro; rfl
    imodintro
    iintro #Hsys
    rw [_root_.Perennial.fmt.stringMethodSpec_unfold]
    imodintro
    iintro %Φ HΦ
    repeat' (first | (wp_apply wp_Errno_Error $$ Hsys as %es) | (wp_method_call) | (wp_func_call; wp_call) |
      (dsimp only) | (wp_auto) | (wp_call) |
      (unfold internal.poll.errNetClosing.Error.impl) |
      (unfold internal.poll.DeadlineExceededError.Error.impl) |
      (unfold timeoutError.Error.impl) | (unfold os.SyscallError.Error.impl))
    all_goals (first | iapply HΦ | (inext; iapply HΦ))

theorem addrOrNil_addr (x : GoInterface) : netAddr (GF := GF) x ⊢ addrOrNil x := by
  unfold addrOrNil; iintro #H; iright; iexact H

theorem addrOrNil_nil : ⊢ addrOrNil (GF := GF) interface.nil := by
  unfold addrOrNil; ileft; ipureintro; rfl

/-- A failure's error, as the wrappers build it: the new `*OpError` `pe` around the kind's `Err`
(net's own, given `edTyped ed`), with addresses `nil` or `netAddr`s. -/
theorem resErr_intro {k : NetErr} {op : GoString} {src addr e : GoInterface}
    {ed : Option GoInterface} {nm : GoString → Prop} {pe : Loc} {nw : GoString}
    (hnw : tcpNet nw) (hed : edTyped ed) :
    pe ↦□ (OpError.mk op nw src addr e) -∗ kindErr (GF := GF) k ed nm e -∗
    addrOrNil src -∗ addrOrNil addr -∗
    resErr (some k) op src addr ed nm (interface.mkOk (go.GoType.PointerType OpError.ty) #pe) := by
  iintro #Hpe #He #Hs #Ha
  ihave #Hown := kindErr_netOwnErr k ed nm e hed $$ He
  ihave #Hes := netOwnErr_errStr e $$ Hown
  unfold resErr opErr
  iexists e
  iframe He Hes Hs Ha
  iexists pe, nw
  iframe Hpe
  ipureintro; exact ⟨rfl, hnw⟩

/-- What `OpError.Error` needs of `v` (weaker than `opErrOk`): `Err` has an `Error()`
(`errStr`), `Source` and `Addr` are nil or a `netAddr`. -/
def opErrMsgOk (v : net.OpError) : IProp GF :=
  iprop(errStr v.Err' ∗ addrOrNil v.Source' ∗ addrOrNil v.Addr')

instance opErrMsgOk_persistent (v : net.OpError) : Persistent (opErrMsgOk (GF := GF) v) := by
  unfold opErrMsgOk; infer_instance

theorem opErrOk_opErrMsgOk (v : net.OpError) : opErrOk (GF := GF) v ⊢ opErrMsgOk v := by
  unfold opErrOk opErrMsgOk
  iintro ⟨#He, #Hs, #Ha⟩
  isplitr
  · iapply netOwnErr_errStr $$ He
  iframe Hs Ha

set_option maxHeartbeats 2000000 in
/-- `e.Error()` on an `*OpError` `pe` whose `Err` has an `Error()` and whose addresses net made
(`opErrMsgOk`; `opErrOk` gives it): a message of Go's form (`opErrMsg`) for its `Op`. -/
theorem wp_OpError_Error (pe : Loc) (v : net.OpError) (Φ : val → IProp GF) :
    (pe ↦□ v : IProp GF) -∗ opErrMsgOk v -∗ syscall.errnoOk (GF := GF) -∗
      ▷ (∀ msg : GoString, ⌜opErrMsg v.Op' msg⌝ -∗ Φ #msg) -∗
    WP (App (Val #(methods (go.GoType.PointerType OpError.ty) go!"Error" #pe)) (Val #()))
      {{ Φ }} := by
  iintro #Hpe #Hok #Hsys HΦ
  ihave %hnn := typedPointsto_not_null _ _ _ $$ Hpe
  ihave #H2 := Hpe
  iStructNamed H2
  unfold opErrMsgOk errStr addrOrNil
  icases Hok with ⟨⟨%ii, %he, #He0⟩, #Hs, #Ha⟩
  ihave #He := He0 $$ Hsys
  wp_method_call
  wp_call
  wp_auto
  rw [decide_eq_false hnn]
  wp_auto
  unfold netAddr
  rw [he]
  icases Hs with (%hs | ⟨%ps, %vs, %hs, #Hps⟩) <;> rw [hs] <;>
  icases Ha with (%ha | ⟨%pa, %aa, %ha, #Hpa⟩) <;> rw [ha]
  all_goals
    repeat' (first | (wp_if_destruct) | (wp_apply wp_TCPAddr_String as %ts) |
      (wp_apply wp_errStr $$ He as %es) | (wp_method_call) |
      (wp_func_call; wp_call) | (wp_auto) | (dsimp only))
  all_goals
    iapply HΦ
    ipureintro
    apply opErrMsg_of_prefix
    repeat (apply opPrefix_append)
    exact opPrefix_self _

/-- An error whose `Error()` returns a fixed string (`errors.New`'s, `errors.newVar`'s) has
`errStr`. -/
theorem errStr_of_wp (ii : GoInterfaceOk) (s : GoString) :
    (□ ∀ Φ : val → IProp GF, ▷ Φ #s -∗
      WP (App (Val #(methods ii.ty go!"Error" ii.v)) (Val #())) {{ Φ }}) ⊢
      errStr (interface.ok ii) := by
  iintro #H
  unfold errStr
  iexists ii
  isplitr
  · ipureintro; rfl
  imodintro
  iintro -
  rw [_root_.Perennial.fmt.stringMethodSpec_unfold]
  imodintro
  iintro %Φ HΦ
  iapply H
  inext
  iapply HΦ

/-- A failure's error (`resErr (some k)`, an `*OpError`) has an `Error()`. -/
theorem resErr_errStr (k : NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    resErr (GF := GF) (some k) op src addr ed nm err ⊢ errStr err := by
  unfold resErr opErr
  iintro ⟨%e, ⟨%pe, %nw, ⟨%Herr, -⟩, #Hpe⟩, -, #Hes, #Hs, #Ha⟩
  subst Herr
  ihave #Hok : opErrMsgOk (GF := GF) (OpError.mk op nw src addr e) $$ []
  · unfold opErrMsgOk; iframe Hes Hs Ha
  unfold errStr
  iexists ⟨go.GoType.PointerType OpError.ty, #pe⟩
  isplitr
  · ipureintro; rfl
  imodintro
  iintro #Hsys
  rw [_root_.Perennial.fmt.stringMethodSpec_unfold]
  imodintro
  iintro %Φ HΦ
  iapply wp_OpError_Error $$ Hpe Hok Hsys
  inext
  iintro %msg -
  iapply HΦ

end proof

end net
end Perennial