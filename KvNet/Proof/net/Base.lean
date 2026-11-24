-- The copy for the part `KvNet/` of `Net/Proof/net/Base.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Shared definitions of the specs of `net`'s trusted models (`Net/TrustedCode/net.lean`, project
net's `net`, over the net extension `GooseLang/Ext/Net`): `net`'s package fact (`isInit`:
`ErrClosed`, `errClosed` and `errTimeout` hold their values), the model's types as goose names them,
and the vocabulary of the specs:

* `connAt t cn s a la ra` (persistent): the `*TCPConn` `t`'s `conn` holds the id of the end `s` of
  the connection `cn`, dialed to `a` (`netConnAt`), its addresses `la`, `ra` (`netAddr`: a
  non-nil `*TCPAddr`, read-only) and its network (`tcpNet`, D23); `isConn c cn s a`: the `Conn` `c`
  is such a `t`.
* `lisAt t l x`, `isListener li l` (persistent): the `*TCPListener` `t` (the `Listener` `li`) holds
  the listener id `l` and its address `x` (its state is the node's `netLis l a o`, which its owner
  keeps).
* The errors (D14): `opErr op src addr e err` (`err` a new `*OpError`, read-only, with `Err` `e`),
  `kindErr k ed nm e` (`e` the `Err` of a failure of kind `k`: `closedErr` = `poll.ErrNetClosing`,
  `ed` = `poll.ErrDeadlineExceeded`'s value, or `sysErr nm e`, an `*os.SyscallError`), `resErr res
  ...` (a result's error), `ErrFlag` (what `OpError.Timeout`/`Temporary` answer); `netErr err` (a
  non-nil `*OpError`), with `resErr_netErr`.
-/
module

public import KvNet.GeneratedProof.net
public import KvNet.ManualProof.net
public import GooseLang.Ext.Net.Specs
public import Perennial.Proof.io.Base
public import Perennial.Proof.time.Base
public import Proof.os.PkgInit
public import Perennial.Proof.context.Base
public import Perennial.Proof.errors.Base

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Net

namespace net

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.FieldAssumptions]

/-- `poll.ErrNetClosing` as an `error` (`errNetClosing{}`): `net.ErrClosed`'s value, the `Err` of
a failure of kind `closed`. -/
def closedErr : GoInterface :=
  interface.mkOk internal.poll.errNetClosing.ty #(zero_val internal.poll.errNetClosing)

/-- `net`'s package fact: `ErrClosed` and `errClosed` hold `poll.ErrNetClosing`, and `errTimeout`
a `*timeoutError`, for good (Go never writes them after initialization). -/
abbrev isInit : IProp GF := iprop(
  "#HErrClosed" ∷ globalAddr ErrClosed ↦□ closedErr ∗
  "#HerrClosed" ∷ globalAddr errClosed ↦□ (zero_val internal.poll.errNetClosing) ∗
  "#HerrTimeout" ∷ ∃ p : Loc,
    globalAddr errTimeout ↦□ interface.mkOk (go.GoType.PointerType timeoutError.ty) #p)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.net :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.net :=
  build_get_is_pkg_init_wf

theorem conn_ty_eq' : model.conn = conn.ty := by unfold conn.ty; rfl
theorem TCPConn_ty_eq : model.TCPConn = TCPConn.ty := by unfold TCPConn.ty; rfl
theorem TCPListener_ty_eq : model.TCPListener = TCPListener.ty := by unfold TCPListener.ty; rfl
theorem OpError_ty_eq : model.OpError = OpError.ty := by unfold OpError.ty; rfl
theorem Conn_ty_eq : model.Conn = Conn.ty := by unfold Conn.ty; rfl
theorem Listener_ty_eq : model.Listener = Listener.ty := by unfold Listener.ty; rfl

theorem TCPAddr_ty_eq : model.TCPAddr = TCPAddr.ty := by unfold TCPAddr.ty; rfl
theorem IP_ty_eq : model.IP = IP.ty := by unfold IP.ty; rfl
theorem Addr_ty_eq' : model.Addr = Addr.ty := by unfold Addr.ty; rfl
theorem Errno_ty_eq : model.Errno = syscall.Errno.ty := by unfold syscall.Errno.ty; rfl
theorem timeoutError_ty_eq : model.timeoutError = timeoutError.ty := by unfold timeoutError.ty; rfl

/-! ### Networks (D23) -/

/-- The networks the models accept: `"tcp"` and `"tcp4"` (`model.netOk`). -/
def tcpNet (nw : GoString) : Prop := nw = go!"tcp" ∨ nw = go!"tcp4"

theorem tcpNet_tcp : tcpNet go!"tcp" := .inl rfl
theorem tcpNet_tcp4 : tcpNet go!"tcp4" := .inr rfl

/-! ### Addresses (D18) -/

/-- `x` is a non-nil `*TCPAddr` (as an `Addr`), read-only for good. -/
def netAddr (x : GoInterface) : IProp GF :=
  iprop(∃ (p : Loc) (v : TCPAddr), ⌜x = interface.mkOk (go.GoType.PointerType TCPAddr.ty) #p⌝ ∗
    p ↦□ v)

instance netAddr_persistent (x : GoInterface) : Persistent (netAddr (GF := GF) x) := by
  unfold netAddr; infer_instance

/-! ### Connections and listeners -/

/-- The `*TCPConn` `t` is the end `s` of the connection `cn`, dialed to `a`, with the addresses `la`
(`LocalAddr`) and `ra` (`RemoteAddr`), on a network `"tcp"` or `"tcp4"` (D23). -/
def connAt (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) : IProp GF :=
  iprop(∃ nw, ⌜tcpNet nw⌝ ∗ t ↦□ (TCPConn.mk (conn.mk (endId cn s) la ra nw)) ∗ netAddr la ∗
    netAddr ra ∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a)

instance connAt_persistent (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    Persistent (connAt (GF := GF) t cn s a la ra) := by
  unfold connAt; infer_instance

theorem connAt_conn (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    connAt (GF := GF) t cn s a la ra ⊢
      netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a := by
  unfold connAt; iintro ⟨%nw, -, -, -, -, H⟩; iexact H

/-- The `Conn` `c` is the end `s` of the connection `cn`, dialed to `a`: a `*TCPConn` `t` with
`connAt t cn s a la ra`. A method call on `c` resolves (`wp_auto`, once `c` is destructed) to the
`*TCPConn`'s method, the form the `Conn` specs are stated in. -/
def isConn (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) : IProp GF :=
  iprop(∃ (t : Loc) (la ra : GoInterface),
    ⌜c = interface.mkOk (go.GoType.PointerType TCPConn.ty) #t⌝ ∗ connAt t cn s a la ra)

instance isConn_persistent (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) :
    Persistent (isConn (GF := GF) c cn s a) := by
  unfold isConn; infer_instance

/-- The `*TCPListener` `t` is this node's listener `l`, with the address `x` (`Addr`), on a
network `"tcp"` or `"tcp4"` (D23). -/
def lisAt (t : Loc) (l : w64) (x : GoInterface) : IProp GF :=
  iprop(∃ nw, ⌜tcpNet nw⌝ ∗ t ↦□ (TCPListener.mk l x nw) ∗ netAddr x ∗ ⌜l ≠ 0⌝)

instance lisAt_persistent (t : Loc) (l : w64) (x : GoInterface) :
    Persistent (lisAt (GF := GF) t l x) := by
  unfold lisAt; infer_instance

/-- The `Listener` `li` is the listener `l` of this node (its state is the node's
`netLis l a o`, which its owner keeps). -/
def isListener (li : GoInterface) (l : w64) : IProp GF :=
  iprop(∃ (t : Loc) (x : GoInterface),
    ⌜li = interface.mkOk (go.GoType.PointerType TCPListener.ty) #t⌝ ∗ lisAt t l x)

instance isListener_persistent (li : GoInterface) (l : w64) :
    Persistent (isListener (GF := GF) li l) := by
  unfold isListener; infer_instance

/-! ### Errors (D14) -/

/-- `e` is an `*os.SyscallError` (as an `error`) around a nonzero `syscall.Errno`, its system call
named as `nm` allows: the `Err` of a failure of kind `sys`. -/
def sysErr (nm : GoString → Prop) (e : GoInterface) : IProp GF :=
  iprop(∃ (p : Loc) (name : GoString) (n : w64),
    ⌜e = interface.mkOk (go.GoType.PointerType os.SyscallError.ty) #p ∧ nm name ∧ n ≠ 0⌝ ∗
    p ↦□ (os.SyscallError.mk name (interface.mkOk syscall.Errno.ty #n)))

instance sysErr_persistent (nm : GoString → Prop) (e : GoInterface) :
    Persistent (sysErr (GF := GF) nm e) := by
  unfold sysErr; infer_instance

/-- `e` is the bare `syscall.Errno` (as an `error`, not in an `*os.SyscallError`) of a failed
registration of a new socket with the poller (D6, D12; `model.epollErr`): `ENOMEM` (12) or `ENOSPC`
(28) of `epoll_ctl(2)`. A failed `Listen`'s `Err` may be one. -/
def epollErr (e : GoInterface) : Prop :=
  e = interface.mkOk syscall.Errno.ty #(W64 12) ∨ e = interface.mkOk syscall.Errno.ty #(W64 28)

/-- `e` is the `Err` of a failure of kind `k`: `poll.ErrNetClosing` (`closed`), the value of
`poll.ErrDeadlineExceeded` (`timeout`; `ed`, for an operation that may time out, else no timeout),
an `*os.SyscallError` (`sys`, named as `nm` allows). -/
def kindErr (k : NetErr) (ed : Option GoInterface) (nm : GoString → Prop) (e : GoInterface) :
    IProp GF :=
  match k, ed with
  | .closed, _ => iprop(⌜e = closedErr⌝)
  | .timeout, some ed => iprop(⌜e = ed⌝)
  | .timeout, none => iprop(False)
  | .sys, _ => sysErr nm e

instance kindErr_persistent (k : NetErr) (ed : Option GoInterface) (nm : GoString → Prop)
    (e : GoInterface) : Persistent (kindErr (GF := GF) k ed nm e) := by
  cases k <;> cases ed <;> unfold kindErr <;> infer_instance

/-- `err` is a new `*OpError` (as an `error`, read-only for good) of the operation `op` on a
network `"tcp"` or `"tcp4"` (D23: the call's, connection's or listener's), with `Source` `src`,
`Addr` `addr` and `Err` `e`. -/
def opErr (op : GoString) (src addr e err : GoInterface) : IProp GF :=
  iprop(∃ (pe : Loc) (nw : GoString),
    ⌜err = interface.mkOk (go.GoType.PointerType OpError.ty) #pe ∧ tcpNet nw⌝ ∗
    pe ↦□ (OpError.mk op nw src addr e))

instance opErr_persistent (op : GoString) (src addr e err : GoInterface) :
    Persistent (opErr (GF := GF) op src addr e err) := by
  unfold opErr; infer_instance

/-- The error of an operation `op` (`Source` `src`, `Addr` `addr`) whose result is `res`
(`Net.errCode`'s): `nil` for success, else an `*OpError` whose `Err` is the kind's (`kindErr`). -/
def resErr (res : Option NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) : IProp GF :=
  match res with
  | none => iprop(⌜err = interface.nil⌝)
  | some k => iprop(∃ e, opErr op src addr e err ∗ kindErr k ed nm e)

instance resErr_persistent (res : Option NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    Persistent (resErr (GF := GF) res op src addr ed nm err) := by
  cases res <;> unfold resErr <;> infer_instance

/-- What `OpError.Timeout` and `Temporary` may answer for the `Err` `e` (D14): `false` for
`poll.ErrNetClosing`'s type, `true` for `*poll.DeadlineExceededError` and `*timeoutError`, anything
otherwise. -/
def ErrFlag (e : GoInterface) (b : Bool) : Prop :=
  match e with
  | interface.ok ii => (ii.ty = internal.poll.errNetClosing.ty → b = false) ∧
      (ii.ty = go.GoType.PointerType internal.poll.DeadlineExceededError.ty → b = true) ∧
      (ii.ty = go.GoType.PointerType timeoutError.ty → b = true)
  | interface.nil => True

/-- A failure's error: a non-nil `*OpError`. -/
def netErr (err : GoInterface) : Prop :=
  ∃ pe : Loc, err = interface.mkOk (go.GoType.PointerType OpError.ty) #pe

theorem netErr_ne_nil {err : GoInterface} (h : netErr err) : err ≠ interface.nil := by
  obtain ⟨pe, rfl⟩ := h; intro h; cases h

/-- An `*OpError` is a failure's error. -/
theorem opErr_netErr (op : GoString) (src addr e err : GoInterface) :
    opErr (GF := GF) op src addr e err ⊢ ⌜netErr err⌝ := by
  unfold opErr; iintro ⟨%pe, %nw, %h, -⟩; ipureintro; exact ⟨pe, h.1⟩

/-- A failure's `resErr` is a failure's error; a success's is `nil`. -/
theorem resErr_netErr (res : Option NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) :
    resErr (GF := GF) res op src addr ed nm err ⊢
      ⌜(res = none → err = interface.nil) ∧ (res ≠ none → netErr err)⌝ := by
  cases res
  · unfold resErr; iintro %h; ipureintro; exact ⟨fun _ => h, fun h => absurd rfl h⟩
  · unfold resErr opErr; iintro ⟨%e, ⟨%pe, %nw, %h, -⟩, -⟩
    ipureintro; exact ⟨fun h => (by cases h), fun _ => ⟨pe, h.1⟩⟩

end def_

end net
end Perennial
