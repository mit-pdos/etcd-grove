-- The copy for the part `KvRaft/` of `Net/Proof/net/Base.lean` (etc/copy-part.py; rerun it, do not edit).
/-
Shared definitions of the specs of `net` (project net's `net`: Go's code down to `netFD`, the Go
model under it, `models/net/model.go`, over the net extension `GooseLang/Ext/Net`'s primitive stubs,
`Net/TrustedCode/net.lean`): `net`'s package fact (`isInit`: `ErrClosed`, `errClosed` and
`errTimeout` hold their values) and the vocabulary of the specs:

* `connAt t cn s a la ra` (persistent): the `*TCPConn` `t`'s `conn` points to a `netFD`
  (`connFd`, `fdAt`) holding, in Go's `pfd.Sysfd`, the id of the end `s` of the connection `cn`,
  dialed to `a` (`netConnAt`), its addresses `la`, `ra` (`netAddr`: a non-nil `*TCPAddr`,
  read-only) and its network (`tcpNet`, D23); `isConn c cn s a`: the `Conn` `c`
  is such a `t`.
* `lisAt t l x`, `isListener li l` (persistent): the `*TCPListener` `t` (the `Listener` `li`) points
  to a `netFD` holding the listener id `l` and its address `x` (its state is the node's `netLis l a o`, which its owner
  keeps).
* The errors (D14): `opErr op src addr e err` (`err` a new `*OpError`, read-only, with `Err` `e`),
  `kindErr k ed nm e` (`e` the `Err` of a failure of kind `k`: `closedErr` = `poll.ErrNetClosing`,
  `ed` = `poll.ErrDeadlineExceeded`'s value, or `sysErr nm e`, an `*os.SyscallError`), `resErr res
  ...` (a result's error), `ErrFlag` (what `OpError.Timeout`/`Temporary` answer); `netErr err` (a
  non-nil `*OpError`), with `resErr_netErr`; `opErrOk v` (the precondition of `OpError`'s
  `Error`/`Timeout`/`Temporary`, approved by Upamanyu, D2: `Err` one of net's own errors,
  `netOwnErr`, and `Source`/`Addr` nil or a `netAddr`).
-/
module

public import KvRaft.GeneratedProof.net
public import GooseLang.Ext.Net.Specs
public import Perennial.Proof.io.Base
public import Perennial.Proof.time.Base
public import Proof.os.PkgInit
public import Proof.internal.poll.PkgInit
public import Perennial.Proof.context.Base
public import Perennial.Proof.errors.Base
public import Perennial.Proof.fmt.Args

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
variable [package_sem' : net.Assumptions]

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

/-- The `netFD` `fd` (read-only for good) holds the id `id` in Go's `pfd.Sysfd`, the network `nw`
and the addresses `la` (`laddr`) and `ra` (`raddr`); and `net` is initialized (`isPkgInit net`, so
are `io`, `internal/poll`, `syscall`: what the connection's operations need, `Conn.Read`'s `io.EOF`
comparison and the errors' `Error()`, `errnoOk_of_poll`; `Dial`, `DialTimeout` and `Listen` take
it, `Accept` passes the listener's on). -/
def fdAt (fd : Loc) (id : w64) (nw : GoString) (la ra : GoInterface) : IProp GF :=
  iprop(∃ v : netFD, ⌜v.pfd'.Sysfd' = id ∧ v.net' = nw ∧ v.laddr' = la ∧ v.raddr' = ra⌝ ∗ fd ↦□ v ∗
    isPkgInit (PROP := IProp GF) pkg_id.net)

instance fdAt_persistent (fd : Loc) (id : w64) (nw : GoString) (la ra : GoInterface) :
    Persistent (fdAt (GF := GF) fd id nw la ra) := by
  unfold fdAt; infer_instance

/-- The `*TCPConn` `t` (read-only for good) holds a `conn` whose `fd` is `fdAt fd id nw la ra`. -/
def connFd (t : Loc) (id : w64) (nw : GoString) (la ra : GoInterface) : IProp GF :=
  iprop(∃ fd : Loc, t ↦□ (TCPConn.mk (conn.mk fd)) ∗ fdAt fd id nw la ra)

instance connFd_persistent (t : Loc) (id : w64) (nw : GoString) (la ra : GoInterface) :
    Persistent (connFd (GF := GF) t id nw la ra) := by
  unfold connFd; infer_instance

/-- The `*TCPConn` `t` is the end `s` of the connection `cn`, dialed to `a`, with the addresses `la`
(`LocalAddr`) and `ra` (`RemoteAddr`), on a network `"tcp"` or `"tcp4"` (D23). -/
def connAt (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) : IProp GF :=
  iprop(∃ nw, ⌜tcpNet nw⌝ ∗ connFd t (endId cn s) nw la ra ∗ netAddr la ∗
    netAddr ra ∗ netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a)

instance connAt_persistent (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    Persistent (connAt (GF := GF) t cn s a la ra) := by
  unfold connAt; infer_instance

theorem connAt_conn (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    connAt (GF := GF) t cn s a la ra ⊢
      netConnAt (extGlobalGS netExt (G := hG.goose_globalGS)) cn a := by
  unfold connAt; iintro ⟨%nw, -, -, -, -, H⟩; iexact H

theorem fdAt_net (fd : Loc) (id : w64) (nw : GoString) (la ra : GoInterface) :
    fdAt (GF := GF) fd id nw la ra ⊢ isPkgInit (PROP := IProp GF) pkg_id.net := by
  unfold fdAt; iintro ⟨%v, -, -, #H⟩; iexact H

/-- A connection's end: `net` is initialized (its `netFD`'s, `fdAt`). -/
theorem connAt_net (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    connAt (GF := GF) t cn s a la ra ⊢ isPkgInit (PROP := IProp GF) pkg_id.net := by
  unfold connAt connFd; iintro ⟨%nw, -, ⟨%fd, -, #Hfd⟩, -, -, -⟩
  iapply fdAt_net $$ Hfd

theorem connAt_poll (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    connAt (GF := GF) t cn s a la ra ⊢ isPkgInit (PROP := IProp GF) pkg_id.internal.poll := by
  iintro #H
  ihave #Hn := connAt_net $$ H
  iPkgInit

theorem connAt_io (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    connAt (GF := GF) t cn s a la ra ⊢ isPkgInit (PROP := IProp GF) pkg_id.io := by
  iintro #H
  ihave #Hn := connAt_net $$ H
  iPkgInit

/-- The `Conn` `c` is the end `s` of the connection `cn`, dialed to `a`: a `*TCPConn` `t` with
`connAt t cn s a la ra`. A method call on `c` resolves (`wp_auto`, once `c` is destructed) to the
`*TCPConn`'s method, the form the `Conn` specs are stated in. -/
def isConn (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) : IProp GF :=
  iprop(∃ (t : Loc) (la ra : GoInterface),
    ⌜c = interface.mkOk (go.GoType.PointerType TCPConn.ty) #t⌝ ∗ connAt t cn s a la ra)

instance isConn_persistent (c : GoInterface) (cn : Nat) (s : Bool) (a : GoString) :
    Persistent (isConn (GF := GF) c cn s a) := by
  unfold isConn; infer_instance

/-- The `*TCPListener` `t` (read-only for good) holds a `netFD` with the listener id `l`, the
network `nw` and the address `x` (its `laddr`). -/
def lisFd (t : Loc) (l : w64) (nw : GoString) (x : GoInterface) : IProp GF :=
  iprop(∃ (fd : Loc) (lc : ListenConfig) (ra : GoInterface),
    t ↦□ (TCPListener.mk fd lc) ∗ fdAt fd l nw x ra)

instance lisFd_persistent (t : Loc) (l : w64) (nw : GoString) (x : GoInterface) :
    Persistent (lisFd (GF := GF) t l nw x) := by
  unfold lisFd; infer_instance

/-- The `*TCPListener` `t` is this node's listener `l`, with the address `x` (`Addr`), on a
network `"tcp"` or `"tcp4"` (D23). -/
def lisAt (t : Loc) (l : w64) (x : GoInterface) : IProp GF :=
  iprop(∃ nw, ⌜tcpNet nw⌝ ∗ lisFd t l nw x ∗ netAddr x ∗ ⌜l ≠ 0⌝)

instance lisAt_persistent (t : Loc) (l : w64) (x : GoInterface) :
    Persistent (lisAt (GF := GF) t l x) := by
  unfold lisAt; infer_instance

/-- A listener: `net` is initialized (its `netFD`'s, `fdAt`). -/
theorem lisAt_net (t : Loc) (l : w64) (x : GoInterface) :
    lisAt (GF := GF) t l x ⊢ isPkgInit (PROP := IProp GF) pkg_id.net := by
  unfold lisAt lisFd; iintro ⟨%nw, -, ⟨%fd, %lc, %ra, -, #Hfd⟩, -, -⟩
  iapply fdAt_net $$ Hfd

/-- `syscall`'s package fact (what an `*os.SyscallError`'s `Error()` needs, `errStr`), from
`internal/poll`'s (which imports `syscall`). -/
theorem errnoOk_of_poll :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ⊢ syscall.errnoOk (GF := GF) := by
  iintro #H
  ihave #Hs : isPkgInit (PROP := IProp GF) pkg_id.syscall $$ [H]
  · iPkgInit
  iapply syscall.errnoOk_of_isPkgInit $$ Hs

theorem connAt_errnoOk (t : Loc) (cn : Nat) (s : Bool) (a : GoString) (la ra : GoInterface) :
    connAt (GF := GF) t cn s a la ra ⊢ syscall.errnoOk (GF := GF) := by
  iintro #H
  iapply errnoOk_of_poll
  iapply connAt_poll $$ H

theorem lisAt_errnoOk (t : Loc) (l : w64) (x : GoInterface) :
    lisAt (GF := GF) t l x ⊢ syscall.errnoOk (GF := GF) := by
  iintro #H
  iapply errnoOk_of_poll
  ihave #Hn := lisAt_net $$ H
  iPkgInit

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

/-- What a timeout needs (`kindErr`'s `ed`): `poll.ErrDeadlineExceeded` holds `e` (for an operation
that may time out); nothing for the other kinds; impossible without `ed`. -/
def edAt (k : NetErr) (ed : Option GoInterface) : IProp GF :=
  match k, ed with
  | .timeout, some e => iprop(globalAddr internal.poll.ErrDeadlineExceeded ↦□ e)
  | .timeout, none => iprop(False)
  | _, _ => iprop(True)

/-- The `Err` of a result `res` (`codeErr`'s): `nil` for success, else the kind's (`kindErr`). -/
def resKind (res : Option NetErr) (ed : Option GoInterface) (nm : GoString → Prop)
    (e : GoInterface) : IProp GF :=
  match res with
  | none => iprop(⌜e = interface.nil⌝)
  | some k => kindErr k ed nm e

instance resKind_persistent (res : Option NetErr) (ed : Option GoInterface) (nm : GoString → Prop)
    (e : GoInterface) : Persistent (resKind (GF := GF) res ed nm e) := by
  cases res <;> unfold resKind <;> infer_instance

/-- A failure's `Err` is not `nil`, given that the deadline error (if any) is not. -/
theorem kindErr_ne_nil (k : NetErr) (ed : Option GoInterface) (nm : GoString → Prop)
    (e : GoInterface) (hed : ∀ x, ed = some x → x ≠ interface.nil) :
    kindErr (GF := GF) k ed nm e ⊢ ⌜e ≠ interface.nil⌝ := by
  cases k
  · show iprop(⌜e = closedErr⌝) ⊢ _; iintro %h; ipureintro; subst h; unfold closedErr interface.mkOk; intro h; cases h
  · cases ed with
    | none => show iprop(False) ⊢ _; iintro H; iexfalso; iexact H
    | some x => show iprop(⌜e = x⌝) ⊢ _; iintro %h; ipureintro; rw [h]; exact hed x rfl
  · show sysErr nm e ⊢ _; unfold sysErr; iintro ⟨%p, %name, %n, %h, -⟩; ipureintro
    rw [h.1]; unfold interface.mkOk; intro h; cases h

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

/-- `x` is `nil` or a `netAddr` (an `*OpError`'s `Source` and `Addr`). -/
def addrOrNil (x : GoInterface) : IProp GF := iprop(⌜x = interface.nil⌝ ∨ netAddr x)

instance addrOrNil_persistent (x : GoInterface) : Persistent (addrOrNil (GF := GF) x) := by
  unfold addrOrNil; infer_instance

/-- `e` is a non-nil error whose `Error()` returns some string once `syscall` is initialized
(`syscall.errnoOk`: an `*os.SyscallError`'s `Error()` reads `syscall`'s error table through
`Errno.Error`; what `OpError.Error` needs of its `Err`: Go's code calls `e.Err.Error()`). The
condition lets the operations without a package fact in their preconditions (`Dial`, `Close`, ...)
make the fact; whoever calls `Error()` has `syscall`'s (from `isPkgInit` of a package importing it:
`syscall.errnoOk_of_isPkgInit`). -/
def errStr (e : GoInterface) : IProp GF :=
  iprop(∃ ii : GoInterfaceOk, ⌜e = interface.ok ii⌝ ∗
    □ (syscall.errnoOk (GF := GF) -∗ _root_.Perennial.fmt.stringMethodSpec (GF := GF) ii go!"Error"))

instance errStr_persistent (e : GoInterface) : Persistent (errStr (GF := GF) e) := by
  unfold errStr; infer_instance

/-- The error of an operation `op` (`Source` `src`, `Addr` `addr`) whose result is `res`
(`Net.errCode`'s): `nil` for success, else an `*OpError` whose `Err` is the kind's (`kindErr`), has an
`Error()` (`errStr`), and whose addresses are `nil` or `netAddr`s (so `OpError.Error` is defined on it). -/
def resErr (res : Option NetErr) (op : GoString) (src addr : GoInterface)
    (ed : Option GoInterface) (nm : GoString → Prop) (err : GoInterface) : IProp GF :=
  match res with
  | none => iprop(⌜err = interface.nil⌝)
  | some k => iprop(∃ e, opErr op src addr e err ∗ kindErr k ed nm e ∗ errStr e ∗
      addrOrNil src ∗ addrOrNil addr)

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

/-! ### `OpError`'s methods: the precondition (D2, approved by Upamanyu) -/

/-- `e` is one of the errors net's model makes (D14): `poll.ErrNetClosing` (`closedErr`), an
`*poll.DeadlineExceededError` (`poll.ErrDeadlineExceeded`'s value), an `*timeoutError`
(`errTimeout`'s), or an `*os.SyscallError` around a nonzero errno (`sysErr`). -/
def netOwnErr (e : GoInterface) : IProp GF :=
  iprop(⌜e = closedErr⌝ ∨
    (∃ p : Loc, ⌜e = interface.mkOk (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #p⌝) ∨
    (∃ p : Loc, ⌜e = interface.mkOk (go.GoType.PointerType timeoutError.ty) #p⌝) ∨
    sysErr (fun _ => True) e)

instance netOwnErr_persistent (e : GoInterface) : Persistent (netOwnErr (GF := GF) e) := by
  unfold netOwnErr; infer_instance

/-- The precondition of `OpError`'s `Error`, `Timeout` and `Temporary` (Upamanyu's D2: Go's code
calls the `Err`'s and the addresses' methods, which only net's own make defined): `Err` is one of
net's own errors and `Source`, `Addr` are `nil` or `*TCPAddr`s. -/
def opErrOk (v : net.OpError) : IProp GF :=
  iprop(netOwnErr v.Err' ∗ addrOrNil v.Source' ∗ addrOrNil v.Addr')

instance opErrOk_persistent (v : net.OpError) : Persistent (opErrOk (GF := GF) v) := by
  unfold opErrOk; infer_instance

/-- `ed` (if any) is `poll.ErrDeadlineExceeded`'s value, an `*DeadlineExceededError` (`internal/poll`'s
package fact, `errDeadlineExceeded_of_pkgInit`). -/
def edTyped (ed : Option GoInterface) : Prop :=
  ∀ x, ed = some x →
    ∃ p : Loc, x = interface.mkOk (go.GoType.PointerType internal.poll.DeadlineExceededError.ty) #p

theorem edTyped_none : edTyped none := fun _ h => by cases h

/-- `poll.ErrDeadlineExceeded`'s value is typed, from `internal/poll`'s package fact. -/
theorem edTyped_of_poll (ed : GoInterface) :
    isPkgInit (PROP := IProp GF) pkg_id.internal.poll ∗
      globalAddr internal.poll.ErrDeadlineExceeded ↦□ ed ⊢ ⌜edTyped (some ed)⌝ := by
  iintro ⟨#Hp, #Hed⟩
  ihave ⟨%xd, #Hxd⟩ := _root_.Perennial.internal.poll.errDeadlineExceeded_of_pkgInit $$ Hp
  icombine Hed Hxd gives %hed
  ipureintro
  intro x hx
  cases hx
  exact ⟨xd, hed⟩

/-- A failure's `Err` is one of net's own errors. -/
theorem kindErr_netOwnErr (k : NetErr) (ed : Option GoInterface) (nm : GoString → Prop)
    (e : GoInterface) (hed : edTyped ed) :
    kindErr (GF := GF) k ed nm e ⊢ netOwnErr e := by
  cases k
  · show iprop(⌜e = closedErr⌝) ⊢ _; unfold netOwnErr; iintro %h; ileft; ipureintro; exact h
  · cases ed with
    | none => show iprop(False) ⊢ _; iintro H; iexfalso; iexact H
    | some x =>
      obtain ⟨p, hp⟩ := hed x rfl
      show iprop(⌜e = x⌝) ⊢ _
      unfold netOwnErr; iintro %h; iright; ileft; iexists p; ipureintro; rw [h, hp]
  · show sysErr nm e ⊢ _; unfold netOwnErr sysErr
    iintro ⟨%p, %name, %n, %h, #Hp⟩
    iright; iright; iright
    iexists p, name, n
    isplitr
    · ipureintro; exact ⟨h.1, trivial, h.2.2⟩
    iexact Hp

/-- An `*OpError` a net operation returned, with its addresses: `opErrOk` of its value. -/
theorem opErr_opErrOk (op : GoString) (src addr e err : GoInterface) :
    opErr (GF := GF) op src addr e err ∗ netOwnErr e ∗ addrOrNil src ∗ addrOrNil addr ⊢
      ∃ (pe : Loc) (v : net.OpError),
        ⌜err = interface.mkOk (go.GoType.PointerType OpError.ty) #pe⌝ ∗ pe ↦□ v ∗ opErrOk v := by
  unfold opErr opErrOk
  iintro ⟨⟨%pe, %nw, %h, #Hpe⟩, #He, #Hs, #Ha⟩
  iexists pe, _
  isplitr
  · ipureintro; exact h.1
  iframe Hpe
  dsimp only
  iframe He Hs Ha

end def_

end net
end Perennial
