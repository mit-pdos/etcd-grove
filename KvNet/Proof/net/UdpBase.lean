-- The copy for the part `KvNet/` of `Net/Proof/net/UdpBase.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The vocabulary of the specs of `net`'s UDP models (`Net/TrustedCode/net.lean`, section "UDP", over
the UDP extension `GooseLang/Ext/Udp`, `notes/net-udp.md`):

* `udpConnAt c s a` (persistent): the `*UDPConn` `c` holds the UDP extension's socket id `s`, bound
  to `a` (`udpSock`), its local address (a non-nil `*UDPAddr`, read-only) and the network `"udp4"`.
  Sockets are never closed (`Close` is not modeled, U12), so it is persistent: any number of
  threads may send and receive on `c` at once.
* `udpAddrAt p ip port` (persistent): the `*UDPAddr` `p` holds the IP `ip` (its slice, read-only)
  and the port `port`, for good: what `ListenUDP` and `WriteToUDP` read of their address.
* `udpErr op src addr err`: `err` is a new `*OpError{Op: op, Net: "udp4", Source: src, Addr: addr}`
  whose `Err` is an `*os.SyscallError` (U9: the UDP extension's only failure is `sys`);
  `udpListenErr src addr err`: `ListenUDP`'s, whose `Err` may also be a bare nonzero `Errno`.
-/
module

public import KvNet.Proof.net.Base
public import GooseLang.Ext.Udp.Specs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Net Udp

namespace net

/-! The model's types as goose names them, for proofs over the UDP extension alone (`Base.lean`'s
equations of the same types carry its section's `HasExt netExt`). -/
section tys
variable [GooseExts] [go_gctx : GoGlobalContext]

theorem udp_OpError_ty_eq : model.OpError = OpError.ty := by unfold OpError.ty; rfl
theorem udp_Addr_ty_eq : model.Addr = Addr.ty := by unfold Addr.ty; rfl
theorem udp_IP_ty_eq : model.IP = IP.ty := by unfold IP.ty; rfl
theorem udp_Errno_ty_eq : model.Errno = syscall.Errno.ty := by unfold syscall.Errno.ty; rfl

end tys

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions] [field_sem : net.UdpFieldAssumptions]

theorem UDPConn_ty_eq : model.UDPConn = UDPConn.ty := by unfold UDPConn.ty; rfl
theorem UDPAddr_ty_eq : model.UDPAddr = UDPAddr.ty := by unfold UDPAddr.ty; rfl

/-- `x` is a non-nil `*UDPAddr` (as an `Addr`), read-only for good. -/
def udpAddr (x : GoInterface) : IProp GF :=
  iprop(∃ (p : Loc) (v : UDPAddr), ⌜x = interface.mkOk (go.GoType.PointerType UDPAddr.ty) #p⌝ ∗
    p ↦□ v)

instance udpAddr_persistent (x : GoInterface) : Persistent (udpAddr (GF := GF) x) := by
  unfold udpAddr; infer_instance

/-- The `*UDPConn` `c` is this node's UDP socket `s`, bound to `a`, with the local address `la`. -/
def udpConnAt (c : Loc) (s : w64) (a : GoString) : IProp GF :=
  iprop(∃ la, c ↦□ (UDPConn.mk s la go!"udp4") ∗ udpAddr la ∗ ⌜s ≠ 0⌝ ∗
    udpSock (extLocalGS udpExt (L := hG.goose_localGS)) s a)

instance udpConnAt_persistent (c : Loc) (s : w64) (a : GoString) :
    Persistent (udpConnAt (GF := GF) c s a) := by
  unfold udpConnAt; infer_instance

/-- The `*UDPAddr` `p` holds the IP `ip` (its bytes, read-only) and the port `port`, for good. -/
def udpAddrAt (p : Loc) (ip : List w8) (port : w64) : IProp GF :=
  iprop(∃ (sl : GoSlice) (z : GoString), p ↦□ (UDPAddr.mk sl port z) ∗ sl ↦*□ ip)

instance udpAddrAt_persistent (p : Loc) (ip : List w8) (port : w64) :
    Persistent (udpAddrAt (GF := GF) p ip port) := by
  unfold udpAddrAt; infer_instance

/-- `err` is a new `*OpError` (as an `error`, read-only for good) of the operation `op` on the
network `"udp4"`, with `Source` `src`, `Addr` `addr`, and an `*os.SyscallError` as its `Err`
(`sysErr`, any system call's name). -/
def udpErr (op : GoString) (src addr err : GoInterface) : IProp GF :=
  iprop(∃ (pe : Loc) (e : GoInterface),
    ⌜err = interface.mkOk (go.GoType.PointerType OpError.ty) #pe⌝ ∗
    pe ↦□ (OpError.mk op go!"udp4" src addr e) ∗ sysErr (fun _ => True) e)

instance udpErr_persistent (op : GoString) (src addr err : GoInterface) :
    Persistent (udpErr (GF := GF) op src addr err) := by
  unfold udpErr; infer_instance

/-- `err` is a new `*OpError` of `ListenUDP` (`Op` `"listen"`, network `"udp4"`, `Source` `src`,
`Addr` `addr`), whose `Err` is an `*os.SyscallError` (`sysErr`) or a bare nonzero `syscall.Errno`
(Go's `fd.init` failing to register the socket with epoll returns the `Errno` unwrapped). -/
def udpListenErr (src addr err : GoInterface) : IProp GF :=
  iprop(∃ (pe : Loc) (e : GoInterface),
    ⌜err = interface.mkOk (go.GoType.PointerType OpError.ty) #pe⌝ ∗
    pe ↦□ (OpError.mk go!"listen" go!"udp4" src addr e) ∗
    (sysErr (fun _ => True) e ∨ ⌜∃ n : w64, n ≠ 0 ∧ e = interface.mkOk syscall.Errno.ty #n⌝))

instance udpListenErr_persistent (src addr err : GoInterface) :
    Persistent (udpListenErr (GF := GF) src addr err) := by
  unfold udpListenErr; infer_instance

theorem udpListenErr_ne_nil {src addr err : GoInterface} :
    udpListenErr (GF := GF) src addr err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold udpListenErr
  iintro ⟨%pe, %e, %h, -, -⟩
  ipureintro
  rw [h]
  intro h'
  cases h'

theorem udpErr_ne_nil {op : GoString} {src addr err : GoInterface} :
    udpErr (GF := GF) op src addr err ⊢ ⌜err ≠ interface.nil⌝ := by
  unfold udpErr
  iintro ⟨%pe, %e, %h, -, -⟩
  ipureintro
  rw [h]
  intro h'
  cases h'

end def_

end net
end Perennial
