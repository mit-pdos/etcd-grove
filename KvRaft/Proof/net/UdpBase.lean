-- The copy for the part `KvRaft/` of `Net/Proof/net/UdpBase.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The vocabulary of the specs of `net`'s UDP calls (Go's `ListenUDP`, `WriteToUDP`, `ReadFromUDP`, over
the Go model's `sysListener.listenUDP`, `UDPConn.readFrom`, `UDPConn.writeTo`, `models/net/model.go`,
and the UDP extension `GooseLang/Ext/Udp`, `notes/net-udp.md`):

* `udpConnAt c s a` (persistent): the `*UDPConn` `c` (Go's `struct{ conn }`, read-only) holds a
  `netFD` (`udpFdAt`, read-only) with the UDP extension's socket id `s` in Go's `pfd.Sysfd`, bound
  to `a` (`udpSock`), its local address (a non-nil `*UDPAddr`, read-only), no remote address, and
  the network `"udp4"`. Sockets are never closed (`Close` is not modeled, U12), so it is
  persistent: any number of threads may send and receive on `c` at once.
* `udpAddrAt p ip port` (persistent): the `*UDPAddr` `p` holds the IP `ip` (its slice, read-only)
  and the port `port`, for good: what `ListenUDP` and `WriteToUDP` read of their address.
* `udpErr op src addr err`: `err` is a new `*OpError{Op: op, Net: "udp4", Source: src, Addr: addr}`
  whose `Err` is an `*os.SyscallError` (U9: the UDP extension's only failure is `sys`);
  `udpListenErr src addr err`: `ListenUDP`'s, whose `Err` may also be a bare nonzero `Errno`.
-/
module

public import KvRaft.Proof.net.Base
public import GooseLang.Ext.Udp.Specs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode
open Net Udp

namespace net

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- `x` is a non-nil `*UDPAddr` (as an `Addr`), read-only for good. -/
def udpAddr (x : GoInterface) : IProp GF :=
  iprop(∃ (p : Loc) (v : UDPAddr), ⌜x = interface.mkOk (go.GoType.PointerType UDPAddr.ty) #p⌝ ∗
    p ↦□ v)

instance udpAddr_persistent (x : GoInterface) : Persistent (udpAddr (GF := GF) x) := by
  unfold udpAddr; infer_instance

/-- The `netFD` `fd` (read-only for good) is a model UDP socket: the UDP extension's id `s` in Go's
`pfd.Sysfd`, the network `"udp4"`, the local address `la`, no remote address (`udpFD`). -/
def udpFdAt (fd : Loc) (s : w64) (la : GoInterface) : IProp GF :=
  iprop(∃ v : netFD, ⌜v.pfd'.Sysfd' = s ∧ v.net' = go!"udp4" ∧ v.laddr' = la ∧
    v.raddr' = interface.nil⌝ ∗ fd ↦□ v)

instance udpFdAt_persistent (fd : Loc) (s : w64) (la : GoInterface) :
    Persistent (udpFdAt (GF := GF) fd s la) := by
  unfold udpFdAt; infer_instance

/-- The `*UDPConn` `c` is this node's UDP socket `s`, bound to `a`. -/
def udpConnAt (c : Loc) (s : w64) (a : GoString) : IProp GF :=
  iprop(∃ (fd : Loc) (la : GoInterface), c ↦□ (UDPConn.mk (conn.mk fd)) ∗ udpFdAt fd s la ∗
    udpAddr la ∗ ⌜s ≠ 0⌝ ∗ udpSock (extLocalGS udpExt (L := hG.goose_localGS)) s a)

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
