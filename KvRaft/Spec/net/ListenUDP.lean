-- The copy for the part `KvRaft/` of `Net/Spec/net/ListenUDP.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`net.ListenUDP("udp4", laddr)` for `laddr` a `*UDPAddr` whose `IP` and `Port` make the valid
address `a` (`ValidDest`, `GooseLang/Ext/Udp/Impl.lean`, U1: the canonical IPv4 string, `addrOk`),
through Go's `ListenUDP` and the model's `sysListener.listenUDP` (`models/net/model.go`): the UDP
extension's `Listen`. A new socket
bound to `a`, as a `*UDPConn` (`udpConnAt`, persistent), or a nil `*UDPConn` and the
`*OpError{Op: "listen", Source: nil, Addr: laddr}` whose `Err` is an `*os.SyscallError` or a bare
nonzero `syscall.Errno` (`udpListenErr`). Any node may bind any valid address, more than once (U1). Proved in
`Net/Proof/net/ListenUDP.lean`.
-/
module

public import KvRaft.Proof.net.UdpBase

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Net Udp

namespace net

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]

/-- See the file header. -/
abbrev ListenUDP.spec : Prop :=
  ∀ (p : Loc) (ip : List w8) (port : w64) (a : GoString),
  {{ udpAddrAt (GF := GF) p ip port ∗ ⌜ValidDest ip port a⌝ }}
    (App (App (Val (@! net.ListenUDP)) (Val #(go!"udp4"))) (Val #p))
  {{ (c : Loc) (err : GoInterface), RET (PairV #c #err);
      (⌜err = interface.nil⌝ ∗ ∃ s, udpConnAt (GF := GF) c s a) ∨
      (⌜c = null⌝ ∗ udpListenErr (GF := GF) interface.nil
        (interface.mkOk (go.GoType.PointerType UDPAddr.ty) #p) err) }}

end spec

end net
end Perennial
