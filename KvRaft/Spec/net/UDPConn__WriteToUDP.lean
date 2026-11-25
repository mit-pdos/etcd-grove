-- The copy for the part `KvRaft/` of `Net/Spec/net/UDPConn__WriteToUDP.lean` (etc/copy-part.py; rerun it, do not edit).
/-
`(*UDPConn).WriteToUDP(b, addr)` on this node's socket `s` (`udpConnAt`), `addr` a `*UDPAddr` whose
`IP` and `Port` make the valid address `a` (`ValidDest`, U1), through `UDPConn.WriteToUDP.impl`
(`Net/TrustedCode/net.lean`): the UDP extension's `Send`, by a logically atomic update over `a`'s
datagrams (`udpSent`), opened at the step that sends (`SendOut`: one datagram `d` with
`Intact b d`, U3, added; or a failure, `d` added or not, U2). `Q ok` is the update's result, `ok`
whether the send succeeded: then `(len(b), nil)`; else `(0, err)`, `err` the
`*OpError{Op: "write", Source: <the local address>, Addr: addr}` (`udpErr`). `b` is only read.
Proved in `Net/Proof/net/UDPConn__WriteToUDP.lean`.
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
variable [package_sem' : net.Assumptions] [field_sem : net.UdpFieldAssumptions]

/-- See the file header. -/
abbrev UDPConn.WriteToUDP.spec : Prop :=
  ∀ (c : Loc) (s : w64) (la : GoString) (b : GoSlice) (q : DFrac) (bs : List w8) (p : Loc)
    (ip : List w8) (port : w64) (a : GoString) (Q : Bool → IProp GF),
  {{ udpConnAt (GF := GF) c s la ∗ b ↦*{q} bs ∗ udpAddrAt (GF := GF) p ip port ∗
      ⌜ValidDest ip port a⌝ ∗
      (|={⊤,∅}=> ∃ ms, udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms ∗
        ∀ r ms', ⌜SendOut bs ms r ms'⌝ -∗
          udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms' ={∅,⊤}=∗
          Q (r = errCode none)) }}
    (App (App (Val #(methods (go.GoType.PointerType UDPConn.ty) go!"WriteToUDP" #c)) (Val #b))
      (Val #p))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      b ↦*{q} bs ∗ ∃ ok, Q ok ∗
        ((⌜ok = true ∧ n = b.len ∧ err = interface.nil⌝) ∨
         (⌜ok = false ∧ n = W64 0⌝ ∗ ∃ src, udpErr (GF := GF) go!"write" src
           (interface.mkOk (go.GoType.PointerType UDPAddr.ty) #p) err)) }}

end spec

end net
end Perennial
