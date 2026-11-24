/-
`(*UDPConn).ReadFromUDP(b)` on this node's socket `s` bound to `a` (`udpConnAt`), through
`UDPConn.ReadFromUDP.impl` (`Net/TrustedCode/net.lean`): the UDP extension's `Recv` of `len(b)`, by
a logically atomic update over `a`'s datagrams (`udpSent`, left as they are), opened at the step
that decides (`RecvOut`: a failure, `none`, or one of the datagrams sent to `a`, `some d`, U4, U5).
`Q od` is the update's result. For `some d`: `(n, addr, nil)`, `n = min(len(b), len(d))`, the first
`n` bytes of `b` now `d`'s first `n` (the rest of `d` discarded: U4), `addr` a new `*UDPAddr` whose
fields are arbitrary (U10: never the sender's identity). For `none`: `(0, nil, err)`, `b`
unchanged, `err` the `*OpError{Op: "read", Source: <the local address>, Addr: nil}` (`udpErr`).
The result is goose's 3-tuple `((n, addr), err)` (left-nested pairs). Proved in
`Net/Proof/net/UDPConn__ReadFromUDP.lean`.
-/
module

public import Net.Proof.net.UdpBase

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
abbrev UDPConn.ReadFromUDP.spec : Prop :=
  ∀ (c : Loc) (s : w64) (a : GoString) (b : GoSlice) (bs0 : List w8)
    (Q : Option (List w8) → IProp GF),
  {{ udpConnAt (GF := GF) c s a ∗ b ↦* bs0 ∗
      (|={⊤,∅}=> ∃ ms, udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms ∗
        ∀ od, ⌜RecvOut ms od⌝ -∗
          udpSent (extGlobalGS udpExt (G := hG.goose_globalGS)) a ms ={∅,⊤}=∗ Q od) }}
    (App (Val #(methods (go.GoType.PointerType UDPConn.ty) go!"ReadFromUDP" #c)) (Val #b))
  {{ (n : w64) (addr : Loc) (err : GoInterface), RET (PairV (PairV #n #addr) #err);
      ∃ od, Q od ∗
        match od with
        | some d => ⌜n.toNat = min b.len.toNat d.length ∧ err = interface.nil⌝ ∗
            b ↦* (d.take n.toNat ++ bs0.drop n.toNat)
        | none => ⌜n = W64 0 ∧ addr = null⌝ ∗ b ↦* bs0 ∗ ∃ src, udpErr (GF := GF) go!"read" src
            interface.nil err }}

end spec

end net
end Perennial
