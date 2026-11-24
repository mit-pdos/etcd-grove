/-
Tests of the UDP extension's trusted semantics (`Impl.lean`), outside the trust base: for each UDP
row of `examples/net/semantics/doc.go` (`udp_*_test.go`), an `example` that the outcome relations
allow (or exclude) the outcome the row's Go test measured (or the row documents or assumes); the
comment names the Go test. And U13: every operation may stutter in every state, every state has an
outcome that is not a stutter (`isUdpStep_total`), and invalid uses panic.
-/
module

public import GooseLang.Ext.Udp.Impl
public import Perennial.Golang.Defn.PostLang

namespace Perennial
namespace Udp

open Net

set_option linter.unusedSimpArgs false

/-! ## Addresses (U1) -/

private def lo : List w8 := [127, 0, 0, 1]
private def lo2 : List w8 := [127, 0, 0, 2]
private def a1 : GoString := go!"127.0.0.1:20000"
private def a2 : GoString := go!"127.0.0.2:20001"

private theorem udpAddrOf_lo : udpAddrOf lo (W64 20000) = some a1 := by
  decide +kernel

private theorem udpAddrOf_lo2 : udpAddrOf lo2 (W64 20001) = some a2 := by
  decide +kernel

private theorem addrOk_a1 : addrOk a1 = true := by decide
private theorem addrOk_a2 : addrOk a2 = true := by decide

private theorem valid_a1 : ValidDest lo (W64 20000) a1 := ⟨udpAddrOf_lo, addrOk_a1⟩
private theorem valid_a2 : ValidDest lo2 (W64 20001) a2 := ⟨udpAddrOf_lo2, addrOk_a2⟩

/-- `TestUDPListenForms`: the 4-byte IP and the 16-byte IPv4-mapped one name the same address (the
`Zone`, which Go ignores for IPv4, is not passed to the extension at all). -/
example : udpAddrOf (v4InV6Prefix ++ lo) (W64 20000) = some a1 := by decide +kernel
example : ipv4Of (v4InV6Prefix ++ lo) = ipv4Of lo := by decide

/-- (excluded, U1, U13) a 5-byte IP, a 16-byte one without the IPv4-mapped prefix, a port past
65535 make no address. -/
example : udpAddrOf [127, 0, 0, 1, 0] (W64 20000) = none := by decide +kernel
example : udpAddrOf (List.replicate 16 0) (W64 20000) = none := by decide +kernel
example : udpAddrOf lo (W64 65536) = none := by decide +kernel

/-- (excluded, U1 with D20) an address `addrOk` refuses: a zero first byte, the port 0, an
ephemeral port. -/
example : addrOk go!"0.0.0.1:20000" = false ∧ addrOk go!"127.0.0.1:0" = false ∧
    addrOk go!"127.0.0.1:40000" = false := by decide

section steps
variable [GooseExts] [GoGlobalContext] [go.BasicIntoValInj]

/-! ## `Listen` (U1) -/

/-- `TestUDPListenForms`: a bind succeeds, a new socket (`s ≠ 0`) bound to the address. -/
example : ListenStep a1 ⟨∅⟩ (Val (PairV (#(W64 1)) (#(W64 0)))) ⟨(∅ : GMap w64 GoString).insert 1 a1⟩ :=
  .inr ⟨W64 1, by decide, rfl, rfl, rfl⟩

/-- `TestUDPListenTwice`: a second bind of a bound address fails (`EADDRINUSE`, `sys`); the model
also allows it to succeed (more than Linux). -/
example : ListenStep a1 ⟨(∅ : GMap w64 GoString).insert 1 a1⟩ (Val (failV .sys))
    ⟨(∅ : GMap w64 GoString).insert 1 a1⟩ := .inl ⟨rfl, rfl⟩
example : ListenStep a1 ⟨(∅ : GMap w64 GoString).insert 1 a1⟩ (Val (PairV (#(W64 2)) (#(W64 0))))
    ⟨((∅ : GMap w64 GoString).insert 1 a1).insert 2 a1⟩ :=
  .inr ⟨W64 2, by decide, by simp, rfl, rfl⟩

/-- `TestUDPListenNotLocal`: a bind of an address not the machine's fails (`EADDRNOTAVAIL`, `sys`). -/
example (L : UdpLocal) (a : GoString) : ListenStep a L (Val (failV .sys)) L := .inl ⟨rfl, rfl⟩

/-- (excluded) a new socket's id is never 0, nor one the node has. -/
example (L : UdpLocal) (a : GoString) (s : w64) (L' : UdpLocal)
    (h : ListenStep a L (Val (PairV (#s) (#(W64 0)))) L') : s ≠ 0 ∧ L.socks !! s = none := by
  rcases h with ⟨h, -⟩ | ⟨s', hs0, hs, h, -⟩
  · unfold failV at h
    obtain ⟨-, h2⟩ := val.PairV.inj (Expr.Val.inj h)
    have := go.intoVal_inj (V := w64) h2
    exact absurd this (by decide)
  · obtain ⟨h1, -⟩ := val.PairV.inj (Expr.Val.inj h)
    obtain rfl := go.intoVal_inj (V := w64) h1
    exact ⟨hs0, hs⟩

/-- `TestUDPAndTCPSamePort`: the UDP extension is not the TCP one (separate state: a TCP listener
and a UDP socket at one address coexist). -/
example : udpExt.name ≠ netExt.name := by decide

/-! ## `Send` (U2, U3) -/

/-- `TestUDPSendDelivered`: a payload of at most `intactMax` (524) bytes arrives byte for byte;
1 and 524 bytes. -/
example (bs d : List w8) (h : bs.length ≤ intactMax) (hI : Intact bs d) : d = bs := hI h
example (d : List w8) (hI : Intact (List.replicate 524 7) d) : d = List.replicate 524 7 :=
  hI (by rw [List.length_replicate]; unfold intactMax; omega)
example (d : List w8) (hI : Intact [42] d) : d = [42] := hI (by unfold intactMax; simp)

/-- `TestUDPSendDelivered`: `(len, nil)`, the datagram added to the destination's. -/
example (g : UdpGlobal) (bs : List w8) :
    SendStep bs a1 g (Val (#(errCode none))) (g.add a1 bs) :=
  ⟨bs, fun _ => rfl, .inl ⟨rfl, rfl⟩⟩
/-- (excluded) a successful small send adds only what was sent. -/
example (g g' : UdpGlobal) (bs : List w8) (h : bs.length ≤ intactMax)
    (hs : SendStep bs a1 g (Val (#(errCode none))) g') : g' = g.add a1 bs := by
  obtain ⟨d, hI, ⟨-, rfl⟩ | ⟨he, -⟩⟩ := hs
  · rw [hI h]
  · have := go.intoVal_inj (V := w64) (Expr.Val.inj he); cases this

/-- (U3) a payload of 525 bytes, past `intactMax`, may arrive as any bytes; so may one of 1473
bytes (`TestUDPNetnsFragmentation`: fragmented by IP). -/
example (d : List w8) : Intact (List.replicate 525 0) d := fun h => by
  rw [List.length_replicate] at h; unfold intactMax at h; omega
example (d : List w8) : Intact (List.replicate 1473 0) d := fun h => by
  rw [List.length_replicate] at h; unfold intactMax at h; omega

/-- `TestUDPSendToUnbound`: a send to an address no socket is bound to succeeds. -/
example (bs : List w8) : SendStep bs a2 ⟨∅⟩ (Val (#(errCode none))) ((⟨∅⟩ : UdpGlobal).add a2 bs) :=
  ⟨bs, fun _ => rfl, .inl ⟨rfl, rfl⟩⟩

/-- `TestUDPSendSizeLimit`: 65507 bytes delivered whole (allowed: any bytes, these among them);
65508 bytes: a `sys` failure (`EMSGSIZE`), nothing arrives. -/
example (g : UdpGlobal) :
    SendStep (List.replicate 65507 1) a1 g (Val (#(errCode none)))
      (g.add a1 (List.replicate 65507 1)) :=
  ⟨_, fun _ => rfl, .inl ⟨rfl, rfl⟩⟩
example (g : UdpGlobal) :
    SendStep (List.replicate 65508 1) a1 g (Val (#(errCode (some .sys)))) g :=
  ⟨[], fun h => by rw [List.length_replicate] at h; unfold intactMax at h; omega,
    .inr ⟨rfl, .inr rfl⟩⟩

/-- `TestUDPZeroLength`: an empty datagram is sent (`(0, nil)`) and received (`(0, sender, nil)`,
not EOF). -/
example (g : UdpGlobal) : SendStep [] a1 g (Val (#(errCode none))) (g.add a1 []) :=
  ⟨[], fun _ => rfl, .inl ⟨rfl, rfl⟩⟩
example (g : UdpGlobal) (n : w64) : RecvStep a1 n (g.add a1 []) (Val (recvRes [] (errCode none))) :=
  .inr ⟨[], by simp [UdpGlobal.sentTo, UdpGlobal.add], by simp⟩

/-! ## `Recv` (U4, U5) -/

private def g1 (d : List w8) : UdpGlobal := (⟨∅⟩ : UdpGlobal).add a1 d

theorem sentTo_add_self (g : UdpGlobal) (a : GoString) (d : List w8) :
    (g.add a d).sentTo a = d :: g.sentTo a := by
  simp [UdpGlobal.sentTo, UdpGlobal.add]

/-- `TestUDPSendDelivered`: a datagram sent is received byte for byte, into a buffer large
enough. -/
example (d : List w8) (n : w64) (h : d.length ≤ n.toNat) :
    RecvStep a1 n (g1 d) (Val (recvRes d (errCode none))) :=
  .inr ⟨d, by simp [g1, sentTo_add_self], by rw [List.take_of_length_le h]⟩

/-- `TestUDPRecvTruncates`: a 100-byte datagram into 10 bytes: its first 10. -/
example : RecvStep a1 (W64 10) (g1 (List.replicate 100 5))
    (Val (recvRes ((List.replicate 100 5).take 10) (errCode none))) :=
  .inr ⟨_, by simp [g1, sentTo_add_self], rfl⟩

/-- `TestUDPRecvEmptyBuffer`: a 0-byte buffer with a datagram queued: `(0, sender, nil)`. -/
example (d : List w8) : RecvStep a1 (W64 0) (g1 d) (Val (recvRes [] (errCode none))) :=
  .inr ⟨d, by simp [g1, sentTo_add_self], by simp⟩

/-- `TestUDPRecvEmptyBuffer`, (U13) with nothing queued a receive blocks: a stutter, and (excluded)
no datagram is invented: its only outcome besides is a failure. -/
example (L : UdpLocal) (g : UdpGlobal) (h : GMap Loc (NonAtomic val)) (v : val) :
    UdpStep "Recv" v h L g (ExternalOp udpExt.name "Recv" (Val v)) h L g :=
  ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩
example (n : w64) (e' : Expr) (h : RecvStep a1 n ⟨∅⟩ e') :
    e' = Val (recvRes [] (errCode (some .sys))) := by
  rcases h with h | ⟨d, hd, -⟩
  · exact h
  · simp [UdpGlobal.sentTo] at hd

/-- `TestUDPNetnsFaults`: duplication (a `Recv` leaves the network as it was, so a datagram may be
received any number of times), reordering (the later of two datagrams first), loss (any receive may
fail, or wait for good). -/
example (d1 d2 : List w8) (n : w64) (L : UdpLocal) (hL : L.socks !! 1 = some a1) :
    IsUdpStep "Recv" (PairV (#(W64 1)) (#n)) L ((g1 d1).add a1 d2)
      (Val (recvRes (d1.take n.toNat) (errCode none))) L ((g1 d1).add a1 d2) :=
  .inl ⟨W64 1, n, a1, rfl, hL, .inr ⟨d1, by simp [g1, sentTo_add_self], rfl⟩, rfl, rfl⟩
example (d1 d2 : List w8) (n : w64) :
    RecvStep a1 n ((g1 d1).add a1 d2) (Val (recvRes (d2.take n.toNat) (errCode none))) :=
  .inr ⟨d2, by simp [sentTo_add_self], rfl⟩
example (g : UdpGlobal) (n : w64) : RecvStep a1 n g (Val (recvRes [] (errCode (some .sys)))) :=
  .inl rfl

/-- `TestUDPNetnsFaults` (excluded): every datagram received is (the first bytes of) one sent to
the socket's address. -/
example (g : UdpGlobal) (n : w64) (bs : List w8) (h : RecvStep a1 n g (Val (recvRes bs (errCode none)))) :
    ∃ d ∈ g.sentTo a1, bs = d.take n.toNat := by
  rcases h with h | ⟨d, hd, h⟩
  · obtain ⟨-, h2⟩ := val.PairV.inj (Expr.Val.inj h)
    have := go.intoVal_inj (V := w64) h2; cases this
  · obtain ⟨h1, -⟩ := val.PairV.inj (Expr.Val.inj h)
    exact ⟨d, hd, go.intoVal_inj (V := GoString) h1⟩

/-- `TestUDPNetnsSentBeforeBind`: a datagram sent to an address before any socket was bound there
may still be received by a socket bound later (Linux drops it: the model allows more). -/
example (d : List w8) (n : w64) :
    IsUdpStep "Recv" (PairV (#(W64 1)) (#n)) ⟨(∅ : GMap w64 GoString).insert 1 a1⟩ (g1 d)
      (Val (recvRes (d.take n.toNat) (errCode none))) ⟨(∅ : GMap w64 GoString).insert 1 a1⟩ (g1 d) :=
  .inl ⟨W64 1, n, a1, rfl, by simp, .inr ⟨d, by simp [g1, sentTo_add_self], rfl⟩, rfl, rfl⟩

/-! ## Crashes (U7, U8) -/

/-- `TestUDPKilledProcess`: a crash drops the node's sockets (the address binds again) and leaves
the network (its queued datagrams may still be received: the model allows more than Linux). -/
example (L L' : UdpLocal) (h : udp_semantics.crash L L') : L'.socks = ∅ := by
  subst h; rfl
example (L : UdpLocal) (a : GoString) :
    ListenStep a { L with socks := ∅ } (Val (PairV (#(W64 1)) (#(W64 0))))
      ⟨(∅ : GMap w64 GoString).insert 1 a⟩ :=
  .inr ⟨W64 1, by decide, rfl, rfl, rfl⟩

/-- (the initial network, U8) no datagram: a receive at the start can only fail. -/
example (g : UdpGlobal) (hg : g.init) (a : GoString) : g.sentTo a = [] := by
  simp [UdpGlobal.sentTo, UdpGlobal.init] at *; simp [hg]

/-! ## Steps (U13): stutters, every state's outcome, panics -/

/-- Every operation may stutter, in every state. -/
example (op : String) (v : val) (h : GMap Loc (NonAtomic val)) (L : UdpLocal) (g : UdpGlobal) :
    UdpStep op v h L g (ExternalOp udpExt.name op (Val v)) h L g :=
  ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩

private theorem orInvalid_total {valid : Prop} {step : Expr → UdpLocal → UdpGlobal → Prop}
    {L : UdpLocal} {g : UdpGlobal} (h : valid → ∃ e' L' g', step e' L' g') :
    ∃ e' L' g', OrInvalid valid (step e' L' g') L g e' L' g' := by
  by_cases hv : valid
  · obtain ⟨e', L', g', hs⟩ := h hv
    exact ⟨e', L', g', .inl hs⟩
  · exact ⟨_, _, _, .inr ⟨hv, rfl, rfl, rfl⟩⟩

/-- U13: every operation, in every state and on every argument, has an outcome rule besides the
stutter (a step, or a panic): no program waits where Go would go on. -/
theorem isUdpStep_total (op : String) (v : val) (L : UdpLocal) (g : UdpGlobal) :
    ∃ e' L' g', IsUdpStep op v L g e' L' g' := by
  unfold IsUdpStep
  split
  · apply orInvalid_total
    rintro ⟨ip, port, a, rfl, hv⟩
    exact ⟨_, _, _, ip, port, a, rfl, hv, .inl ⟨rfl, rfl⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨s, bs, ip, port, la, a, rfl, hs, hv⟩
    exact ⟨_, _, _, s, bs, ip, port, la, a, rfl, hs, hv,
      ⟨bs, fun _ => rfl, .inr ⟨rfl, .inr rfl⟩⟩, rfl⟩
  · apply orInvalid_total
    rintro ⟨s, n, a, rfl, hs⟩
    exact ⟨_, _, _, s, n, a, rfl, hs, .inl rfl, rfl, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨true, rfl⟩, rfl, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨[], rfl⟩, rfl, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨W64 0, rfl⟩, rfl, rfl⟩
  · exact orInvalid_total fun hv => ⟨_, _, _, hv, ⟨W64 1, by decide, rfl⟩, rfl, rfl⟩
  · exact ⟨_, _, _, rfl, rfl, rfl⟩

/-- The panic of an invalid use. -/
private abbrev panicE : Expr := Panic "net.udp: invalid use of the UDP extension"

/-- U1, U13 (excluded): a `Listen` of a 5-byte IP panics. -/
example (port : w64) (L L' : UdpLocal) (g g' : UdpGlobal) (e' : Expr)
    (h : IsUdpStep "Listen" (PairV (#([127, 0, 0, 1, 0] : List w8)) (#port)) L g e' L' g') :
    e' = panicE := by
  have hn : ∀ p : w64, udpAddrOf [127, 0, 0, 1, 0] p = none := by
    intro p; simp [udpAddrOf, ipv4Of]
  rcases h with ⟨ip, port', a, hv, hd, -⟩ | ⟨-, rfl, -, -⟩
  · obtain ⟨h1, h2⟩ := val.PairV.inj hv
    obtain rfl := go.intoVal_inj (V := GoString) h1
    obtain rfl := go.intoVal_inj (V := w64) h2
    have h3 := hd.1
    rw [hn] at h3; cases h3
  · rfl

/-- U13 (excluded): a `Send` from an id naming no socket of the node panics. -/
example (bs ip : List w8) (port : w64) (g g' : UdpGlobal) (L' : UdpLocal) (e' : Expr)
    (h : IsUdpStep "Send" (PairV (#(W64 1)) (PairV (#bs) (PairV (#ip) (#port)))) ⟨∅⟩ g e' L' g') :
    e' = panicE := by
  rcases h with ⟨s, bs', ip', port', la, a, hv, hs, -⟩ | ⟨-, rfl, -, -⟩
  · obtain ⟨h1, -⟩ := val.PairV.inj hv
    obtain rfl := go.intoVal_inj (V := w64) h1
    simp at hs
  · rfl

/-- U13 (excluded): an unknown operation panics. -/
example (v : val) (L L' : UdpLocal) (g g' : UdpGlobal) (e' : Expr)
    (h : IsUdpStep "Close" v L g e' L' g') : e' = panicE := h.1

end steps

end Udp
end Perennial
