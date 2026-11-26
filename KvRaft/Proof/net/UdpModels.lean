-- The copy for the part `KvRaft/` of `Net/Proof/net/UdpModels.lean` (etc/copy-part.py; rerun it, do not edit).
/-
The UDP part of `net`'s Go model (`models/net/model.go`: the stubs `extUdp*`, one UDP-extension
operation each, `Net/TrustedCode/net.lean`; the helpers `udpSysErr`, `anyUDPAddr`, `udpFD`; the
models `sysListener.listenUDP`, `UDPConn.readFrom`, `UDPConn.writeTo`, `UDPAddr.String`) and Go's
small calls the UDP specs' proofs step through (`(*UDPConn).ok()`, `(*UDPAddr).opAddr()`), as WP
lemmas over the UDP extension alone (`HasExt udpExt`): each gives the error's, the address's or
the socket's predicate of `UdpBase.lean`, or the extension's outcome.
-/
module

public import KvRaft.Proof.net.UdpBase

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode Net Udp

namespace net

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem' : net.Assumptions]
variable [go.BasicIntoValInj]

local notation "UG" => extGlobalGS udpExt (G := hG.goose_globalGS)
local notation "UL" => extLocalGS udpExt (L := hG.goose_localGS)

/-- `udpConnAt`'s content, for a proof that keeps `udpConnAt` itself too. -/
theorem udpConnAt_elim (c : Loc) (s : w64) (a : GoString) :
    udpConnAt (GF := GF) c s a ⊢
      ∃ (fd : Loc) (la : GoInterface) (v : netFD), c ↦□ (UDPConn.mk (conn.mk fd)) ∗ fd ↦□ v ∗
        ⌜v.pfd'.Sysfd' = s ∧ v.net' = go!"udp4" ∧ v.laddr' = la ∧ v.raddr' = interface.nil⌝ ∗
        udpAddr la := by
  unfold udpConnAt udpFdAt
  iintro ⟨%fd, %la, #Hc, ⟨%v, %hv, #Hv⟩, #Hla, -, -⟩
  iexists fd, la, v
  iframe Hc Hv Hla
  ipureintro; exact hv

/-! ### The stubs -/

theorem wp_extUdpAnyString (Φ : val → IProp GF) :
    (∀ s : GoString, Φ #s) -∗ WP (App (Val (@! net.extUdpAnyString)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_udp_AnyString
  iexact HΦ

theorem wp_extUdpAnyW64 (Φ : val → IProp GF) :
    (∀ n : w64, Φ #n) -∗ WP (App (Val (@! net.extUdpAnyW64)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_udp_AnyW64
  iexact HΦ

theorem wp_extUdpAnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ #b) -∗ WP (App (Val (@! net.extUdpAnyBool)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_udp_AnyBool
  iexact HΦ

theorem wp_extUdpAnyErrno (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n ≠ 0⌝ -∗ Φ #n) -∗ WP (App (Val (@! net.extUdpAnyErrno)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  iapply wp_udp_AnyErrno
  iexact HΦ

/-- U1. `extUdpListen(ip, port)` at the valid address `a`. -/
theorem wp_extUdpListen (ip : List w8) (port : w64) (a : GoString) (Φ : val → IProp GF) :
    ⌜ValidDest ip port a⌝ -∗
    (Φ (failV .sys) ∧ ∀ s : w64, ⌜s ≠ 0⌝ -∗ udpSock UL s a -∗ Φ (PairV (#s) (#(W64 0)))) -∗
    WP (App (App (Val (@! net.extUdpListen)) (Val #ip)) (Val #port)) {{ Φ }} := by
  iintro %hv HΦ
  wp_func_call; wp_call
  iapply wp_udp_Listen ip port a $$ %hv HΦ

/-- U2, U3. `extUdpSend(s, bs, ip, port)` to the valid address `a`. -/
theorem wp_extUdpSend (s : w64) (la : GoString) (bs ip : List w8) (port : w64) (a : GoString)
    (Φ : val → IProp GF) :
    ⌜ValidDest ip port a⌝ -∗ udpSock UL s la -∗
    (|={⊤,∅}=> ∃ ms, udpSent UG a ms ∗
      ∀ r ms', ⌜SendOut bs ms r ms'⌝ -∗ udpSent UG a ms' ={∅,⊤}=∗ Φ (#r)) -∗
    WP (App (App (App (App (Val (@! net.extUdpSend)) (Val #s)) (Val #bs)) (Val #ip)) (Val #port))
      {{ Φ }} := by
  iintro %hv #Hs HAU
  wp_func_call; wp_call
  iapply wp_udp_Send s la bs ip port a $$ %hv Hs HAU

/-- U4, U5. `extUdpRecv(s, n)` at the socket `s` bound to `a`. -/
theorem wp_extUdpRecv (s : w64) (a : GoString) (n : w64) (Φ : val → IProp GF) :
    udpSock UL s a -∗
    (|={⊤,∅}=> ∃ ms, udpSent UG a ms ∗
      ∀ od, ⌜RecvOut ms od⌝ -∗ udpSent UG a ms ={∅,⊤}=∗ Φ (recvVal n od)) -∗
    WP (App (App (Val (@! net.extUdpRecv)) (Val #s)) (Val #n)) {{ Φ }} := by
  iintro #Hs HAU
  wp_func_call; wp_call
  iapply wp_udp_Recv s a n $$ Hs HAU

/-! ### The helpers -/

/-- `udpSysErr(name)`: an `*os.SyscallError` around an arbitrary nonzero `Errno`. -/
theorem wp_udpSysErr (name : GoString) (Φ : val → IProp GF) :
    (∀ e, sysErr (GF := GF) (fun _ => True) e -∗ Φ #e) -∗
    WP (App (Val (@! net.udpSysErr)) (Val #name)) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_extUdpAnyErrno as %n %hn
  wp_alloc p as Hp
  ipersist Hp
  wp_auto
  iapply HΦ
  unfold sysErr
  iexists p, name, n
  isplitr
  · ipureintro; exact ⟨rfl, trivial, hn⟩
  iexact Hp

/-- `anyUDPAddr()`: a new `*UDPAddr` with arbitrary fields, read-only (as an `Addr`). -/
theorem wp_anyUDPAddr (Φ : val → IProp GF) :
    (∀ x, udpAddr (GF := GF) x -∗ Φ #x) -∗
    WP (App (Val (@! net.anyUDPAddr)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_extUdpAnyString as %z
  wp_apply wp_string_to_bytes z as %sl ⟨-, -⟩
  wp_apply wp_extUdpAnyW64 as %port
  wp_apply wp_extUdpAnyString as %zone
  wp_alloc p as Hp
  ipersist Hp
  wp_auto
  iapply HΦ
  unfold udpAddr
  iexists p, _
  isplitr
  · ipureintro; rfl
  iexact Hp

/-- `udpFD(id, "udp4")`: a new datagram `netFD` for the socket `id`, with a new local address. -/
theorem wp_udpFD (id : w64) (Φ : val → IProp GF) :
    (∀ (fd : Loc) (la : GoInterface), udpFdAt (GF := GF) fd id la -∗ udpAddr la -∗ Φ #fd) -∗
    WP (App (App (Val (@! net.udpFD)) (Val #id)) (Val #(go!"udp4"))) {{ Φ }} := by
  iintro HΦ
  iapply wp_fupd
  wp_func_call; wp_call
  wp_auto
  wp_apply wp_anyUDPAddr as %la #Hla
  (try wp_auto)
  ipersist «$r0»
  imodintro
  iapply HΦ $$ [«$r0»] Hla
  unfold udpFdAt
  iexists _
  iframe «$r0»
  ipureintro
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- `(*UDPConn).ok()` (`conn`'s, promoted) on a `UDPConn` holding a non-nil `fd`: `true`. -/
theorem wp_UDPConn_ok (c fd : Loc) (hfd : fd ≠ null) (Φ : val → IProp GF) :
    (c ↦□ (UDPConn.mk (conn.mk fd)) : IProp GF) -∗ Φ #true -∗
    WP (App (Val #(methods (go.GoType.PointerType UDPConn.ty) go!"ok" #c)) (Val #())) {{ Φ }} := by
  iintro #Hc HΦ
  ihave #Hc2 := Hc
  iStructNamed Hc2
  ihave %hcn := typedPointsto_not_null _ _ _ $$ conn
  iStructNamed conn
  wp_method_call
  (try wp_auto)
  wp_method_call; wp_call
  wp_auto
  (try rw [show (!decide (structFieldRef UDPConn go!"conn" c = null)) = true by simp [hcn]])
  (try wp_auto)
  (try rw [show (!decide (fd = null)) = true by simp [hfd]])
  (try simp only [hfd, decide_false, Bool.not_false])
  (try wp_auto)
  iexact HΦ

/-- `(*UDPAddr).opAddr()` on a non-nil `*UDPAddr`: the address as an `Addr`. -/
theorem wp_UDPAddr_opAddr (p : Loc) (hp : p ≠ null) (Φ : val → IProp GF) :
    Φ #(interface.mkOk (go.GoType.PointerType UDPAddr.ty) #p) -∗
    WP (App (Val #(methods (go.GoType.PointerType UDPAddr.ty) go!"opAddr" #p)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_method_call; wp_call
  wp_auto
  (try rw [decide_eq_false hp])
  (try simp only [hp, decide_false, ↓reduceIte, Bool.false_eq_true])
  (try wp_auto)
  iexact HΦ

/-- `(*UDPAddr).String()` (the model): an arbitrary string. -/
theorem wp_UDPAddr_String (p : Loc) (Φ : val → IProp GF) :
    (∀ str : GoString, Φ #str) -∗
    WP (App (Val #(methods (go.GoType.PointerType UDPAddr.ty) go!"String" #p)) (Val #())) {{ Φ }} := by
  iintro HΦ
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_extUdpAnyString as %str
  (try wp_auto)
  iapply HΦ

/-! ### The models -/

/-- U1. `sl.listenUDP(ctx, laddr)` (the model) for the network `"udp4"` and a `*UDPAddr` whose `IP`
and `Port` make the valid address `a`: a new socket bound to `a` (`udpConnAt`), or a nil
`*UDPConn` and the system call's error, an `*os.SyscallError` or a bare nonzero `Errno`. -/
theorem wp_listenUDP (sl : Loc) (lc : ListenConfig) (addr : GoString) (ctx : GoInterface) (p : Loc)
    (ip : List w8) (port : w64) (a : GoString) (Φ : val → IProp GF) :
    sl ↦ (sysListener.mk lc go!"udp4" addr) -∗ udpAddrAt (GF := GF) p ip port -∗
    ⌜ValidDest ip port a⌝ -∗
    ((∀ c : Loc, (∃ s, udpConnAt (GF := GF) c s a) -∗ Φ (PairV #c #interface.nil)) ∧
     (∀ e : GoInterface, (sysErr (GF := GF) (fun _ => True) e ∨
        ⌜∃ n : w64, n ≠ 0 ∧ e = interface.mkOk syscall.Errno.ty #n⌝) -∗
        Φ (PairV #(null : Loc) #e))) -∗
    WP (App (App (Val #(methods (go.GoType.PointerType sysListener.ty) go!"listenUDP" #sl))
      (Val #ctx)) (Val #p)) {{ Φ }} := by
  iintro Hsl #Hp %Hv HΦ
  unfold udpAddrAt
  icases Hp with ⟨%ipsl, %z, #Hpt, #Hip⟩
  ihave #Hpt2 := Hpt
  iStructNamed Hpt2
  iStructNamed Hsl
  wp_method_call; wp_call
  wp_auto
  wp_apply wp_bytes_to_string ipsl ip _ $$ Hip as -
  (try wp_auto)
  wp_apply wp_extUdpListen ip port a $$ %Hv
  isplit
  · -- a failure
    unfold failV
    wp_auto
    wp_apply wp_extUdpAnyBool as %bb
    cases bb
    · wp_auto
      wp_apply wp_extUdpAnyString as %nm
      wp_apply wp_udpSysErr nm as %e #He
      (try wp_auto)
      icases HΦ with ⟨-, HΦ⟩
      iapply HΦ
      ileft; iexact He
    · wp_auto
      wp_apply wp_extUdpAnyErrno as %n %hn
      (try wp_auto)
      icases HΦ with ⟨-, HΦ⟩
      iapply HΦ
      iright; ipureintro; exact ⟨n, hn, rfl⟩
  · -- a new socket
    iintro %s %hs0 #Hs
    iapply wp_fupd
    wp_auto
    wp_apply wp_udpFD s as %fd %la #Hfd #Hla
    wp_func_call; wp_call
    (try wp_auto)
    ipersist «$r0»
    imodintro
    icases HΦ with ⟨HΦ, -⟩
    iapply HΦ
    iexists s
    unfold udpConnAt
    iexists fd, la
    iframe «$r0» Hfd Hla Hs
    ipureintro; exact hs0

/-- The arithmetic of the copy: `copy(b, d[:len(b)])` copies `min(len(b), len(d))` bytes. -/
theorem recv_copy (L n : w64) (bs0 d : List w8) (hL : bs0.length = sint.nat L)
    (hL0 : 0 ≤ sint.Z L) (hn : sint.Z n = min bs0.length (d.take L.toNat).length) :
    n.toNat = min L.toNat d.length ∧
      (d.take L.toNat).take bs0.length ++ bs0.drop (d.take L.toNat).length =
        d.take n.toNat ++ bs0.drop n.toNat := by
  have hLt : L.toNat = bs0.length := by
    rw [hL]; simp only [sint.nat, sint.Z] at hL0 ⊢
    have h := BitVec.toInt_eq_toNat_cond L
    split at h <;> omega
  have hnt : n.toNat = min L.toNat d.length := by
    rw [List.length_take, ← hLt] at hn
    simp only [sint.Z] at hn
    have h := BitVec.toInt_eq_toNat_cond n
    split at h <;> omega
  refine ⟨hnt, ?_⟩
  rw [hnt, List.take_take, List.length_take, ← hLt]
  congr 1
  rw [Nat.min_self]
  rcases Nat.le_total L.toNat d.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.take_of_length_le h, List.take_of_length_le (Nat.le_refl _)]

/-- U4, U5. `c.readFrom(b, addr)` (the model) on the socket `s` bound to `a`: the extension's `Recv`
of `len(b)`, by the caller's atomic update over `a`'s datagrams; for `some d` the bytes copied into
`b` (and `*addr` overwritten), for `none` the system call's error and a nil address. -/
theorem wp_readFrom (c : Loc) (s : w64) (a : GoString) (b : GoSlice) (bs0 : List w8) (pa : Loc)
    (va : UDPAddr) (Q : Option (List w8) → IProp GF) (Φ : val → IProp GF) :
    udpConnAt (GF := GF) c s a -∗ b ↦* bs0 -∗ pa ↦ va -∗
    (|={⊤,∅}=> ∃ ms, udpSent UG a ms ∗
      ∀ od, ⌜RecvOut ms od⌝ -∗ udpSent UG a ms ={∅,⊤}=∗ Q od) -∗
    (∀ od (n : w64) (ra : Loc) (e : GoInterface), Q od -∗
      (match od with
       | some d => ⌜n.toNat = min b.len.toNat d.length ∧ e = interface.nil ∧ ra = pa⌝ ∗
           b ↦* (d.take n.toNat ++ bs0.drop n.toNat) ∗ (∃ va' : UDPAddr, pa ↦ va')
       | none => ⌜n = W64 0 ∧ ra = null⌝ ∗ b ↦* bs0 ∗ pa ↦ va ∗
           sysErr (GF := GF) (fun _ => True) e) -∗
      Φ (PairV (PairV #n #ra) #e)) -∗
    WP (App (App (Val #(methods (go.GoType.PointerType UDPConn.ty) go!"readFrom" #c)) (Val #b))
      (Val #pa)) {{ Φ }} := by
  iintro #Hc Hb Hpa HAU HΦ
  unfold udpConnAt
  icases Hc with ⟨%fd, %la, #Hcp, #Hfd, #Hla, %Hs0, #Hsock⟩
  unfold udpFdAt
  icases Hfd with ⟨%v, %hv, #Hv⟩
  obtain ⟨hid, -, -, -⟩ := hv
  icases ownSlice_len b _ bs0 $$ Hb with %Hlen
  ihave #Hcp2 := Hcp
  iStructNamed Hcp2
  iStructNamed conn
  ihave #Hv2 := Hv
  iStructNamed Hv2
  iStructNamed pfd
  wp_method_call; wp_call
  wp_auto
  rw [hid]
  wp_apply wp_extUdpRecv s a b.len $$ Hsock
  imod HAU with ⟨%ms, Hel, Hk⟩
  imodintro
  iexists ms
  iframe Hel
  iintro %od %Hod Hel
  imod Hk $$ %od %Hod Hel with HQ
  imodintro
  cases od with
  | none =>
    simp only [recvVal, recvRes]
    wp_auto
    wp_apply wp_udpSysErr go!"recvfrom" as %e #He
    (try wp_auto)
    iapply HΦ $$ HQ
    dsimp only
    iframe Hb Hpa He
    ipureintro; exact ⟨rfl, rfl⟩
  | some d =>
    simp only [recvVal, recvRes]
    wp_auto
    wp_apply wp_extUdpAnyString as %ipz
    wp_apply wp_string_to_bytes ipz as %ipsl ⟨-, -⟩
    wp_apply wp_extUdpAnyW64 as %port
    (try wp_auto)
    wp_apply wp_string_to_bytes (d.take b.len.toNat) as %sl ⟨Hsl, -⟩
    wp_apply wp_slice_copy_int b bs0 sl (d.take b.len.toNat) (DFrac.own 1) $$ [Hb Hsl]
      as %n ⟨%Hn, Hb, -⟩
    · iframe
    (try wp_auto)
    obtain ⟨hn, heq⟩ := recv_copy b.len n bs0 d Hlen.1 Hlen.2 Hn
    iapply HΦ $$ HQ
    dsimp only
    rw [heq]
    iframe Hb
    isplitr
    · ipureintro; exact ⟨hn, rfl, rfl⟩
    iexists _
    iframe

/-- U2, U3. `c.writeTo(b, addr)` (the model) from the socket `s` to the `*UDPAddr` `p` whose `IP`
and `Port` make the valid address `a`: the extension's `Send`, by the caller's atomic update over
`a`'s datagrams; `(len(b), nil)` on success, else `0` and the system call's error. -/
theorem wp_writeTo (c : Loc) (s : w64) (la : GoString) (b : GoSlice) (q : DFrac) (bs : List w8)
    (p : Loc) (ip : List w8) (port : w64) (a : GoString) (Q : Bool → IProp GF) (Φ : val → IProp GF) :
    udpConnAt (GF := GF) c s la -∗ b ↦*{q} bs -∗ udpAddrAt (GF := GF) p ip port -∗
    ⌜ValidDest ip port a⌝ -∗
    (|={⊤,∅}=> ∃ ms, udpSent UG a ms ∗
      ∀ r ms', ⌜SendOut bs ms r ms'⌝ -∗ udpSent UG a ms' ={∅,⊤}=∗ Q (r = errCode none)) -∗
    (∀ (r n : w64) (e : GoInterface), b ↦*{q} bs -∗ Q (r = errCode none) -∗
      ((⌜r = errCode none ∧ n = b.len ∧ e = interface.nil⌝) ∨
       (⌜r ≠ errCode none ∧ n = W64 0⌝ ∗ sysErr (GF := GF) (fun _ => True) e)) -∗
      Φ (PairV #n #e)) -∗
    WP (App (App (Val #(methods (go.GoType.PointerType UDPConn.ty) go!"writeTo" #c)) (Val #b))
      (Val #p)) {{ Φ }} := by
  iintro #Hc Hb #Hp %Hv HAU HΦ
  unfold udpConnAt
  icases Hc with ⟨%fd, %lad, #Hcp, #Hfd, #Hla, %Hs0, #Hsock⟩
  unfold udpFdAt
  icases Hfd with ⟨%v, %hv, #Hv⟩
  obtain ⟨hid, -, -, -⟩ := hv
  unfold udpAddrAt
  icases Hp with ⟨%ipsl, %z, #Hpt, #Hip⟩
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hpt
  ihave #Hcp2 := Hcp
  iStructNamed Hcp2
  iStructNamed conn
  ihave #Hv2 := Hv
  iStructNamed Hv2
  iStructNamed pfd
  ihave #Hpt2 := Hpt
  iStructNamed Hpt2
  wp_method_call; wp_call
  wp_auto
  (try rw [decide_eq_false Hnn])
  (try simp only [Hnn, ↓reduceIte, decide_false, Bool.false_eq_true])
  (try wp_auto)
  rw [hid]
  wp_apply wp_bytes_to_string b bs q $$ Hb as Hb
  (try wp_auto)
  wp_apply wp_bytes_to_string ipsl ip _ $$ Hip as -
  (try wp_auto)
  wp_apply wp_extUdpSend s la bs ip port a $$ %Hv Hsock
  imod HAU with ⟨%ms, Hel, Hk⟩
  imodintro
  iexists ms
  iframe Hel
  iintro %r %ms' %Hr Hel
  imod Hk $$ %r %ms' %Hr Hel with HQ
  imodintro
  by_cases hr : r = W64 0
  · subst hr
    wp_auto
    iapply HΦ $$ Hb HQ
    ileft
    ipureintro
    exact ⟨rfl, rfl, rfl⟩
  · (try wp_auto)
    (try rw [decide_eq_false hr])
    (try simp only [hr, decide_false, ↓reduceIte, Bool.false_eq_true])
    (try wp_auto)
    wp_apply wp_udpSysErr go!"sendto" as %e #He
    (try wp_auto)
    iapply HΦ $$ Hb HQ
    iright
    iframe He
    ipureintro; exact ⟨hr, rfl⟩

end proof

end net
end Perennial
