/-
The WP specs of the UDP extension's operations (`Impl.lean`), over its ghost state (`Ghost.lean`).

Each spec's outcome is the operation's outcome relation in `Impl.lean`, restated over the resources
(`SendOut`, `RecvOut`): what a program may see is exactly what the semantics allows. `Send` and
`Recv` are logically atomic over the destination's datagrams (`udpSent`), taken by an atomic update
at the step that decides, so that a program keeps them in an invariant with its per-address
protocol (every datagram in `udpSent a ms` satisfies it). Every operation may stutter (U13: a
wait), which one rule handles for all, by Löb induction (`wp_udp_op`, as `Net.wp_net_op`); the
panics of invalid uses are excluded there by the resources (the socket exists: `udpSock`) and
premises (the address is valid: `ValidDest`).
-/
module

public import GooseLang.Ext.Udp.Ghost
public import Perennial.Golang.Defn.PostLang

@[expose] public section

noncomputable section

namespace Perennial
namespace Udp

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net

/-! ## Outcomes, over the datagrams of one address -/

/-- U2, U3. A `Send` of `bs` to an address whose datagrams were `ms` returns the code `r` and leaves
`ms'`. -/
def SendOut (bs : List w8) (ms : List (List w8)) (r : w64) (ms' : List (List w8)) : Prop :=
  ∃ d, Intact bs d ∧
    ((r = errCode none ∧ ms' = d :: ms) ∨ (r = errCode (some .sys) ∧ (ms' = d :: ms ∨ ms' = ms)))

/-- U4, U5. What a `Recv` at an address whose datagrams are `ms` gets: a failure (`none`), or one
of them (`some d`). -/
def RecvOut (ms : List (List w8)) : Option (List w8) → Prop
  | none => True
  | some d => d ∈ ms

/-- The value a `Recv` of at most `n` bytes returns for what it got: the datagram's first `n`
bytes, or a `sys` failure. -/
def recvVal (n : w64) : Option (List w8) → val
  | none => recvRes [] (errCode (some .sys))
  | some d => recvRes (d.take n.toNat) (errCode none)

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [GoGlobalContext]
variable [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {sk : Stuckness} {E : CoPset}

/-- The network's ghost state. -/
abbrev udpG : UdpGS GF := extGlobalGS udpExt

/-- This node's ghost state. -/
abbrev udpL : UdpLocalGS GF := extLocalGS udpExt (L := L)

/-- U13. The lifting rule of the extension's operations: a WP of an operation from its outcome
rules (`IsUdpStep`), each with the node's and the network's interpretations; its stutters
(`UdpStep`'s other case) are handled here, by Löb induction (as `Net.wp_net_op`). -/
theorem wp_udp_op (o : String) (v : val) (hv : v.isPanic = false) (Φ : val → IProp GF) :
    ▷ (∀ σ g e' σ' g', ⌜IsUdpStep o v σ g e' σ' g'⌝ -∗ udpLocalCtx (udpL (L := L)) σ -∗
        udpCtx (udpG (G := G)) g ={E}=∗
        udpLocalCtx (udpL (L := L)) σ' ∗ udpCtx (udpG (G := G)) g' ∗ WP e' @ sk; E {{ Φ }}) ⊢
    WP (ExternalOp udpExt.name o (Val v)) @ sk; E {{ Φ }} := by
  sorry

/-- U1. `Listen` at the valid address `a` (given as `ip` and `port`): a failure, or a new socket
bound to `a` (persistent). -/
theorem wp_udp_Listen (ip : List w8) (port : w64) (a : GoString) (Φ : val → IProp GF) :
    ⌜ValidDest ip port a⌝ -∗
    (Φ (failV .sys) ∧ ∀ s : w64, ⌜s ≠ 0⌝ -∗ udpSock (udpL (L := L)) s a -∗
      Φ (PairV (#s) (#(W64 0)))) -∗
    WP (ExternalOp udpExt.name "Listen" (Val (PairV (#ip) (#port)))) @ sk; E {{ Φ }} := by
  sorry

/-- U2, U3. `Send` of `bs` from the socket `s` to the valid address `a` (given as `ip` and `port`),
by a logically atomic update over `a`'s datagrams (`SendOut`). -/
theorem wp_udp_Send (s : w64) (la : GoString) (bs ip : List w8) (port : w64) (a : GoString)
    (Φ : val → IProp GF) :
    ⌜ValidDest ip port a⌝ -∗ udpSock (udpL (L := L)) s la -∗
    (|={E,∅}=> ∃ ms, udpSent (udpG (G := G)) a ms ∗
      ∀ r ms', ⌜SendOut bs ms r ms'⌝ -∗ udpSent (udpG (G := G)) a ms' ={∅,E}=∗ Φ (#r)) -∗
    WP (ExternalOp udpExt.name "Send"
      (Val (PairV (#s) (PairV (#bs) (PairV (#ip) (#port)))))) @ sk; E {{ Φ }} := by
  sorry

/-- U4, U5. `Recv` of at most `n` bytes at the socket `s` bound to `a`, by a logically atomic
update over `a`'s datagrams, which it leaves as they are (`RecvOut`). -/
theorem wp_udp_Recv (s : w64) (a : GoString) (n : w64) (Φ : val → IProp GF) :
    udpSock (udpL (L := L)) s a -∗
    (|={E,∅}=> ∃ ms, udpSent (udpG (G := G)) a ms ∗
      ∀ od, ⌜RecvOut ms od⌝ -∗ udpSent (udpG (G := G)) a ms ={∅,E}=∗ Φ (recvVal n od)) -∗
    WP (ExternalOp udpExt.name "Recv" (Val (PairV (#s) (#n)))) @ sk; E {{ Φ }} := by
  sorry

/-- `AnyBool`: an arbitrary boolean. -/
theorem wp_udp_AnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ (#b)) -∗ WP (ExternalOp udpExt.name "AnyBool" (Val (#()))) @ sk; E {{ Φ }} := by
  sorry

/-- `AnyString`: an arbitrary string. -/
theorem wp_udp_AnyString (Φ : val → IProp GF) :
    (∀ str : GoString, Φ (#str)) -∗
      WP (ExternalOp udpExt.name "AnyString" (Val (#()))) @ sk; E {{ Φ }} := by
  sorry

/-- `AnyW64`: an arbitrary word. -/
theorem wp_udp_AnyW64 (Φ : val → IProp GF) :
    (∀ n : w64, Φ (#n)) -∗ WP (ExternalOp udpExt.name "AnyW64" (Val (#()))) @ sk; E {{ Φ }} := by
  sorry

/-- `AnyErrno`: an arbitrary nonzero word. -/
theorem wp_udp_AnyErrno (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n ≠ 0⌝ -∗ Φ (#n)) -∗
      WP (ExternalOp udpExt.name "AnyErrno" (Val (#()))) @ sk; E {{ Φ }} := by
  sorry

end lifting

end Udp
end Perennial
