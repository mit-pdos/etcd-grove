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
def recvVal [GooseExts] [GoGlobalContext] (n : w64) : Option (List w8) → val
  | none => recvRes [] (errCode (some .sys))
  | some d => recvRes (d.take n.toNat) (errCode none)

/-! ## The network's algebra -/

theorem sentTo_add (g : UdpGlobal) (a b : GoString) (d : List w8) :
    (g.add a d).sentTo b = if a = b then d :: g.sentTo a else g.sentTo b := by
  by_cases h : a = b
  · subst h; simp [UdpGlobal.sentTo, UdpGlobal.add]
  · simp [UdpGlobal.sentTo, UdpGlobal.add, h]

/-- Adding a datagram to `a` (a valid address, in the ghost map with `ms`) adds it to the ghost
map's entry. -/
theorem sentOk_add {g : UdpGlobal} {sm : GMap GoString (List (List w8))} {a : GoString}
    {ms : List (List w8)} (d : List w8) (h : SentOk g sm) (ha : sm.lookup a = some ms) :
    SentOk (g.add a d) (sm.insert a (d :: ms)) := by
  obtain ⟨h1, h2⟩ := h
  have hms : ms = g.sentTo a := h2 a ms ha
  refine ⟨fun b => ?_, fun b ms' hb => ?_⟩
  · rw [GMap.lookup_insert_eq_iff]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)]
      have := h1 a
      rw [show sm !! a = some ms from ha] at this
      exact this
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)]; exact h1 b
  · rw [GMap.lookup_insert_eq_iff] at hb
    rw [sentTo_add]
    by_cases hab : a = b
    · subst hab
      rw [ite_eq_left_of_eq_true _ _ (eq_true rfl)] at hb ⊢
      cases hb
      rw [hms]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hab)] at hb ⊢
      exact h2 b ms' hb

/-- A `Send`'s step, as an outcome over the destination's datagrams `ms`: the network with a
datagram added, or as it was. -/
theorem sendStep_cases [GooseExts] [GoGlobalContext] {bs : List w8} {a : GoString} {g : UdpGlobal}
    {e' : Expr} {g' : UdpGlobal} (ms : List (List w8)) (h : SendStep bs a g e' g') :
    ∃ (r : w64) (d : List w8), e' = Val (#r) ∧
      ((g' = g.add a d ∧ SendOut bs ms r (d :: ms)) ∨ (g' = g ∧ SendOut bs ms r ms)) := by
  obtain ⟨d, hI, (⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩)⟩ := h
  · exact ⟨_, d, rfl, .inl ⟨rfl, d, hI, .inl ⟨rfl, rfl⟩⟩⟩
  · exact ⟨_, d, rfl, .inl ⟨rfl, d, hI, .inr ⟨rfl, .inl rfl⟩⟩⟩
  · exact ⟨_, d, rfl, .inr ⟨rfl, d, hI, .inr ⟨rfl, .inr rfl⟩⟩⟩

/-- The socket `s` exists in the node's state, bound to `a`. -/
theorem udpSock_lookup {GF : BundledGFunctors} (hL : UdpLocalGS GF) (σ : UdpLocal) (s : w64)
    (a : GoString) : udpLocalCtx hL σ -∗ udpSock hL s a -∗ ⌜σ.socks.lookup s = some a⌝ := by
  letI := hL.allG
  unfold udpLocalCtx udpSock
  iintro H1 H2
  iapply ghost_map_lookup $$ H1 H2

section lifting
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt udpExt] [GoGlobalContext]
variable [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]
variable {sk : Stuckness} {E : CoPset}

/-- The network's ghost state. -/
abbrev udpG : UdpGS GF := extGlobalGS udpExt

/-- This node's ghost state. -/
abbrev udpL : UdpLocalGS GF := extLocalGS udpExt (L := L)

theorem udp_local_ctx_eq (σ : UdpLocal) :
    ExtInterp.localCtx (E := udpExt) (extLocalGS udpExt (L := L) (GF := GF)) σ ⊣⊢
      udpLocalCtx (udpL (L := L)) σ := .rfl

theorem udp_global_ctx_eq (g : UdpGlobal) :
    ExtInterp.globalCtx (E := udpExt) (extGlobalGS udpExt (G := G)) g ⊣⊢ udpCtx (udpG (G := G)) g :=
  .rfl


/-- U13. The lifting rule of the extension's operations: a WP of an operation from its outcome
rules (`IsUdpStep`), each with the node's and the network's interpretations; its stutters
(`UdpStep`'s other case) are handled here, by Löb induction (as `Net.wp_net_op`). -/
theorem wp_udp_op (o : String) (v : val) (hv : v.isPanic = false) (Φ : val → IProp GF) :
    ▷ (∀ σ g e' σ' g', ⌜IsUdpStep o v σ g e' σ' g'⌝ -∗ udpLocalCtx (udpL (L := L)) σ -∗
        udpCtx (udpG (G := G)) g ={E}=∗
        udpLocalCtx (udpL (L := L)) σ' ∗ udpCtx (udpG (G := G)) g' ∗ WP e' @ sk; E {{ Φ }}) ⊢
    WP (ExternalOp udpExt.name o (Val v)) @ sk; E {{ Φ }} := by
  iloeb as IH
  iintro HΦ
  iapply wp_extStep o v Φ hv
  iintro %h %σ %g Hheap Hl Hg
  icases (udp_local_ctx_eq σ).mp $$ Hl with Hl
  icases (udp_global_ctx_eq g).mp $$ Hg with Hg
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    exact ⟨_, h, σ, g, (show UdpStep o v h σ g _ h σ g from ⟨rfl, .inl ⟨rfl, rfl, rfl⟩⟩)⟩
  inext
  iintro %e' %h' %σ' %g' %Hst _
  obtain ⟨rfl, Hcase⟩ := (show UdpStep o v h σ g e' h' σ' g' from Hst)
  imod Hclose
  rcases Hcase with ⟨rfl, rfl, rfl⟩ | Hop
  · -- a stutter
    imodintro
    iframe Hheap
    isplitl [Hl]
    · iapply (udp_local_ctx_eq _).mpr; iexact Hl
    isplitl [Hg]
    · iapply (udp_global_ctx_eq _).mpr; iexact Hg
    iapply IH
    inext
    iexact HΦ
  · imod HΦ $$ %_ %_ %_ %_ %_ %Hop Hl Hg with ⟨Hl, Hg, Hwp⟩
    imodintro
    iframe Hheap Hwp
    isplitl [Hl]
    · iapply (udp_local_ctx_eq _).mpr; iexact Hl
    · iapply (udp_global_ctx_eq _).mpr; iexact Hg

/-- U1. `Listen` at the valid address `a` (given as `ip` and `port`): a failure, or a new socket
bound to `a` (persistent). -/
theorem wp_udp_Listen (ip : List w8) (port : w64) (a : GoString) (Φ : val → IProp GF) :
    ⌜ValidDest ip port a⌝ -∗
    (Φ (failV .sys) ∧ ∀ s : w64, ⌜s ≠ 0⌝ -∗ udpSock (udpL (L := L)) s a -∗
      Φ (PairV (#s) (#(W64 0)))) -∗
    WP (ExternalOp udpExt.name "Listen" (Val (PairV (#ip) (#port)))) @ sk; E {{ Φ }} := by
  letI := (udpL (L := L)).allG
  iintro %Hok HΦ
  iapply wp_udp_op "Listen" (PairV (#ip) (#port)) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  obtain ⟨ip', port', a', Hv, Hok', Hls, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨ip, port, a, rfl, Hok⟩
  obtain ⟨h1, h2⟩ := val.PairV.inj Hv
  obtain rfl := go.intoVal_inj (V := GoString) h1
  obtain rfl := go.intoVal_inj (V := w64) h2
  obtain rfl : a = a' := Option.some.inj (Hok.1.symm.trans Hok'.1)
  unfold udpLocalCtx
  rcases Hls with ⟨rfl, rfl⟩ | ⟨s, hs0, hs, rfl, rfl⟩
  · icases HΦ with ⟨HΦ, -⟩
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iexact HΦ
  · imod ghost_map_insert_persist s a hs $$ Hl with ⟨Hl, #Hs⟩
    icases HΦ with ⟨-, HΦ⟩
    imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ $$ %s %hs0
    unfold udpSock
    iexact Hs

/-- U2, U3. `Send` of `bs` from the socket `s` to the valid address `a` (given as `ip` and `port`),
by a logically atomic update over `a`'s datagrams (`SendOut`). -/
theorem wp_udp_Send (s : w64) (la : GoString) (bs ip : List w8) (port : w64) (a : GoString)
    (Φ : val → IProp GF) :
    ⌜ValidDest ip port a⌝ -∗ udpSock (udpL (L := L)) s la -∗
    (|={E,∅}=> ∃ ms, udpSent (udpG (G := G)) a ms ∗
      ∀ r ms', ⌜SendOut bs ms r ms'⌝ -∗ udpSent (udpG (G := G)) a ms' ={∅,E}=∗ Φ (#r)) -∗
    WP (ExternalOp udpExt.name "Send"
      (Val (PairV (#s) (PairV (#bs) (PairV (#ip) (#port)))))) @ sk; E {{ Φ }} := by
  iintro %Hok #Hs HAU
  iapply wp_udp_op "Send" (PairV (#s) (PairV (#bs) (PairV (#ip) (#port)))) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  ihave %Hsl := udpSock_lookup _ σ s la $$ Hl Hs
  obtain ⟨s', bs', ip', port', la', a', Hv, -, Hok', Hsend, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨s, bs, ip, port, la, a, rfl, Hsl, Hok⟩
  obtain ⟨h1, h2⟩ := val.PairV.inj Hv
  obtain ⟨h2, h3⟩ := val.PairV.inj h2
  obtain ⟨h3, h4⟩ := val.PairV.inj h3
  obtain rfl := go.intoVal_inj (V := w64) h1
  obtain rfl := go.intoVal_inj (V := GoString) h2
  obtain rfl := go.intoVal_inj (V := GoString) h3
  obtain rfl := go.intoVal_inj (V := w64) h4
  obtain rfl : a = a' := Option.some.inj (Hok.1.symm.trans Hok'.1)
  imod HAU with ⟨%ms, Hel, Hk⟩
  letI := (udpG (G := G)).allG
  unfold udpCtx udpSent
  icases Hg with ⟨%sm, Hauth, %Hsm⟩
  ihave %Hms := ghost_map_lookup $$ Hauth Hel
  obtain ⟨r, d, rfl, (⟨rfl, Hout⟩ | ⟨rfl, Hout⟩)⟩ := sendStep_cases ms Hsend
  · imod ghost_map_update (d :: ms) $$ Hauth Hel with ⟨Hauth, Hel⟩
    imod Hk $$ %r %(d :: ms) %Hout Hel with HΦ
    imodintro
    iframe Hl
    isplitl [Hauth]
    · iexists _
      iframe Hauth
      ipureintro
      exact sentOk_add d Hsm Hms
    iapply wp_value'
    iexact HΦ
  · imod Hk $$ %r %ms %Hout Hel with HΦ
    imodintro
    iframe Hl
    isplitl [Hauth]
    · iexists _
      iframe Hauth
      ipureintro
      exact Hsm
    iapply wp_value'
    iexact HΦ

/-- U4, U5. `Recv` of at most `n` bytes at the socket `s` bound to `a`, by a logically atomic
update over `a`'s datagrams, which it leaves as they are (`RecvOut`). -/
theorem wp_udp_Recv (s : w64) (a : GoString) (n : w64) (Φ : val → IProp GF) :
    udpSock (udpL (L := L)) s a -∗
    (|={E,∅}=> ∃ ms, udpSent (udpG (G := G)) a ms ∗
      ∀ od, ⌜RecvOut ms od⌝ -∗ udpSent (udpG (G := G)) a ms ={∅,E}=∗ Φ (recvVal n od)) -∗
    WP (ExternalOp udpExt.name "Recv" (Val (PairV (#s) (#n)))) @ sk; E {{ Φ }} := by
  iintro #Hs HAU
  iapply wp_udp_op "Recv" (PairV (#s) (#n)) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  ihave %Hsl := udpSock_lookup _ σ s a $$ Hl Hs
  obtain ⟨s', n', a', Hv, Hsl', Hrecv, rfl, rfl⟩ :=
    Hst.resolve_right fun ⟨hnv, _⟩ => hnv ⟨s, n, a, rfl, Hsl⟩
  obtain ⟨h1, h2⟩ := val.PairV.inj Hv
  obtain rfl := go.intoVal_inj (V := w64) h1
  obtain rfl := go.intoVal_inj (V := w64) h2
  obtain rfl : a = a' := Option.some.inj (Hsl.symm.trans Hsl')
  imod HAU with ⟨%ms, Hel, Hk⟩
  letI := (udpG (G := G)).allG
  unfold udpCtx udpSent
  icases Hg with ⟨%sm, Hauth, %Hsm⟩
  ihave %Hms := ghost_map_lookup $$ Hauth Hel
  have hms := Hsm.2 a ms Hms
  obtain ⟨od, rfl, Hout⟩ : ∃ od, e' = Val (recvVal n od) ∧ RecvOut ms od := by
    rcases Hrecv with rfl | ⟨d, hd, rfl⟩
    · exact ⟨none, rfl, trivial⟩
    · exact ⟨some d, rfl, hms ▸ hd⟩
  imod Hk $$ %od %Hout Hel with HΦ
  imodintro
  iframe Hl
  isplitl [Hauth]
  · iexists _
    iframe Hauth
    ipureintro
    exact Hsm
  iapply wp_value'
  iexact HΦ

/-- `AnyBool`: an arbitrary boolean. -/
theorem wp_udp_AnyBool (Φ : val → IProp GF) :
    (∀ b : Bool, Φ (#b)) -∗ WP (ExternalOp udpExt.name "AnyBool" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_udp_op "AnyBool" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨b, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- `AnyString`: an arbitrary string. -/
theorem wp_udp_AnyString (Φ : val → IProp GF) :
    (∀ str : GoString, Φ (#str)) -∗
      WP (ExternalOp udpExt.name "AnyString" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_udp_op "AnyString" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨str, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- `AnyW64`: an arbitrary word. -/
theorem wp_udp_AnyW64 (Φ : val → IProp GF) :
    (∀ n : w64, Φ (#n)) -∗ WP (ExternalOp udpExt.name "AnyW64" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_udp_op "AnyW64" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨n, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ
  · exact absurd rfl hnv

/-- `AnyErrno`: an arbitrary nonzero word. -/
theorem wp_udp_AnyErrno (Φ : val → IProp GF) :
    (∀ n : w64, ⌜n ≠ 0⌝ -∗ Φ (#n)) -∗
      WP (ExternalOp udpExt.name "AnyErrno" (Val (#()))) @ sk; E {{ Φ }} := by
  iintro HΦ
  iapply wp_udp_op "AnyErrno" (#()) (by simp) Φ
  inext
  iintro %σ %g %e' %σ' %g' %Hst Hl Hg
  rcases Hst with ⟨-, ⟨n, hn, rfl⟩, rfl, rfl⟩ | ⟨hnv, -⟩
  · imodintro
    iframe Hl Hg
    iapply wp_value'
    iapply HΦ $$ %n %hn
  · exact absurd rfl hnv

end lifting

end Udp
end Perennial
