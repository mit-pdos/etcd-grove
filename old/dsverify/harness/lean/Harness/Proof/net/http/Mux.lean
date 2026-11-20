/-
The default mux of the lab's model of `net/http`: `(*ServeMux).Handle`, `Handle`, and
`(*ServeMux).ServeHTTP` (as a handler: `mux_handlerOk`).
-/
module

public import Harness.Proof.net.http.Proto
public import Perennial.Proof.sync.Mutex__Lock
public import Perennial.Proof.sync.Mutex__Unlock

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode NetConn

namespace net.http

section deps
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem sync_init_of_http :
    isPkgInit (PROP := IProp GF) pkg_id.net.http ⊢ isPkgInit (PROP := IProp GF) pkg_id.sync := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.net.http).trans ?_
  show iprop(isPkgInit pkg_id.bufio ∗ isPkgInit pkg_id.errors ∗ isPkgInit pkg_id.net ∗
    isPkgInit pkg_id.sync ∗ True) ⊢ _
  iintro ⟨-, -, -, H, -⟩
  iexact H

theorem net_init_of_http :
    isPkgInit (PROP := IProp GF) pkg_id.net.http ⊢ isPkgInit (PROP := IProp GF) pkg_id.net := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.net.http).trans ?_
  show iprop(isPkgInit pkg_id.bufio ∗ isPkgInit pkg_id.errors ∗ isPkgInit pkg_id.net ∗
    isPkgInit pkg_id.sync ∗ True) ⊢ _
  iintro ⟨-, -, H, -⟩
  iexact H

end deps

section mux
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [net.http.Assumptions]

set_option goose.wp.extras true

theorem muxInv_unfold (mp : Loc) (γ : MuxNames) :
    muxInv (GF := GF) mp γ ⊣⊢ ∃ (M : GMap GoString GoInterface) (R : List GoString),
      ownMap mp (DFrac.own 1) M ∗ ghostMapAuth γ.routes 1 M ∗
      ghostVar γ.owner (1 : Qp).half R ∗ ⌜∀ p, p ∈ R ↔ (M !! p).isSome⌝ := by
  unfold muxInv; exact .rfl

/-- `(*ServeMux).Handle(p, h)` on a mux with names `γ`, with the owner's half of its
registered paths `R`, `p` nonempty and new: `p` routes to `h`, for good. -/
abbrev ServeMux.Handle.spec : Prop :=
  ∀ (mux mp : Loc) (γ : MuxNames) (R : List GoString) (p : GoString) (h : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ isMux mux mp γ ∗
      ghostVar γ.owner (1 : Qp).half R ∗ ⌜p ≠ [] ∧ p ∉ R⌝ }}
    (App (App (Val (mux @!! go.GoType.PointerType net.http.ServeMux.ty @!! go!"Handle"))
      (Val #p)) (Val #(interface.ok h)))
  {{ RET #(); ghostVar γ.owner (1 : Qp).half (p :: R) ∗
      ghostMapElem γ.routes p .discard (interface.ok h) }}

theorem ServeMux.Handle.wp_proof : ServeMux.Handle.spec (GF := GF) (hG := hG) := by
  intro mux mp γ R p h
  wp_start as ⟨#Hmux, Ho, %Hp⟩
  ihave #Hsync := sync_init_of_http $$ Hpkg
  unfold isMux
  icases Hmux with ⟨#Hm, #Hmu⟩
  wp_auto
  wp_if_destruct
  · exfalso; simp_all
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hi⟩
  icases (muxInv_unfold mp γ).1 $$ Hi with ⟨%M, %R', Hmp, Hr, Ho', %HR⟩
  icombine Ho Ho' gives %Heq
  obtain ⟨-, rfl⟩ := Heq
  have hM : M !! p = none := by
    cases hm : M !! p with
    | none => rfl
    | some v => exact absurd ((HR p).2 (by simp [hm])) Hp.2
  wp_apply wp_map_lookup2 $$ Hmp as Hmp
  rw [hM]
  wp_auto
  wp_apply wp_mapInsert $$ Hmp as Hmp
  imod ghostVar_update_halves (p :: R) γ.owner R R $$ Ho Ho' with ⟨Ho, Ho'⟩
  imod ghost_map_insert_persist p (interface.ok h) hM $$ Hr with ⟨Hr, #Hel⟩
  wp_apply sync.Mutex.Unlock.wp_proof _ (muxInv mp γ) $$ [$Hsync $Hmu $Hlocked Hmp Hr Ho']
  · unfold muxInv
    iexists _, p :: R
    iframe Hmp Hr Ho'
    ipureintro
    intro q
    by_cases hq : q = p
    · subst hq; simp
    · simp [hq, HR q, Ne.symm hq]
  iapply HΦ
  iframe Ho Hel

/-- `Handle(p, h)` (through the default mux), with the right to register paths, `R`
registered so far, `p` nonempty and new: the default mux routes `p` to `h`, for good. -/
abbrev Handle.spec : Prop :=
  ∀ (R : List GoString) (p : GoString) (h : GoInterfaceOk),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ muxOwner R ∗ ⌜p ≠ [] ∧ p ∉ R⌝ }}
    (App (App (Val (@! net.http.Handle)) (Val #p)) (Val #(interface.ok h)))
  {{ RET #(); muxOwner (p :: R) ∗ muxRoute p h }}

theorem Handle.wp_proof : Handle.spec (GF := GF) (hG := hG) := by
  intro R p h
  wp_start as ⟨Ho, %Hp⟩
  unfold muxOwner
  icases Ho with ⟨%mux, %mp, %γ, #Hd, Ho⟩
  ihave #Hd' := Hd
  unfold defaultMux
  icases Hd' with ⟨#HD, #Hmux⟩
  wp_auto
  wp_apply ServeMux.Handle.wp_proof mux mp γ R p h $$ [$Hpkg $Hmux $Ho] as ⟨Ho, #Hel⟩
  · ipureintro; exact Hp
  iapply HΦ
  isplitl
  · iexists mux, mp, γ
    iframe Hd Ho
  · unfold muxRoute
    iexists mux, mp, γ
    unfold defaultMux
    iframe HD Hmux Hel

/-- `(*ServeMux).ServeHTTP(w, req)` on the default mux, for a request `{CONNECT, p}` with `p`
routed to `h`: it runs `h`'s `ServeHTTP` with what `h`'s `handlerOk` needs. -/
abbrev ServeMux.ServeHTTP.spec [HasExt netConnExt] [net.Assumptions] [net.model.Assumptions] :
    Prop :=
  ∀ (mux : Loc) (p : GoString) (h : GoInterfaceOk) (Pb Q : Proto GF) (w : GoInterface)
    (req c : Loc) (cid : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.net.http ∗ globalAddr DefaultServeMux ↦□ mux ∗
      muxRoute p h ∗ handlerOk h p Pb Q ∗
      respWriter w c ∗ req ↦ (net.http.Request.mk go!"CONNECT" p) ∗
      net.ownTCPConn c cid true ∗ recvTok cid true (httpReqP p Pb) (connectHead p) ∗
      sendTok cid true Q [] ∗ connFresh cid true }}
    (App (App (Val (mux @!! go.GoType.PointerType net.http.ServeMux.ty @!! go!"ServeHTTP"))
      (Val #w)) (Val #req))
  {{ RET #(); respWriterBack w }}

theorem ServeMux.ServeHTTP.wp_proof [HasExt netConnExt] [net.Assumptions]
    [net.model.Assumptions] : ServeMux.ServeHTTP.spec (GF := GF) (hG := hG) := by
  intro mux p h Pb Q w req c cid
  wp_start as ⟨#HD, #Hr, #Hh, Hw, Hreq, #Hc, Hrecv, Hsend, Hf⟩
  ihave #Hsync := sync_init_of_http $$ Hpkg
  unfold muxRoute defaultMux
  icases Hr with ⟨%mux', %mp, %γ, ⟨#HD', #Hmux⟩, #Hel⟩
  icombine HD HD' gives %Heq
  subst Heq
  unfold isMux
  icases Hmux with ⟨#Hm, #Hmu⟩
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $Hmu] as ⟨Hlocked, Hi⟩
  icases (muxInv_unfold mp γ).1 $$ Hi with ⟨%M, %R', Hmp, Hr, Ho', %HR⟩
  ihave %hM := ghost_map_lookup $$ Hr Hel
  wp_apply wp_map_lookup2 $$ Hmp as Hmp
  rw [show M !! p = some (interface.ok h) from hM]
  wp_apply sync.Mutex.Unlock.wp_proof _ (muxInv mp γ) $$ [$Hsync $Hmu $Hlocked Hmp Hr Ho']
  · unfold muxInv
    iexists M, R'
    iframe Hmp Hr Ho'
    ipureintro; exact HR
  simp only [Option.getD_some, Option.isSome_some, decide_true, Bool.not_true]
  wp_auto
  wp_bind (App (App (Val #(methods h.ty go!"ServeHTTP" h.v)) (Val #w)) (Val #req))
  unfold handlerOk
  iapply Hh $$ Hpkg Hw Hreq Hc Hrecv Hsend Hf
  inext
  iintro Hb
  wp_auto
  iapply HΦ $$ Hb

theorem handlerOk_intro [HasExt netConnExt] [net.Assumptions] [net.model.Assumptions]
    (h : GoInterfaceOk) (p : GoString) (Pb Q : Proto GF) :
    iprop(□ ∀ (w : GoInterface) (req c : Loc) (cid : w64) (Φ : val → IProp GF),
      isPkgInit (PROP := IProp GF) pkg_id.net.http -∗
      respWriter w c -∗ req ↦ (net.http.Request.mk go!"CONNECT" p) -∗
      net.ownTCPConn c cid true -∗
      recvTok cid true (httpReqP p Pb) (connectHead p) -∗ sendTok cid true Q [] -∗
      connFresh cid true -∗
      ▷ (respWriterBack w -∗ Φ #()) -∗
      WP (App (App (Val #(methods h.ty go!"ServeHTTP" h.v)) (Val #w)) (Val #req)) {{ Φ }}) ⊢
    handlerOk (GF := GF) h p Pb Q := by
  unfold handlerOk; exact .rfl

/-- The default mux (its pointer, loaded from `DefaultServeMux`, as a `Handler`) serves `p` as
the handler `h` it routes `p` to does. -/
theorem mux_handlerOk [HasExt netConnExt] [net.Assumptions] [net.model.Assumptions]
    (mux : Loc) (p : GoString) (h : GoInterfaceOk) (Pb Q : Proto GF) :
    ⊢@{IProp GF} globalAddr DefaultServeMux ↦□ mux -∗ muxRoute p h -∗ handlerOk h p Pb Q -∗
      handlerOk ⟨go.GoType.PointerType net.http.ServeMux.ty, #mux⟩ p Pb Q := by
  iintro #HD #Hr #Hh
  iapply handlerOk_intro
  iintro !> %w %req %c %cid %Φ #Hpkg Hw Hreq #Hc Hrecv Hsend Hf HΦ
  iapply ServeMux.ServeHTTP.wp_proof mux p h Pb Q w req c cid $$ [$Hpkg $HD $Hr $Hh $Hw $Hreq
    $Hc $Hrecv $Hsend $Hf] HΦ

end mux

end net.http

end Perennial
