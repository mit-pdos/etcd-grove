/-
The parts of the kit's per-type premise `vsrnet.TypeCodecs` (`Spec/json.lean`; the main tree's
`typeCodecOk`) that hold because the kit's contract `vsrnet.jsonCodec` gives no deposit there
(notes/dsv-vr.md, "Round 7", goal 4): `typeCodecOk J F T` constrains a method only where `J.enc`
(marshalling) or `J.dec` (unmarshalling) gives a resource for the value, and `encP` has one only
for a `*events.Event` and a `[]log.Log`, `decP` only for a `*vsrwire.Frame`, a `*events.<T>`
payload and a `*[]log.Log`. So:
* `marshal_val_none`: `T.JSONModelMarshal` at a value of any named type `T`;
* `marshal_ptr_none`: `(*T).JSONModelMarshalPtr` for `T ≠ events.Event`;
* `unmarshal_ptr_none`: `(*T).JSONModelUnmarshal` for `T` neither `vsrwire.Frame` nor a payload;
* `typeCodecOk_logs`: all of `log.Logs` (the kit's code never hands a `Logs` to encoding/json:
  `DoViewChange`'s generated methods call its `MarshalJSON`/`UnmarshalJSON` directly);
* `typeCodecOk_of_unmarshal`, `typeCodecOk_event`, and `codecOk_of`: the kit's JSON facts
  (`vsrnet.codecOk`) from the premises `registeredCodecOk` and `TypeCodecs` (which state only the
  substantive parts) and the scanner's proved `scanOk`.
-/
module

public import Dsverify.Proof.github_com.tangledbytes.go_vsr.Spec.json

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial.github_com.tangledbytes.go_vsr.examples

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Net VsrModel

attribute [local instance] GooseGlobalGS.gooseInvGS

/-- Unfold the kit's named types to `go.GoType.Named` of their paths, and decide an equality of
two of them (or of a named type and a pointer or slice type). -/
local macro "vr_ty_ne" : tactic =>
  `(tactic| (
    intro hty
    simp only [pkg.events.Event.ty, pkg.events.Request.ty, pkg.events.Reply.ty,
      pkg.events.Prepare.ty, pkg.events.PrepareOK.ty, pkg.events.Commit.ty,
      pkg.events.StartViewChange.ty, pkg.events.DoViewChange.ty, pkg.events.StartView.ty,
      pkg.events.GetState.ty, pkg.events.NewState.ty, pkg.events.Heartbeat.ty,
      vsrwire.Frame.ty, pkg.log.Logs.ty, pkg.log.Log.ty, pkg.events.payloadTy,
      go.GoType.Named.injEq, go.GoType.PointerType.injEq, reduceCtorEq] at hty
    all_goals first
      | exact hty
      | exact absurd hty.1 (by decide)
      | exact absurd hty (by decide)))

section proof
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt netExt] [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF] [sem : go.Semantics]
variable [encoding.json.Assumptions]

/-- `marshalAt` where the contract gives no deposit. -/
theorem vsrnet.marshalAt_none (J : models_lab.jsoncodec.JsonCodec GF) (f : val) (v : GoInterface)
    (h : ∀ Ψ, J.enc v Ψ ⊢ iprop(False)) : ⊢ encoding.json.marshalAt J f v := by
  unfold encoding.json.marshalAt
  iintro %Ψ %Φ Henc
  iexfalso
  iapply (h Ψ) $$ Henc

/-- `unmarshalAt` where the contract gives no deposit. -/
theorem vsrnet.unmarshalAt_none (J : models_lab.jsoncodec.JsonCodec GF)
    (F : List w8 → Bool → w64 × w64) (f : val) (ptr : GoInterface)
    (h : ∀ bs Ψ, J.dec bs ptr Ψ ⊢ iprop(False)) : ⊢ encoding.json.unmarshalAt J F f ptr := by
  unfold encoding.json.unmarshalAt
  iintro %data %dq %bs %Ψ %Φ Hd Hdec
  iexfalso
  iapply (h bs Ψ) $$ Hdec

/-- `encP` gives a deposit only for a `*events.Event` and a `[]log.Log`. -/
theorem vsrnet.encP_none (v : GoInterface) (Ψ : Option (List w8) → IProp GF)
    (h1 : ∀ l : Loc, v ≠ interface.mkOk (go.GoType.PointerType pkg.events.Event.ty) #l)
    (h2 : ∀ sl : GoSlice, v ≠ interface.mkOk (go.GoType.SliceType pkg.log.Log.ty) #sl) :
    vsrnet.encP v Ψ ⊢ iprop(False) := by
  unfold vsrnet.encP
  iintro (⟨%_, %_, %_, %ev, %m, %hv, -⟩ | ⟨%_, %sl, %dq, %es, %hv, -⟩)
  · exact (h1 ev hv).elim
  · exact (h2 sl hv).elim

/-- `decP` gives a deposit only for a `*vsrwire.Frame`, a `*events.<T>` payload and a
`*[]log.Log`. -/
theorem vsrnet.decP_none (bs : List w8) (ptr : GoInterface) (Ψ : Bool → IProp GF)
    (h1 : ∀ p : Loc, ptr ≠ interface.mkOk (go.GoType.PointerType vsrwire.Frame.ty) #p)
    (h2 : ∀ (m : Msg) (p : Loc),
      ptr ≠ interface.mkOk (go.GoType.PointerType (pkg.events.payloadTy m)) #p)
    (h3 : ∀ p : Loc,
      ptr ≠ interface.mkOk (go.GoType.PointerType (go.GoType.SliceType pkg.log.Log.ty)) #p) :
    vsrnet.decP bs ptr Ψ ⊢ iprop(False) := by
  unfold vsrnet.decP
  iintro (⟨%_, %ws, %m, %p, %fr, %hbs, %hws, %hm, %hfr, %hp, -⟩ |
    ⟨%_, %_, %_, %m, %p, %hbs, %hm, %hb, %hp, -⟩ | ⟨%_, %es, %p, %hbs, %hes, %hp, -⟩)
  · exact (h1 p hp).elim
  · exact (h2 m p hp).elim
  · exact (h3 p hp).elim

/-- `T.JSONModelMarshal` at a value of a named type `T` (not a pointer or a slice type): no
deposit. -/
theorem vsrnet.marshal_val_none (T : go.GoType) (f : val) (x : val)
    (hT1 : T ≠ go.GoType.PointerType pkg.events.Event.ty)
    (hT2 : T ≠ go.GoType.SliceType pkg.log.Log.ty) :
    ⊢ encoding.json.marshalAt (vsrnet.jsonCodec (GF := GF)) f (interface.mkOk T x) :=
  vsrnet.marshalAt_none _ _ _ fun Ψ => vsrnet.encP_none _ Ψ
    (fun l h => hT1 ((interface_mkOk_inj _ _ _ _).1 h).1)
    (fun sl h => hT2 ((interface_mkOk_inj _ _ _ _).1 h).1)

/-- `(*T).JSONModelMarshalPtr` for `T` other than `events.Event`: no deposit. -/
theorem vsrnet.marshal_ptr_none (T : go.GoType) (f : val) (l : Loc)
    (hT : T ≠ pkg.events.Event.ty) :
    ⊢ encoding.json.marshalAt (vsrnet.jsonCodec (GF := GF)) f
        (interface.mkOk (go.GoType.PointerType T) #l) :=
  vsrnet.marshalAt_none _ _ _ fun Ψ => vsrnet.encP_none _ Ψ
    (fun l' h => hT (by
      have := ((interface_mkOk_inj _ _ _ _).1 h).1
      simpa only [go.GoType.PointerType.injEq] using this))
    (fun sl h => by
      have := ((interface_mkOk_inj _ _ _ _).1 h).1
      simp only [reduceCtorEq] at this)

/-- `(*T).JSONModelUnmarshal` for `T` neither `vsrwire.Frame` nor a payload type nor `[]log.Log`:
no deposit. -/
theorem vsrnet.unmarshal_ptr_none (T : go.GoType) (F : List w8 → Bool → w64 × w64) (f : val)
    (l : Loc) (h1 : T ≠ vsrwire.Frame.ty) (h2 : ∀ m : Msg, T ≠ pkg.events.payloadTy m)
    (h3 : T ≠ go.GoType.SliceType pkg.log.Log.ty) :
    ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) F f
        (interface.mkOk (go.GoType.PointerType T) #l) :=
  vsrnet.unmarshalAt_none _ _ _ _ fun bs Ψ => vsrnet.decP_none bs _ Ψ
    (fun p h => h1 (by
      have := ((interface_mkOk_inj _ _ _ _).1 h).1
      simpa only [go.GoType.PointerType.injEq] using this))
    (fun m p h => h2 m (by
      have := ((interface_mkOk_inj _ _ _ _).1 h).1
      simpa only [go.GoType.PointerType.injEq] using this))
    (fun p h => h3 (by
      have := ((interface_mkOk_inj _ _ _ _).1 h).1
      simpa only [go.GoType.PointerType.injEq] using this))

/-- **`TypeCodecs.logs`, proved**: `log.Logs`' generated methods, at the kit's contract (no
deposit anywhere). -/
theorem vsrnet.typeCodecOk_logs :
    ⊢ encoding.json.typeCodecOk (GF := GF) vsrnet.jsonCodec vsrnet.scanF pkg.log.Logs.ty := by
  unfold encoding.json.typeCodecOk
  iintro !>
  isplitr
  · iintro %x
    iapply (vsrnet.marshal_val_none _ _ x (by vr_ty_ne) (by vr_ty_ne))
  isplitr
  · iintro %l
    iapply (vsrnet.marshal_ptr_none _ _ l (by vr_ty_ne))
  · iintro %l
    iapply (vsrnet.unmarshal_ptr_none _ _ _ l (by vr_ty_ne) (fun m => by cases m <;> vr_ty_ne)
      (by vr_ty_ne))

/-- `typeCodecOk` of a kit type whose substantive part is `JSONModelUnmarshal` (no deposit for
its marshalling). -/
theorem vsrnet.typeCodecOk_of_unmarshal (T : go.GoType)
    (hv1 : T ≠ go.GoType.PointerType pkg.events.Event.ty)
    (hv2 : T ≠ go.GoType.SliceType pkg.log.Log.ty) (hp : T ≠ pkg.events.Event.ty)
    (hu : ∀ l : Loc, ⊢ encoding.json.unmarshalAt (vsrnet.jsonCodec (GF := GF)) vsrnet.scanF
      #(methods (go.GoType.PointerType T) go!"JSONModelUnmarshal" #l)
      (interface.mkOk (go.GoType.PointerType T) #l)) :
    ⊢ encoding.json.typeCodecOk (GF := GF) vsrnet.jsonCodec vsrnet.scanF T := by
  unfold encoding.json.typeCodecOk
  iintro !>
  isplitr
  · iintro %x
    iapply (vsrnet.marshal_val_none _ _ x hv1 hv2)
  isplitr
  · iintro %l
    iapply (vsrnet.marshal_ptr_none _ _ l hp)
  · iintro %l
    iapply (hu l)

/-- `typeCodecOk` of `events.Event`: its substantive part is `JSONModelMarshalPtr`. -/
theorem vsrnet.typeCodecOk_event
    (hm : ∀ l : Loc, ⊢ encoding.json.marshalAt (vsrnet.jsonCodec (GF := GF))
      #(methods (go.GoType.PointerType pkg.events.Event.ty) go!"JSONModelMarshalPtr" #l)
      (interface.mkOk (go.GoType.PointerType pkg.events.Event.ty) #l)) :
    ⊢ encoding.json.typeCodecOk (GF := GF) vsrnet.jsonCodec vsrnet.scanF pkg.events.Event.ty := by
  unfold encoding.json.typeCodecOk
  iintro !>
  isplitr
  · iintro %x
    iapply (vsrnet.marshal_val_none _ _ x (by vr_ty_ne) (by vr_ty_ne))
  isplitr
  · iintro %l
    iapply (hm l)
  · iintro %l
    iapply (vsrnet.unmarshal_ptr_none _ _ _ l (by vr_ty_ne) (fun m => by cases m <;> vr_ty_ne)
      (by vr_ty_ne))

/-- **The kit's JSON facts, from the two premises** (`vsrnet.registeredCodecOk`,
`vsrnet.TypeCodecs`), the proved `JSONModelUnmarshal` methods (`hu`) and the
vacuous parts above. -/
theorem vsrnet.codecOk_of (hc : vsrnet.registeredCodecOk (GF := GF))
    (hs : ⊢ models_lab.jsoncodec.scanOk (GF := GF) vsrnet.scanF models_lab.jsoncodec.scanFn)
    (ht : vsrnet.TypeCodecs (GF := GF)) (hu : vsrnet.TypeUnmarshals (GF := GF)) :
    vsrnet.codecOk (GF := GF) := by
  unfold vsrnet.codecOk encoding.json.kitCodecOk
  unfold vsrnet.registeredCodecOk at hc
  ihave #⟨Hm, Hu⟩ := hc
  ihave #Hs := hs
  isplitr
  · unfold encoding.json.codecOkWith
    isplitl []
    · iexact Hm
    isplitl []
    · iexact Hu
    iexact Hs
  imodintro
  iintro %T %hT
  simp only [encoding.json.kitTypes, List.mem_cons, List.not_mem_nil, _root_.or_false] at hT
  rcases hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · iapply (vsrnet.typeCodecOk_event ht.event)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.request)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.reply)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.prepare)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.prepareOK)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.commit)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.startViewChange)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.doViewChange)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.startView)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.getState)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.newState)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.heartbeat)
  · iapply (vsrnet.typeCodecOk_of_unmarshal _ (by vr_ty_ne) (by vr_ty_ne) (by vr_ty_ne) hu.frame)
  · iapply vsrnet.typeCodecOk_logs

end proof

end Perennial.github_com.tangledbytes.go_vsr.examples
