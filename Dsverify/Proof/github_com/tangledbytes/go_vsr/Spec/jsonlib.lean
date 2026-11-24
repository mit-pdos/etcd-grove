/-
The vr kit's names over the main tree's `encoding/json` registry and per-type dispatch
(`Proof/encoding/json/Registry.lean`, J1/J2/J3 of mit-pdos/etcd-grove#24: `codecOkWith`,
`codecFnsWith`, `codecSetWith`, `codecInv`, `codecUnset`, `typeCodecOk`, `marshalVia`,
`unmarshalVia`). Definitions, and the dispatch's unfolding lemmas. Names are the lab's.

* `kitFn` (the kit's generated functions: `jsonMarshal`, `jsonUnmarshal` in `examples/vsrnet`;
  the lab's `JsonKit.pkg` is that package's path), `codecFns c` (= `codecFnsWith` at them).
* `codecSet`: the kit's codec registered, **the main tree's `codecSetWith`** at the kit's
  functions (with the registry's mutex, which `getCodec` locks). `RegisterJSON()` makes it from
  `codecFresh` (encoding/json's registry as its first initialization leaves it: `codecMu`'s
  mutex and `codec`'s other half at `nil`), a boot resource of the machine
  (`examples/vsrnet/BootLinked.lean`).
* The registered codec's share of a contract (generic; a candidate for the main tree):
  `marshalsByCodec v` / `unmarshalsByCodec ptr` (the dispatch sends `Marshal(v)` /
  `Unmarshal(_, ptr)` to the registered codec: the dynamic type has no `JSONModel*` method) and
  `codecPart J` (`J` restricted to those values). The registered codec meets `codecPart J` where it
  cannot meet `J` (the per-type methods' values, which the codec does not know and panics on);
  `marshalVia_codec`, `unmarshalVia_codec`, `marshalVia_ptr`, `unmarshalVia_ptr` unfold the
  dispatch.
* `kitTypes` (the 14 named types jsongen's same-package methods cover: `etc/dsv/vr.py`'s
  `jsonmodel_roots`) and `kitCodecOk F` (the kit's JSON facts, persistent: the registered codec
  meets `codecPart jc`, every kit type's methods meet `jc`; `jsoncodec.Scan` computes `F`).
* `bufio.errWf`, `bufio.errOrNil` are the main tree's (`Proof/bufio/ErrOrNil.lean`).
-/
module

public import Proof.encoding.json.Registry
public import Net.Proof.models_lab.Errors
public import Proof.bufio.ErrOrNil
public import Dsverify.Code.github_com.tangledbytes.go_vsr.pkg.events
public import Dsverify.Code.github_com.tangledbytes.go_vsr.pkg.log
public import Dsverify.Code.github_com.tangledbytes.go_vsr.examples.vsrwire

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std

namespace encoding.json

/-- The package of the kit's generated codec functions (the lab's `JsonKit.pkg`). -/
def kitPkg : GoString := go!"github.com/tangledbytes/go-vsr/examples/vsrnet"

/-- The kit's generated function `name` (in `kitPkg`). -/
def kitFn [GooseExts] [GoSemanticsFunctions] (name : GoString) : GoFunc :=
  functions (kitPkg ++ go!"." ++ name) []

section routes
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable [GoSemanticsFunctions]

/-- `Marshal(v)` goes to the registered codec: `v`'s dynamic type has neither
`JSONModelMarshalPtr` nor `JSONModelMarshal` (`marshalAny`). -/
def marshalsByCodec (v : GoInterface) : Prop :=
  match v with
  | .ok ii => go.typeSetContains ii.ty encoding.json.modelMarshalerPtr.ty = false ∧
      go.typeSetContains ii.ty encoding.json.modelMarshaler.ty = false
  | .nil => True

/-- `Unmarshal(_, ptr)` goes to the registered codec: `ptr`'s dynamic type has no
`JSONModelUnmarshal`. -/
def unmarshalsByCodec (ptr : GoInterface) : Prop :=
  match ptr with
  | .ok ii => go.typeSetContains ii.ty encoding.json.modelUnmarshaler.ty = false
  | .nil => True

end routes

section dispatch
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- The registered codec's share of the contract `J`: `J` at the values the dispatch sends to the
codec (see the file header). -/
@[instance_reducible]
def codecPart (J : models_lab.jsoncodec.JsonCodec GF) : models_lab.jsoncodec.JsonCodec GF where
  enc v Ψ := iprop(⌜marshalsByCodec v⌝ ∗ J.enc v Ψ)
  dec bs ptr Ψ := iprop(⌜unmarshalsByCodec ptr⌝ ∗ J.dec bs ptr Ψ)

/-- A value the dispatch sends to the codec: `marshalVia` is the codec's route. -/
theorem marshalVia_codec (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (v : GoInterface) (h : marshalsByCodec v) :
    codecRoute J F ⊢ marshalVia J F v := by
  rcases v with ii | _
  · obtain ⟨h1, h2⟩ := h
    simp only [marshalVia, h1, h2, Bool.false_eq_true, ↓reduceIte]
    iintro H; iexact H
  · simp only [marshalVia]
    iintro H; iexact H

/-- A pointer the dispatch sends to the codec: `unmarshalVia` is the codec's route. -/
theorem unmarshalVia_codec (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (ptr : GoInterface) (h : unmarshalsByCodec ptr) :
    codecRoute J F ⊢ unmarshalVia J F ptr := by
  rcases ptr with ii | _
  · simp only [unmarshalsByCodec] at h
    simp only [unmarshalVia, h, Bool.false_eq_true, ↓reduceIte]
    iintro H; iexact H
  · simp only [unmarshalVia]
    iintro H; iexact H

/-- `Marshal` of a `*T` whose method set has `JSONModelMarshalPtr`: `T`'s own method. -/
theorem marshalVia_ptr (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (T : go.GoType) (l : Loc)
    (h : go.typeSetContains (go.GoType.PointerType T) encoding.json.modelMarshalerPtr.ty = true) :
    typeCodecOk J F T ⊢ marshalVia J F (interface.mkOk (go.GoType.PointerType T) #l) := by
  simp only [marshalVia, interface.mkOk, h, ↓reduceIte]
  unfold typeCodecOk
  iintro #H
  icases H with ⟨-, Hp, -⟩
  iapply Hp

/-- `Unmarshal` into a `*T` whose method set has `JSONModelUnmarshal`: `T`'s own method (which
checks validity with `jsoncodec.Scan`). -/
theorem unmarshalVia_ptr (J : models_lab.jsoncodec.JsonCodec GF) (F : List w8 → Bool → w64 × w64)
    (T : go.GoType) (l : Loc)
    (h : go.typeSetContains (go.GoType.PointerType T) encoding.json.modelUnmarshaler.ty = true) :
    typeCodecOk J F T ∗ models_lab.jsoncodec.scanOk F models_lab.jsoncodec.scanFn ⊢
      unmarshalVia J F (interface.mkOk (go.GoType.PointerType T) #l) := by
  simp only [unmarshalVia, interface.mkOk, h, ↓reduceIte]
  unfold typeCodecOk
  iintro ⟨#H, #Hs⟩
  icases H with ⟨-, -, Hu⟩
  isplitr
  · iexact Hs
  iapply Hu

end dispatch

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- The `*Codec` `c` holds the kit's codec functions, for good (persistent). -/
def codecFns (c : Loc) : IProp GF :=
  codecFnsWith (kitFn go!"jsonMarshal") (kitFn go!"jsonUnmarshal") c

instance codecFns_persistent (c : Loc) : Persistent (codecFns (GF := GF) c) := by
  unfold codecFns; infer_instance

/-- The kit's codec is registered, for good (persistent): the main tree's `codecSetWith` at the
kit's functions (the registry's mutex, `codec ↦□ c`, `codecFns c`). -/
def codecSet : IProp GF :=
  codecSetWith (kitFn go!"jsonMarshal") (kitFn go!"jsonUnmarshal")

instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance

/-- encoding/json's registry as its first initialization leaves it, no codec registered:
`codecMu`'s mutex (its invariant half of `codec`'s points-to) and the other half at `nil`
(exclusive: a machine's boot resource, `RegisterJSON()`'s precondition). -/
def codecFresh : IProp GF :=
  iprop(sync.isMutex (globalAddr encoding.json.codecMu) codecInv ∗ codecUnset)

/-- The 14 named types whose JSON methods jsongen generated into their own packages
(`etc/dsv/vr.py`'s `jsonmodel_roots`): `events`' `Event` and its eleven payloads, `vsrwire.Frame`,
`log.Logs`. -/
def kitTypes : List go.GoType :=
  [github_com.tangledbytes.go_vsr.pkg.events.Event.ty,
   github_com.tangledbytes.go_vsr.pkg.events.Request.ty,
   github_com.tangledbytes.go_vsr.pkg.events.Reply.ty,
   github_com.tangledbytes.go_vsr.pkg.events.Prepare.ty,
   github_com.tangledbytes.go_vsr.pkg.events.PrepareOK.ty,
   github_com.tangledbytes.go_vsr.pkg.events.Commit.ty,
   github_com.tangledbytes.go_vsr.pkg.events.StartViewChange.ty,
   github_com.tangledbytes.go_vsr.pkg.events.DoViewChange.ty,
   github_com.tangledbytes.go_vsr.pkg.events.StartView.ty,
   github_com.tangledbytes.go_vsr.pkg.events.GetState.ty,
   github_com.tangledbytes.go_vsr.pkg.events.NewState.ty,
   github_com.tangledbytes.go_vsr.pkg.events.Heartbeat.ty,
   github_com.tangledbytes.go_vsr.examples.vsrwire.Frame.ty,
   github_com.tangledbytes.go_vsr.pkg.log.Logs.ty]

variable [jc : models_lab.jsoncodec.JsonCodec GF]

/-- **The kit's JSON facts** (persistent): the registered codec's functions meet `codecPart jc`
and `jsoncodec.Scan` computes `F` (`codecOkWith`), and every kit type's methods meet `jc`
(`typeCodecOk`). -/
def kitCodecOk (F : List w8 → Bool → w64 × w64) : IProp GF :=
  iprop(codecOkWith (jc := codecPart jc) F (kitFn go!"jsonMarshal") (kitFn go!"jsonUnmarshal") ∗
    □ ∀ T : go.GoType, ⌜T ∈ kitTypes⌝ → typeCodecOk jc F T)

instance kitCodecOk_persistent F : Persistent (kitCodecOk (GF := GF) F) := by
  unfold kitCodecOk; infer_instance

/-- A kit type's methods, from the kit's facts. -/
theorem kitCodecOk_type (F : List w8 → Bool → w64 × w64) (T : go.GoType) (hT : T ∈ kitTypes) :
    kitCodecOk (GF := GF) F ⊢ typeCodecOk jc F T := by
  unfold kitCodecOk
  iintro #H
  icases H with ⟨-, Hts⟩
  ispecialize Hts $$ %T %hT
  iexact Hts

/-- The scanner's fact, from the kit's facts. -/
theorem kitCodecOk_scan (F : List w8 → Bool → w64 × w64) :
    kitCodecOk (GF := GF) F ⊢ models_lab.jsoncodec.scanOk F models_lab.jsoncodec.scanFn := by
  unfold kitCodecOk codecOkWith
  iintro #H
  icases H with ⟨⟨-, -, Hs⟩, -⟩
  iexact Hs

/-- The codec's route at `codecPart jc`, from the kit's facts and the codec registered. -/
theorem kitCodecOk_route (F : List w8 → Bool → w64 × w64) :
    codecSet (GF := GF) ∗ kitCodecOk F ⊢ codecRoute (codecPart jc) F := by
  unfold kitCodecOk codecRoute codecSet
  iintro ⟨#Hset, #Hk⟩
  icases Hk with ⟨Hc, -⟩
  iexists (kitFn go!"jsonMarshal"), (kitFn go!"jsonUnmarshal")
  isplitr
  · iexact Hset
  iexact Hc

/-- `Unmarshal` into a `*T`, `T` a kit type with `JSONModelUnmarshal`, from the kit's facts. -/
theorem kitCodecOk_unmarshalVia (F : List w8 → Bool → w64 × w64) (T : go.GoType) (l : Loc)
    (hT : T ∈ kitTypes)
    (h : go.typeSetContains (go.GoType.PointerType T) encoding.json.modelUnmarshaler.ty = true) :
    kitCodecOk (GF := GF) F ⊢ unmarshalVia jc F (interface.mkOk (go.GoType.PointerType T) #l) := by
  iintro #Hk
  iapply unmarshalVia_ptr jc F T l h
  isplitr
  · iapply kitCodecOk_type F T hT $$ Hk
  · iapply kitCodecOk_scan F $$ Hk

/-- `Marshal` of a `*T`, `T` a kit type with `JSONModelMarshalPtr`, from the kit's facts. -/
theorem kitCodecOk_marshalVia (F : List w8 → Bool → w64 × w64) (T : go.GoType) (l : Loc)
    (hT : T ∈ kitTypes)
    (h : go.typeSetContains (go.GoType.PointerType T) encoding.json.modelMarshalerPtr.ty = true) :
    kitCodecOk (GF := GF) F ⊢ marshalVia jc F (interface.mkOk (go.GoType.PointerType T) #l) := by
  iintro #Hk
  iapply marshalVia_ptr jc F T l h
  iapply kitCodecOk_type F T hT $$ Hk

end defs

end encoding.json

end Perennial
