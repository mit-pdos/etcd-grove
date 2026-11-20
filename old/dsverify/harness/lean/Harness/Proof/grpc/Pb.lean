/-
The specs of the lab's model of `google.golang.org/protobuf/proto` (`harness/rpcmodel/protobuf`;
`notes/grpc-model.md`): `SetCodec`, `getCodec`, `Marshal`, `Unmarshal` and the lab-only
`MarshalValue` and `UnmarshalValue` (what the grpc model calls), over the kit's codec.

**The codec** (`PbCodec`, a type class: the kit's, whose instance the run chooses and proves its
generated functions meet, `kitCodecOk`; the final statement does not mention it):
* `marshal m Ψ`: the codec's `Marshal(m)` returns `(bs, nil)` with `Ψ (some bs)`, or
  `(_, err)` for a non-nil error with `Ψ none`;
* `unmarshal bs m Ψ`: the codec's `Unmarshal(bs, m)` returns `nil` with `Ψ true`, or an error
  with `Ψ false`.
`codecSet` (persistent): the model's `codec` variable holds a `*Codec` with the kit's functions
for good (made by `SetCodec`).
-/
module

public import Harness.Proof.grpc.Base
public import Harness.Proof.net.rpc.WireSpec
public import Perennial.Proof.sync.Mutex__Lock
public import Perennial.Proof.sync.Mutex__Unlock

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace google_golang_org.protobuf.proto

/-- The kit's protobuf codec, as the specs see it (see the file header). -/
class PbCodec [GooseExts] (GF : BundledGFunctors) where
  marshal : GoInterface → (Option (List w8) → IProp GF) → IProp GF
  unmarshal : List w8 → GoInterface → (Bool → IProp GF) → IProp GF

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [PbKit] [PbCodec GF]

/-- `Marshal`'s function meets `PbCodec.marshal`. -/
def marshalOk (fm : GoFunc) : IProp GF :=
  iprop(□ ∀ (m : GoInterface) (Ψ : Option (List w8) → IProp GF) (Φ : val → IProp GF),
    PbCodec.marshal m Ψ -∗
    ▷ (∀ (s : GoSlice) (err : GoInterface),
        ((⌜err = interface.nil⌝ ∗ ∃ bs, s ↦* bs ∗ Ψ (some bs)) ∨
          (⌜err ≠ interface.nil⌝ ∗ net.rpc.errAny err ∗ Ψ none)) -∗ Φ (PairV #s #err)) -∗
    WP (App (Val #fm) (Val #m)) {{ Φ }})

/-- `Unmarshal`'s function meets `PbCodec.unmarshal`. -/
def unmarshalOk (fu : GoFunc) : IProp GF :=
  iprop(□ ∀ (data : GoSlice) (dq : DFrac) (bs : List w8) (m : GoInterface)
      (Ψ : Bool → IProp GF) (Φ : val → IProp GF),
    data ↦*{dq} bs -∗ PbCodec.unmarshal bs m Ψ -∗
    ▷ (∀ (err : GoInterface) (ok : Bool), data ↦*{dq} bs -∗ ⌜err = interface.nil ↔ ok = true⌝ -∗
        Ψ ok -∗ (if ok then iprop(True) else net.rpc.errAny err) -∗ Φ #err) -∗
    WP (App (App (Val #fu) (Val #data)) (Val #m)) {{ Φ }})

/-- The kit's codec functions meet the kit's `PbCodec` (persistent; the run's to prove). -/
def kitCodecOk : IProp GF :=
  iprop(marshalOk (kitFn go!"pbMarshal") ∗ unmarshalOk (kitFn go!"pbUnmarshal"))

/-- A codec with the kit's functions is registered, for good (persistent). -/
def codecSet : IProp GF :=
  iprop(∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr codec ↦□ c ∗ codecFns c)

instance kitCodecOk_persistent : Persistent (kitCodecOk (GF := GF)) := by
  unfold kitCodecOk marshalOk unmarshalOk; infer_instance
instance codecSet_persistent : Persistent (codecSet (GF := GF)) := by
  unfold codecSet; infer_instance

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [google_golang_org.protobuf.reflect.protoreflect.Assumptions]
variable [google_golang_org.protobuf.proto.Assumptions]
variable [PbKit] [PbCodec GF]

/-- The packages `proto` imports are initialized. -/
theorem deps_of_pkg :
    isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ⊢
      isPkgInit (PROP := IProp GF) pkg_id.sync := by
  refine (isPkgInit_unfold_deps (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto).trans ?_
  show iprop(isPkgInit (PROP := IProp GF) pkg_id.sync ∗ _ ∗ True) ⊢ _
  iintro ⟨H1, -, -⟩
  iexact H1

/-- `SetCodec(c)`: with `c` a non-nil codec holding the kit's functions, a codec with them is
registered for good. -/
abbrev SetCodec.spec : Prop :=
  ∀ c : Loc,
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ codecFns c ∗
      ⌜c ≠ null⌝ }}
    (App (Val (@! google_golang_org.protobuf.proto.SetCodec)) (Val #c))
  {{ RET #(); codecSet (GF := GF) }}

/-- `getCodec()`: with a codec registered, it returns it. -/
abbrev getCodec.spec : Prop :=
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ codecSet (GF := GF) }}
    (App (Val (@! google_golang_org.protobuf.proto.getCodec)) (Val #()))
  {{ (c : Loc), RET #c; codecFns (GF := GF) c }}

/-- What `Marshal` and `MarshalValue` return, given the codec's premise `Ψ`. -/
def marshalPost (Ψ : Option (List w8) → IProp GF) (s : GoSlice) (err : GoInterface) : IProp GF :=
  iprop((⌜err = interface.nil⌝ ∗ ∃ bs, s ↦* bs ∗ Ψ (some bs)) ∨
    (⌜err ≠ interface.nil⌝ ∗ net.rpc.errAny err ∗ Ψ none))

/-- `Marshal(m)`: `(nil, nil)` for a nil `m` (with `Ψ (some [])`), else the codec's. -/
abbrev Marshal.spec : Prop :=
  ∀ (m : GoInterface) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ codecSet (GF := GF) ∗
      kitCodecOk ∗
      ((⌜m = interface.nil⌝ ∗ Ψ (some [])) ∨ (⌜m ≠ interface.nil⌝ ∗ PbCodec.marshal m Ψ)) }}
    (App (Val (@! google_golang_org.protobuf.proto.Marshal)) (Val #m))
  {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err); marshalPost Ψ s err }}

/-- `MarshalValue(v)`: the codec's. -/
abbrev MarshalValue.spec : Prop :=
  ∀ (m : GoInterface) (Ψ : Option (List w8) → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ codecSet (GF := GF) ∗
      kitCodecOk ∗ PbCodec.marshal m Ψ }}
    (App (Val (@! google_golang_org.protobuf.proto.MarshalValue)) (Val #m))
  {{ (s : GoSlice) (err : GoInterface), RET (PairV #s #err); marshalPost Ψ s err }}

/-- `Unmarshal(b, m)` (and `UnmarshalValue`): the codec's. -/
abbrev Unmarshal.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (m : GoInterface) (Ψ : Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ codecSet (GF := GF) ∗
      kitCodecOk ∗ b ↦*{dq} bs ∗ PbCodec.unmarshal bs m Ψ }}
    (App (App (Val (@! google_golang_org.protobuf.proto.Unmarshal)) (Val #b)) (Val #m))
  {{ (err : GoInterface), RET #err;
      ∃ ok : Bool, b ↦*{dq} bs ∗ ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok ∗
        (if ok then iprop(True) else net.rpc.errAny err) }}

/-- `UnmarshalValue(b, v)`: the codec's. -/
abbrev UnmarshalValue.spec : Prop :=
  ∀ (b : GoSlice) (dq : DFrac) (bs : List w8) (m : GoInterface) (Ψ : Bool → IProp GF),
  {{ isPkgInit (PROP := IProp GF) pkg_id.google_golang_org.protobuf.proto ∗ codecSet (GF := GF) ∗
      kitCodecOk ∗ b ↦*{dq} bs ∗ PbCodec.unmarshal bs m Ψ }}
    (App (App (Val (@! google_golang_org.protobuf.proto.UnmarshalValue)) (Val #b)) (Val #m))
  {{ (err : GoInterface), RET #err;
      ∃ ok : Bool, b ↦*{dq} bs ∗ ⌜err = interface.nil ↔ ok = true⌝ ∗ Ψ ok ∗
        (if ok then iprop(True) else net.rpc.errAny err) }}

set_option goose.wp.extras true

theorem SetCodec.wp_proof : SetCodec.spec (GF := GF) (hG := hG) := by
  intro c
  wp_start as ⟨#Hfns, %Hc⟩
  ihave #Hsync := deps_of_pkg $$ Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $HcodecMu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (globalAddr codec ↦ (null : Loc) ∨
    ∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr codec ↦□ c ∗ codecFns c : IProp GF) $$ [Hinv]
  · unfold codecInv; iexact Hinv
  icases Hinv with (Hnull | ⟨%c', %Hc', #Hcp, #Hfns'⟩)
  · wp_auto
    ipersist Hnull
    wp_apply sync.Mutex.Unlock.wp_proof (globalAddr codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
    · unfold codecInv; iright; iexists c; iframe Hnull Hfns; ipureintro; exact Hc
    iapply HΦ
    unfold codecSet
    iexists c; iframe Hnull Hfns; ipureintro; exact Hc
  · wp_auto
    rw [decide_eq_false Hc']
    wp_auto
    wp_apply sync.Mutex.Unlock.wp_proof (globalAddr codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
    · unfold codecInv; iright; iexists c'; iframe Hcp Hfns'; ipureintro; exact Hc'
    iapply HΦ
    unfold codecSet
    iexists c'; iframe Hcp Hfns'; ipureintro; exact Hc'

theorem getCodec.wp_proof : getCodec.spec (GF := GF) (hG := hG) := by
  wp_start as #Hset
  unfold codecSet
  icases Hset with ⟨%c, %Hc, #Hcp, #Hfns⟩
  ihave #Hsync := deps_of_pkg $$ Hpkg
  ihave #Hi := isInit_access $$ Hpkg
  iNamed Hi
  wp_auto
  wp_apply sync.Mutex.Lock.wp_proof $$ [$Hsync $HcodecMu] as ⟨Hlocked, Hinv⟩
  ihave Hinv : (globalAddr codec ↦ (null : Loc) ∨
    ∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr codec ↦□ c ∗ codecFns c : IProp GF) $$ [Hinv]
  · unfold codecInv; iexact Hinv
  icases Hinv with (Hnull | ⟨%c', %Hc', #Hcp', -⟩)
  · icombine Hnull Hcp gives %Heq
    exact absurd Heq.symm Hc
  icombine Hcp' Hcp gives %Heq
  subst Heq
  wp_apply sync.Mutex.Unlock.wp_proof (globalAddr codecMu) codecInv $$ [$Hsync $HcodecMu $Hlocked]
  · unfold codecInv; iright; iexists c'; iframe Hcp' Hfns; ipureintro; exact Hc
  rw [decide_eq_false Hc]
  wp_auto
  iapply HΦ
  iexact Hfns

theorem MarshalValue.wp_proof : MarshalValue.spec (GF := GF) (hG := hG) := by
  intro m Ψ
  wp_start as ⟨#Hset, #Hok, Hm⟩
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
  unfold codecFns kitCodecOk marshalOk
  icases Hfns with ⟨#Hf1, #Hf2⟩
  icases Hok with ⟨#Hmo, -⟩
  wp_auto
  wp_apply Hmo $$ Hm as %s %err Hr
  iapply HΦ
  unfold marshalPost
  iexact Hr

theorem Marshal.wp_proof : Marshal.spec (GF := GF) (hG := hG) := by
  intro m Ψ
  wp_start as ⟨#Hset, #Hok, Hm⟩
  wp_auto
  icases Hm with (⟨%Hnil, HΨ⟩ | ⟨%Hnn, Hm⟩)
  · subst Hnil
    wp_auto
    iapply HΦ
    unfold marshalPost
    ileft
    isplitr
    · ipureintro; rfl
    iexists []
    iframe HΨ
    iapply ownSlice_nil
  · rcases m with i | _
    · wp_auto
      wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
      unfold codecFns kitCodecOk marshalOk
      icases Hfns with ⟨#Hf1, #Hf2⟩
      icases Hok with ⟨#Hmo, -⟩
      wp_auto
      wp_apply Hmo $$ Hm as %s %err Hr
      iapply HΦ
      unfold marshalPost
      iexact Hr
    · exact absurd rfl Hnn

theorem UnmarshalValue.wp_proof : UnmarshalValue.spec (GF := GF) (hG := hG) := by
  intro b dq bs m Ψ
  wp_start as ⟨#Hset, #Hok, Hb, Hm⟩
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
  unfold codecFns kitCodecOk unmarshalOk
  icases Hfns with ⟨#Hf1, #Hf2⟩
  icases Hok with ⟨-, #Huo⟩
  wp_auto
  wp_apply Huo $$ Hb Hm as %err %ok Hb %Hiff HΨ Herr
  iapply HΦ
  iexists ok
  iframe Hb HΨ Herr
  ipureintro; exact Hiff

theorem Unmarshal.wp_proof : Unmarshal.spec (GF := GF) (hG := hG) := by
  intro b dq bs m Ψ
  wp_start as ⟨#Hset, #Hok, Hb, Hm⟩
  wp_auto
  wp_apply getCodec.wp_proof $$ [$Hpkg $Hset] as %c #Hfns
  unfold codecFns kitCodecOk unmarshalOk
  icases Hfns with ⟨#Hf1, #Hf2⟩
  icases Hok with ⟨-, #Huo⟩
  wp_auto
  wp_apply Huo $$ Hb Hm as %err %ok Hb %Hiff HΨ Herr
  iapply HΦ
  iexists ok
  iframe Hb HΨ Herr
  ipureintro; exact Hiff

end spec

end google_golang_org.protobuf.proto

end Perennial
