/-
Lean-first (no Rocq counterpart).

# The object contract (phase 1 of `notes/k8s-etcd3-plan.md`, D30b, D30k)

The store is generic in its codec, versioner, transformer and decoder (`New`'s arguments). Its
specs take them through a contract, a premise and not an axiom, that real ones meet and the
driver's concrete codec will be proved to meet. The layers follow what the store does with a
value:

- **the transformer** (`value.Transformer`, encryption at rest): reading a stored value gives
  data and whether it is stale (`fromS`, a function of the stored value, D30g); a value written
  for data `d` (`toS d v`) reads back as `d`, not stale;
- **the codec** (`runtime.Codec`): `encode` is what `runtime.Encode` gives for an object without
  its resource version (`PrepareObjectForStorage` clears it first), and `decode` inverts it;
  **encoding is not canonical** (D30b): data may decode to an object whose encoding is other
  data;
- **the versioner** (`storage.Versioner`): an object's resource version is a string in it
  (`parseRV`, `fmtRV`), which `UpdateObject` sets and `PrepareObjectForStorage` clears;
- **the decoder** (the store's `Decoder`, `NewDefaultDecoder(codec, versioner)`): decodes data
  into an object and sets its resource version.

The model's reading of a stored value (`ObjSpec.dec`, `Model.lean`'s `Dec`) is derived: the
object its data decodes to, canonical when it is not stale and its data is its encoding
(`dec_toS_encode`: what the store writes is canonical).

`ObjSpec` holds these functions and the ownership predicate of an object in the heap (`objAt x
o rv`: the `runtime.Object` `x` holds the body `o` with resource version string `rv`).
`contractOk S codec versioner transformer decoder` (persistent) is the premise: the WPs of the
exact calls the store makes on them; an error they return has an `Error()` (`errStrOk`), which
the store calls to trace it. `runtime.Encode(codec, obj)`, names-only in this translation,
is one of those calls, so its behavior is part of the premise and not an axiom of this
repository; a concrete codec's proof gives it a body.
-/
module

public import Proof.k8s_io.apiserver.pkg.storage.etcd3.Model
public import GeneratedProof.k8s_io.apiserver.pkg.storage.etcd3
public import Proof.go_etcd_io.etcd.cache.v3.Base
public import Proof.reflect.Values

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace k8s

open Iris Iris.BI

/-! ## The pure layers -/

/-- **The pure part of the contract** (see the file header). -/
structure ObjCodec (Obj : Type) where
  /-- `runtime.Encode`'s bytes for an object without its resource version -/
  encode : Obj → GoString
  /-- the codec's decoding of data -/
  decode : GoString → Option Obj
  decode_encode : ∀ o, decode (encode o) = some o
  /-- the transformer's reading of a stored value: its data and whether it is stale -/
  fromS : GoString → Option (GoString × Bool)
  /-- `v` is a value the transformer may write for the data `d` -/
  toS : GoString → GoString → Prop
  fromS_toS : ∀ d v, toS d v → fromS v = some (d, false)
  /-- the versioner's parse of a resource version string -/
  parseRV : GoString → Option w64
  /-- the versioner's rendering of a resource version -/
  fmtRV : w64 → GoString
  parse_fmt : ∀ n, parseRV (fmtRV n) = some n
  /-- the empty resource version (what `PrepareObjectForStorage` leaves) parses as `0` -/
  parse_empty : parseRV [] = some (W64 0)
  /-- the object `NewFunc()` and `runtime.SetZeroValue` make -/
  zero : Obj

variable {Obj : Type} [DecidableEq Obj]

/-- **The model's reading of a stored value** (`Model.lean`'s `Dec`): the object its data
decodes to; canonical when not stale and its data is the object's encoding. -/
def ObjCodec.dec (C : ObjCodec Obj) : Dec Obj := fun v =>
  match C.fromS v with
  | none => none
  | some (d, st) => (C.decode d).map fun o => (o, !st && decide (C.encode o = d))

/-- **What the store writes reads as the object, canonical** (D30g). -/
theorem ObjCodec.dec_toS_encode (C : ObjCodec Obj) (o : Obj) (v : GoString)
    (h : C.toS (C.encode o) v) : C.dec v = some (o, true) := by
  simp [ObjCodec.dec, C.fromS_toS _ _ h, C.decode_encode]

/-- The store's no-op test (`!origState.stale && bytes.Equal(data, origState.data)`, data the
encoding of `tryUpdate`'s result `o'`) is the model's: unchanged and canonical. -/
theorem ObjCodec.noop_iff (C : ObjCodec Obj) (v d : GoString) (st : Bool) (o o' : Obj)
    (hf : C.fromS v = some (d, st)) (hd : C.decode d = some o) :
    (!st && decide (C.encode o' = d)) = true ↔ o' = o ∧ (C.dec v).map Prod.snd = some true := by
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
    obtain ⟨hst, he⟩ := h
    have : o' = o := by
      have := C.decode_encode o'
      rw [he, hd] at this
      exact (Option.some.inj this).symm
    subst this
    refine ⟨rfl, ?_⟩
    simp [ObjCodec.dec, hf, hd, hst, he]
  · rintro ⟨rfl, h⟩
    simp only [ObjCodec.dec, hf, hd, Option.map_some, Option.some.injEq] at h
    exact h

/-! ## The contract on the store's interface values -/

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]

/-- **The objects**: the pure contract and the ownership of an object in the heap (`objAt x o rv`:
the `runtime.Object` `x` holds the body `o` with resource version string `rv`). An object is a
non-nil pointer to a struct of the Go type `objTy` (what `conversion.EnforcePtr` requires, and what
`NewFunc()` gives for a typed resource), not `runtime.Unstructured` (D30b: one Go type per store),
and `reflect.New(objTy)` makes the zero object (`newObj`), as the store makes the objects it
decodes into. -/
structure ObjSpec (GF : BundledGFunctors) (Obj : Type) extends ObjCodec Obj where
  objAt : GoInterface → Obj → GoString → IProp GF
  /-- an object is not the `nil` interface -/
  objAt_ne_nil : ∀ x o rv, objAt x o rv ⊢ ⌜x ≠ GoInterface.nil⌝
  /-- the Go type of the objects' structs -/
  objTy : go.GoType
  /-- an object is a non-nil `*objTy` -/
  objAt_ptr : ∀ x o rv, objAt x o rv ⊢
    ⌜∃ p : Loc, p ≠ null ∧ x = interface.mkOk (go.GoType.PointerType objTy) #p⌝
  /-- `reflect.New(objTy)`'s allocation is the zero object -/
  newObj : ∀ p : Loc, reflectM.reflNew objTy p ⊢
    |==> objAt (interface.mkOk (go.GoType.PointerType objTy) #p) zero []
  /-- the errors the codec's `Encode` may return -/
  encErr : GoInterface → Prop

/-- **The objects' Go type** is a `runtime.Object` and not a `runtime.Unstructured` (the type
assertions the store makes, `typeSetContains`). -/
def ObjSpec.tyOk (S : ObjSpec GF Obj) : Prop :=
  go.typeSetContains (go.GoType.PointerType S.objTy)
      k8s_io.apimachinery.pkg.runtime.Object.ty = true ∧
    go.typeSetContains (go.GoType.PointerType S.objTy)
      k8s_io.apimachinery.pkg.runtime.Unstructured.ty = false

/-- `runtime.Encode(codec, x)`: the bytes of the object's encoding (after
`PrepareObjectForStorage`: no resource version), or an error. -/
def encodeOk (S : ObjSpec GF Obj) (codec : GoInterface) : IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : Obj) (Φ : val → IProp GF),
    S.objAt x o [] -∗
    ▷ (∀ (sl : GoSlice) (err : GoInterface),
        S.objAt x o [] -∗
        (⌜err = GoInterface.nil⌝ ∗ sl ↦* S.encode o ∨
          ⌜err ≠ GoInterface.nil ∧ S.encErr err⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err) -∗
        Φ (PairV #sl #err)) -∗
    WP (App (App (Val (@! k8s_io.apimachinery.pkg.runtime.Encode)) (Val #codec)) (Val #x))
      {{ Φ }})

/-- The versioner's methods on `x`: `ObjectResourceVersion` (the parse of its resource version),
`PrepareObjectForStorage` (clears it), `UpdateObject` (sets it), and `ParseResourceVersion`. -/
def versionerOk (S : ObjSpec GF Obj) (vi : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ (x : GoInterface) (o : Obj) (rv : GoString) (Φ : val → IProp GF),
      S.objAt x o rv -∗
      ▷ (∀ (n : w64) (err : GoInterface), S.objAt x o rv -∗
          ⌜match S.parseRV rv with
            | some m => err = GoInterface.nil ∧ n = m
            | none => err ≠ GoInterface.nil⌝ -∗ Φ (PairV #n #err)) -∗
      WP (App (Val #(methods vi.ty go!"ObjectResourceVersion" vi.v)) (Val #x)) {{ Φ }}) ∗
    □ (∀ (x : GoInterface) (o : Obj) (rv : GoString) (Φ : val → IProp GF),
      S.objAt x o rv -∗
      ▷ (∀ err : GoInterface, S.objAt x o [] ∗ ⌜err = GoInterface.nil⌝ -∗ Φ #err) -∗
      WP (App (Val #(methods vi.ty go!"PrepareObjectForStorage" vi.v)) (Val #x)) {{ Φ }}) ∗
    □ (∀ (x : GoInterface) (o : Obj) (rv : GoString) (n : w64) (Φ : val → IProp GF),
      S.objAt x o rv -∗
      ▷ (∀ err : GoInterface, S.objAt x o (S.fmtRV n) ∗ ⌜err = GoInterface.nil⌝ -∗ Φ #err) -∗
      WP (App (App (Val #(methods vi.ty go!"UpdateObject" vi.v)) (Val #x)) (Val #n)) {{ Φ }}) ∗
    □ (∀ (s : GoString) (Φ : val → IProp GF),
      ▷ (∀ (n : w64) (err : GoInterface),
          ⌜match S.parseRV s with
            | some m => err = GoInterface.nil ∧ n = m
            | none => err ≠ GoInterface.nil⌝ -∗ Φ (PairV #n #err)) -∗
      WP (App (Val #(methods vi.ty go!"ParseResourceVersion" vi.v)) (Val #s)) {{ Φ }}))

/-- The transformer's methods: `TransformFromStorage` (the stored value's data and staleness, or
an error if it does not read) and `TransformToStorage` (a value for the data), for any context
and authenticated data. -/
def transformerOk (S : ObjSpec GF Obj) (ti : GoInterfaceOk) : IProp GF :=
  iprop(□ (∀ (ctx : GoInterface) (vsl : GoSlice) (v : GoString) (dctx : GoInterface)
        (Φ : val → IProp GF),
      vsl ↦*□ v -∗
      ▷ (∀ (dsl : GoSlice) (st : Bool) (err : GoInterface),
          (match S.fromS v with
            | some (d, s) => ⌜err = GoInterface.nil ∧ st = s⌝ ∗ dsl ↦*□ d
            | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err) -∗
          Φ (PairV (PairV #dsl #st) #err)) -∗
      WP (App (App (App (Val #(methods ti.ty go!"TransformFromStorage" ti.v)) (Val #ctx))
        (Val #vsl)) (Val #dctx)) {{ Φ }}) ∗
    □ (∀ (ctx : GoInterface) (dsl : GoSlice) (d : GoString) (dctx : GoInterface)
        (Φ : val → IProp GF),
      dsl ↦*□ d -∗
      ▷ (∀ (vsl : GoSlice) (err : GoInterface),
          (⌜err = GoInterface.nil⌝ ∗ ∃ v, ⌜S.toS d v⌝ ∗ vsl ↦*□ v) ∨
            (⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err) -∗
          Φ (PairV #vsl #err)) -∗
      WP (App (App (App (Val #(methods ti.ty go!"TransformToStorage" ti.v)) (Val #ctx))
        (Val #dsl)) (Val #dctx)) {{ Φ }}))

/-- The decoder's `Decode(data, x, rev)`: the object the data decodes to, at resource version
`rev`, or an error (the object then holds something). -/
def decoderOk (S : ObjSpec GF Obj) (di : GoInterfaceOk) : IProp GF :=
  iprop(□ ∀ (dsl : GoSlice) (d : GoString) (x : GoInterface) (o : Obj) (rv : GoString)
      (rev : w64) (Φ : val → IProp GF),
    dsl ↦*□ d -∗ S.objAt x o rv -∗
    ▷ (∀ err : GoInterface,
        (match S.decode d with
          | some o' => ⌜err = GoInterface.nil⌝ ∗ S.objAt x o' (S.fmtRV rev)
          | none => ⌜err ≠ GoInterface.nil⌝ ∗ go_etcd_io.etcd.cache.v3.errStrOk err ∗
              ∃ o' rv', S.objAt x o' rv') -∗ Φ #err) -∗
    WP (App (App (App (Val #(methods di.ty go!"Decode" di.v)) (Val #dsl)) (Val #x)) (Val #rev))
      {{ Φ }})

/-- `runtime.SetZeroValue(x)`: the zero object. -/
def zeroOk (S : ObjSpec GF Obj) : IProp GF :=
  iprop(□ ∀ (x : GoInterface) (o : Obj) (rv : GoString) (Φ : val → IProp GF),
    S.objAt x o rv -∗
    ▷ (∀ err : GoInterface, ⌜err = GoInterface.nil⌝ ∗ S.objAt x S.zero [] -∗ Φ #err) -∗
    WP (App (Val (@! k8s_io.apimachinery.pkg.runtime.SetZeroValue)) (Val #x)) {{ Φ }})

/-- **The contract** (persistent; D30k): the codec, versioner, transformer and decoder the store
was made with, and `runtime.SetZeroValue`, meet the object specification `S`. -/
def contractOk (S : ObjSpec GF Obj) (codec : GoInterface) (vi ti di : GoInterfaceOk) :
    IProp GF :=
  iprop(⌜S.tyOk⌝ ∗ encodeOk S codec ∗ versionerOk S vi ∗ transformerOk S ti ∗ decoderOk S di ∗
    zeroOk S)

instance contractOk_persistent (S : ObjSpec GF Obj) (codec : GoInterface)
    (vi ti di : GoInterfaceOk) : Persistent (contractOk S codec vi ti di) := by
  unfold contractOk encodeOk versionerOk transformerOk decoderOk zeroOk; infer_instance

end defs

end k8s
end EtcdGrove
end Perennial
