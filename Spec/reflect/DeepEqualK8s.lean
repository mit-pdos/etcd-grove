/-
`reflect.DeepEqual(x, y)` (names-only in Perennial: reflection) on what the maintainers' checker
compares (k8s 7g, `notes/k8s-7g-trust.md`): its result is equality of the arguments' deep values
(`k8sDeep.DeepV`, `Proof/.../k8s/etcd3/Deep.lean`). Three clauses, at the three shapes of argument
the checker's calls pass:

1. two interface values (a `runtime.Object` or an `error`, converted to `any`, which keeps the
   interface value): `Model.update`'s no-op check and `compareEvents` (`*Obj`), `ValidateWatch`
   (errors);
2. two `correctness.Response` structs (converted to `any`: `interface.mkOk Response.ty`): `Step`,
   `validateGet`, `validateList`, `equalListResponse`, `Replay.validateGet`;
3. two `map[string]runtime.Object` (`Model.Equal`'s `Items`);
4. two `correctness.Response` structs, the first with deep values (object and error), the second
   with a deep object and an `*apierrors.StatusError` error (storage's too-large error, which has
   no `DeepV`): `false` (`Step`'s writes, `validateGet`, `validateList` and `equalListResponse`
   compare the model's expected response, first, with the store's output, which may hold one).
   Added 2026-11-18 (option (B), decided by etcd-grove-03).

Stated at these types only (as `reflect.DeepEqual.spec_pgidSet`, `Spec/reflect/DeepEqual.lean`):
the trust boundary, a second trust-boundary spec of the function at other types (the spec
skill's exception for the trust boundary). Its axiom will be `reflect.DeepEqual.wp_proof_k8s`.

Faithful (`reflect/deepequal.go`, go1.27.3): `DeepEqual(x, y)` returns `x == y` if either is a
nil interface (clause 1, view `nil`: equal iff both nil); `false` if the dynamic types differ
(each `DeepV` constructor fixes one dynamic type); else `deepValueEqual`, which, by kind:
for a pointer, `true` if the two are the same pointer, else compares the pointees; for a struct,
every field in order, exported or not (`Obj`'s, `ObjList`'s, `StorageError`'s `Code`, `Key`,
`ResourceVersion` and inner `err`, `errorString`'s `s`); for an interface field, as at the top
(nil-ness, dynamic type, value); for a slice, `false` if exactly one is nil
(`IsNil`, the model's `= slice.nil`), `false` if the lengths differ, `true` if they share the
array and length, else element by element up to the length (not the capacity); for a map,
`false` if exactly one is nil (here neither: `ownMap_not_nil`), `false` if the lengths differ,
`true` if the same map, else every key of the first is a key of the second with a deeply equal
value; strings, `uint64`, `int64`, `int` and `bool` by `==`, which is Lean's equality of their
values. None of the types holds a float, a function, a channel or a cycle, so no `NaN`, no
"functions are equal only if nil", and the cycle check never fires. Each shortcut (same pointer,
same array, same map) answers what the full comparison would, given the points-tos. It reads only
the cells `deepRep` holds, so the result is a function of the held state; it allocates nothing
the caller sees, never panics on these types, and writes nothing. Go evidence:
`examples/k8s/etcd3/trustspecs_test.go` `TestDeepEqualViews` (60000 random pairs of the three
shapes, materialized with random spare capacity and pointer sharing: `DeepEqual` is `viewEq`, the
Go mirror of `=` on `DeepV`), `TestDeepEqualNamedCases` (unexported fields compared; a typed nil
`*Obj` is not the nil interface; capacity ignored; a nil map value differs from an object),
`realfacts_test.go` `TestDeepEqualFacts` (22 cases: nil and empty `Items` differ; the remaining
count by its pointee; two `NewInvalidObjError` of one message equal; an empty and a nil map
differ).

Clause 4 (faithful by the same rules): the two `Response`s have one type, so `deepValueEqual`
compares the fields in order; `Object` reads only the cells the two `deepRep`s hold, and if the
objects differ the answer is `false` already; then `Err`: if the first is the nil interface
(`de1 = nil`) and the second is not (an interface holding a `*StatusError`, nil or not, is not the
nil interface), `false`; else the dynamic types differ (no `DeepV` constructor is a
`*StatusError`: `*Obj`, `*ObjList`, `*StorageError`, `*errorString`), `false`, without reading
the `*StatusError` (so no ownership of `l` is needed; `l` may be null). Go evidence:
`trustspecs_test.go` `TestDeepEqualTooLarge` (the first response's object and error drawn from the
views of `TestDeepEqualViews`, the second's object too, its error
`storage.NewTooLargeResourceVersionError` with each retry setting, a zero `*StatusError` and a
typed nil `*StatusError`: `DeepEqual` is `false` in both argument orders, and never panics).

Not covered (no claim): a typed nil pointer in an interface (no `DeepV` holds one), any other
dynamic type (`*apierrors.StatusError` except as clause 4's second error, `*fmt.wrapError`,
`*metav1.Status`), maps of other types.
That no `DeepV` is a `*apierrors.StatusError` is what makes clause 4 true: two equal
StatusErrors, or two typed-nil ones, are DeepEqual-true in Go; a `DeepV` constructor for
`*StatusError` (or a type embedding one) must revisit clause 4 (attack 2, m2, 2026-11-18).
Lean-first.
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.Deep

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI map k8sDeep

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev reflect.DeepEqual.spec_k8s : Prop :=
  (∀ (x1 x2 : GoInterface) (d1 d2 : DeepV) (dq1 dq2 : DFrac),
    {{ deepRep (GF := GF) dq1 x1 d1 ∗ deepRep dq2 x2 d2 }}
      (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual [])) (Val #x1)) (Val #x2))
    {{ (b : Bool), RET #b; ⌜b = true ↔ d1 = d2⌝ ∗ deepRep dq1 x1 d1 ∗ deepRep dq2 x2 d2 }}) ∧
  (∀ (o1 e1 o2 e2 : GoInterface) (do1 de1 do2 de2 : DeepV) (dq1 dq2 : DFrac),
    {{ deepRep (GF := GF) dq1 o1 do1 ∗ deepRep dq1 e1 de1 ∗
        deepRep dq2 o2 do2 ∗ deepRep dq2 e2 de2 }}
      (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual []))
        (Val #(interface.mkOk
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.ty
          #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.mk o1 e1))))
        (Val #(interface.mkOk
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.ty
          #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.mk o2 e2))))
    {{ (b : Bool), RET #b; ⌜b = true ↔ do1 = do2 ∧ de1 = de2⌝ ∗
        deepRep dq1 o1 do1 ∗ deepRep dq1 e1 de1 ∗ deepRep dq2 o2 do2 ∗ deepRep dq2 e2 de2 }}) ∧
  (∀ (m1 m2 : Loc) (M1 M2 : GMap GoString GoInterface) (D1 D2 : GMap GoString DeepV)
      (dq1 dq2 : DFrac),
    {{ (m1 ↦${dq1} M1 : IProp GF) ∗ mapRep dq1 M1 D1 ∗ m2 ↦${dq2} M2 ∗ mapRep dq2 M2 D2 }}
      (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual []))
        (Val #(interface.mkOk (go.GoType.MapType go.string
          k8s_io.apimachinery.pkg.runtime.Object.ty) #m1)))
        (Val #(interface.mkOk (go.GoType.MapType go.string
          k8s_io.apimachinery.pkg.runtime.Object.ty) #m2)))
    {{ (b : Bool), RET #b; ⌜b = true ↔ D1 = D2⌝ ∗
        m1 ↦${dq1} M1 ∗ mapRep dq1 M1 D1 ∗ m2 ↦${dq2} M2 ∗ mapRep dq2 M2 D2 }}) ∧
  (∀ (o1 e1 o2 : GoInterface) (l : Loc) (do1 de1 do2 : DeepV) (dq1 dq2 : DFrac),
    {{ deepRep (GF := GF) dq1 o1 do1 ∗ deepRep dq1 e1 de1 ∗ deepRep dq2 o2 do2 }}
      (App (App (Val #(functions _root_.Perennial.reflect.DeepEqual []))
        (Val #(interface.mkOk
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.ty
          #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.mk o1 e1))))
        (Val #(interface.mkOk
          github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.ty
          #(github_com.mit_pdos.etcd_grove.examples.k8s.etcd3.correctness.Response.mk o2
            (interface.mkOk (go.GoType.PointerType
              k8s_io.apimachinery.pkg.api.errors.StatusError.ty) #l)))))
    {{ (b : Bool), RET #b; ⌜b = false⌝ ∗
        deepRep dq1 o1 do1 ∗ deepRep dq1 e1 de1 ∗ deepRep dq2 o2 do2 }})

end spec

end EtcdGrove
end Perennial
