/-
Trusted code for `k8s.io/klog/v2/internal/serialize`, in namespace
`k8s_io.klog.v2.internal.serialize` like the generated package
(`Code/k8s_io/klog/v2/internal/serialize.toml`): klog's key/value serializer `FormatKVs` (klog-infos,
2026-11-23, etcd-grove#25), which klog's translated `loggingT.printS` calls. The model is **never
more defined than Go**: where it returns, Go returns after effects of which the model's are a
possible case (on what translated code can read); everywhere else the model is stuck.
-/
module

public import Perennial.Golang.Defn
public import Perennial.Code.bytes
public import Perennial.Code.time
public import Perennial.TrustedCode.arbitraryString

@[expose] public section

set_option linter.iris.style.nameCheck false

namespace Perennial
namespace k8s_io.klog.v2.internal.serialize
noncomputable section
section code
variable [GooseExts] [GoGlobalContext]

/-- `schema.GroupResource`'s type (`k8s.io/apimachinery/pkg/runtime/schema`'s translation names it
`GroupResource.ty`; klog does not import that package, so the model names the type). -/
@[reducible] def model.GroupResource : go.GoType :=
  go.GoType.Named go!"k8s.io/apimachinery/pkg/runtime/schema.GroupResource" []

/-- Whether the key or value `x` (an `interface{}`) has one of the dynamic types the model follows:
`string`, `int`, `time.Duration` or `schema.GroupResource` (each test is Go's `_, ok := x.(T)`).
Not a Go function: a helper of `FormatKVs.impl`. -/
noncomputable def model.kvOk : val :=
  λ: "x",
    (Snd (App (Val (GoInstruction (TypeAssert2 go.string))) (Var "x"))) ||
    (Snd (App (Val (GoInstruction (TypeAssert2 go.int))) (Var "x"))) ||
    (Snd (App (Val (GoInstruction (TypeAssert2 _root_.Perennial.time.Duration.ty))) (Var "x"))) ||
    (Snd (App (Val (GoInstruction (TypeAssert2 model.GroupResource))) (Var "x")))

/-- Reads every element of the `[]interface{}` `s`, first to last, and is stuck (`Panic`, the
primitive that takes no step: undefined behaviour, not a Go panic) at the first that `model.kvOk`
rejects. Not a Go function: a helper of `FormatKVs.impl`. -/
noncomputable def model.checkKVs : val :=
  rec: "loop" "s" :=
    if: #(W64 0) <⟨go.int⟩ FuncResolve go.len [go.SliceType go.any] #() "s" then
      (if: model.kvOk (![go.any] (IndexRef (go.SliceType go.any) ("s", #(W64 0)))) then #()
       else Panic "klog serialize: a key or value of a type the model does not follow") ;;
      "loop" (Slice (go.SliceType go.any)
        ("s", #(W64 1), FuncResolve go.len [go.SliceType go.any] #() "s"))
    else #()

/-- `model.checkKVs` of every `[]interface{}` of the `[][]interface{}` `kvs`, first to last. Not a
Go function: a helper of `FormatKVs.impl`. -/
noncomputable def model.checkAll : val :=
  rec: "loop" "kvs" :=
    if: #(W64 0) <⟨go.int⟩ FuncResolve go.len [go.SliceType (go.SliceType go.any)] #() "kvs" then
      model.checkKVs (![go.SliceType go.any]
        (IndexRef (go.SliceType (go.SliceType go.any)) ("kvs", #(W64 0)))) ;;
      "loop" (Slice (go.SliceType (go.SliceType go.any))
        ("kvs", #(W64 1), FuncResolve go.len [go.SliceType (go.SliceType go.any)] #() "kvs"))
    else #()

/-- `FormatKVs(b *bytes.Buffer, kvs ...[]interface{})` (klog v2.140.0,
`internal/serialize/keyvalues.go:64-167`, `keyvalues_slog.go:31-119`, `keyvalues.go:180-298`):
`Formatter{}.FormatKVs(b, kvs...)`. For each key/value pair of each slice (a missing last value is
`"(MISSING)"`), `KVFormat` writes to `b` a space, the key (a `string` as is, another type through
`fmt.Sprintf("%s", k)`) and the value: through its `WriteText`, `slog`'s JSON, its `String()`
(`StringerToString`, recovering a panic), as a quoted string (`writeStringValue`:
`strconv.Quote`, or a `=<` block for a multi-line string), its `Error()`, `MarshalLog()`,
`LogValue()`, `%+q` of a `[]byte`, or else `=` and `encoding/json`'s encoding (`formatAny`,
`formatAsJSON`: reflection, calling `MarshalJSON`/`MarshalText` methods). A key formatted again
later ("last one wins") has its earlier output cut out: `FormatKVs` truncates `b` to the start of
the first obsolete pair and rewrites the rest it keeps, from bytes it wrote itself; the bytes `b`
held before the call stay. It reads the slices' elements and writes nothing else.

**The model:** reads every key and value of every slice and is stuck unless each is a `string`, an
`int`, a `time.Duration` or a `schema.GroupResource` (`model.checkAll`); then appends an arbitrary
string to `b` (`fmt.arbitraryString`, which can return every string, through `bytes.Buffer.Write` of
a new `[]byte`) and returns.

**Why faithful:** for those four types Go calls no foreign code and cannot panic: a `string` key is
written as is; an `int` key is formatted by `fmt.Sprintf("%s", k)` (`%!s(int=…)`); `Duration` and
`GroupResource` implement `fmt.Stringer` (and neither `textWriter`, `slog.Value`'s type nor
`slog.LogValuer`, which come before it in the type switch), so a value of either is
`writeStringValue(b, v.String())` (their `String` methods, `time/time.go` and
`apimachinery/pkg/runtime/schema/group_version.go`, format their fields and return) and a key of
either is `fmt.Sprintf("%s", k)`, which calls the same `String`; a `string` value is
`writeStringValue`; an `int` value is `=` and `json.NewEncoder(b).Encode(v)` (its decimal and a
newline, the newline then truncated), which cannot fail for an `int`. The de-duplication only
truncates and rewrites bytes `FormatKVs` wrote. So Go returns, having appended some bytes to `b`
and changed nothing else translated code reads; the model's arbitrary string includes them. Go's
`Write`s grow `b` as the model's one `Write` does (`bytes.Buffer`'s `ErrTooLarge` panic is
unreachable, as `grow`'s spec shows). The model is stuck everywhere else, less defined than Go. -/
noncomputable def FormatKVs.impl : val :=
  λ: "b" "kvs",
    model.checkAll "kvs" ;;
    App (App (Val (GoInstruction (MethodResolve (go.GoType.PointerType _root_.Perennial.bytes.Buffer.ty)
        go!"Write"))) (Var "b"))
      (Convert go.string (go.SliceType go.byte) (_root_.Perennial.fmt.arbitraryString #())) ;;
    #()

end code
end
end k8s_io.klog.v2.internal.serialize
end Perennial
