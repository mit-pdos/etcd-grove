/-
The lab's model of Go's `encoding/json` (`harness/rpcmodel/src/encoding/json`, notes/vsr-net.md):
its package-initialized state and `initialize'`. The specs of its functions are in
`Proof/encoding/json/*`.

**`isPkgInit pkg_id.encoding.json`** (`isInit`, persistent), stated with no parameter but the
kit class `JsonKit`, so that any package importing `encoding/json` gets its `IsPkgInit`
instance: `codecMu` is a mutex guarding `codec` (`codecInv`): `codec` is nil (with full
ownership), or a non-nil `*Codec` for good (`↦□`: the first `SetCodec` wins) whose fields hold,
for good, the kit's codec functions (`codecFns`: `jsonMarshal` and `jsonUnmarshal`, which kitgen
generates into the kit's package `JsonKit.pkg`, and `dsverify.lab/harness/jsoncodec.Scan`).

`JsonKit` has a default instance of low priority (`JsonKit.none`, an empty package path) for
kits that import `encoding/json` without a codec of their own (kits/epaxos-net): with it no
`SetCodec` can be proved (its spec needs the functions of a package that does not exist), so
`codec` stays nil, and every use of the codec is unprovable (it panics in the model). A kit with
`[json]` gets an instance generated into its statement, which takes precedence.
-/
module

public import Perennial.Proof.ProofPrelude
public import Perennial.Proof.sync.Base
public import Perennial.Proof.io.Base
public import Perennial.Spec.sync.initialize
public import Perennial.Spec.io.initialize
public import Harness.GeneratedProof.encoding.json

@[expose] public section

noncomputable section

namespace Perennial

open Iris Iris.BI Iris.ProgramLogic Iris.Std Iris.ProofMode

namespace encoding.json

/-- The kit whose codec the program registers: the package path of its generated
`registerJSON`, `jsonMarshal` and `jsonUnmarshal` (kitgen, from kit.toml's `[json]`). -/
class JsonKit where
  /-- the package of the kit's generated codec functions -/
  pkg : GoString

/-- No kit codec (see the file header). -/
instance (priority := low) JsonKit.none : JsonKit := ⟨go!""⟩

/-- The kit's generated function `name` (in `JsonKit.pkg`). -/
def kitFn [GooseExts] [GoSemanticsFunctions] [JsonKit] (name : GoString) : GoFunc :=
  functions (JsonKit.pkg ++ go!"." ++ name) []

/-- `jsoncodec.Scan`, the scanner every codec registers. -/
def scanFn [GooseExts] [GoSemanticsFunctions] : GoFunc :=
  functions go!"dsverify.lab/harness/jsoncodec.Scan" []

section init
variable [JsonKit]
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The `*Codec` `c` holds the kit's codec functions, for good (persistent). -/
def codecFns (c : Loc) : IProp GF :=
  iprop(structFieldRef encoding.json.Codec go!"Marshal" c ↦□ kitFn go!"jsonMarshal" ∗
    structFieldRef encoding.json.Codec go!"Unmarshal" c ↦□ kitFn go!"jsonUnmarshal" ∗
    structFieldRef encoding.json.Codec go!"Scan" c ↦□ scanFn)

instance codecFns_persistent (c : Loc) : Persistent (codecFns (GF := GF) c) := by
  unfold codecFns; infer_instance

/-- The invariant of `codecMu`: `codec` is nil, or a non-nil codec holding the kit's functions,
that stays. -/
def codecInv : IProp GF :=
  iprop(globalAddr codec ↦ (null : Loc) ∨
    ∃ c : Loc, ⌜c ≠ null⌝ ∗ globalAddr codec ↦□ c ∗ codecFns c)

/-- The package-initialized state of `encoding/json` (persistent); see the file header. -/
abbrev isInit : IProp GF :=
  iprop("#HcodecMu" ∷ sync.isMutex (globalAddr codecMu) codecInv ∗ "_" ∷ True)

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.encoding.json :=
  define_is_pkg_init isInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.encoding.json :=
  build_get_is_pkg_init_wf

theorem isInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.encoding.json ⊢ isInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.encoding.json

end init

end encoding.json

section spec
variable [encoding.json.JsonKit]
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : encoding.json.Assumptions]

/-- `encoding/json`'s `initialize'`: it initializes `sync` and `io` and allocates `codecMu`
and `codec` (nil). -/
abbrev encoding.json.initialize'.spec : Prop :=
  ∀ (get_is_pkg_init : GoString → IProp GF),
  GetIsPkgInitProp pkg_id.encoding.json get_is_pkg_init →
    {{ ownInitializing get_is_pkg_init }}
      (App (Val encoding.json.initialize') (Val #()))
    {{ RET #(); ownInitializing get_is_pkg_init ∗
        isPkgInit (PROP := IProp GF) pkg_id.encoding.json }}

set_option goose.wp.extras true in
theorem encoding.json.initialize'.wp_proof
    (wp_sync_initialize : sync.initialize'.spec (GF := GF) (hG := hG))
    (wp_io_initialize : io.initialize'.spec (GF := GF) (hG := hG)) :
    encoding.json.initialize'.spec (GF := GF) (hG := hG) := by
  intro get_is_pkg_init Hinit
  wp_start as Hown
  iapply wp_package_init (heq := Hinit.1) $$ [Hown] HΦ
  iframe Hown
  iintro Hown
  iapply wp_fupd
  wp_auto
  wp_apply wp_GlobalAlloc (V := Loc) encoding.json.codec
    (go.GoType.PointerType encoding.json.Codec.ty) as Hcodec
  wp_apply wp_GlobalAlloc (V := sync.Mutex) encoding.json.codecMu sync.Mutex.ty as HcodecMu
  wp_apply wp_io_initialize _ Hinit.2.2.1 $$ Hown as ⟨Hown, #Hio⟩
  wp_apply wp_sync_initialize _ Hinit.2.1 $$ Hown as ⟨Hown, #Hsync⟩
  imod sync.init_Mutex encoding.json.codecInv ⊤ (globalAddr encoding.json.codecMu)
      $$ [HcodecMu] [Hcodec] with #HcMu
  · iexact HcodecMu
  · inext; unfold encoding.json.codecInv; ileft; iexact Hcodec
  imodintro
  isplitr
  · ipureintro; exact isPanic_intoVal ()
  iframe Hown
  is_pkg_init_finish
  imodintro
  isplitl
  · iexact HcMu
  itrivial

end spec

end Perennial
