/-
The package fact of `github_com.rs.zerolog` (translated with bodies; dsv-retire-3, 2026-11-26,
mit-pdos/etcd-grove#49 step 3): `zerologInit`, what its functions' proofs read, persistent (`↦□`: no
client writes zerolog's variables after its initializer, the dsv-fix6 review's condition 1):
- `gLevel`'s pointer, to an `int32` cell (`new(int32)`) in an invariant (`SetGlobalLevel` stores
  into it atomically, `GlobalLevel` loads it);
- `LevelFieldName` (`"level"`) and `LevelFieldMarshalFunc`, with its spec on the five levels
  `Trace`..`Error` (`marshalSpec`: `Level.String`, reading `Level*Value`, which the initializer
  makes read-only to prove it);
- `enc` (`internal/json`'s `Encoder{}`);
- `eventPool`'s pointer, a `sync.Pool` of events (`eventElem`: an `*Event` with its buffer owned),
  whose `New` (`&Event{buf: make([]byte, 0, 500)}`) needs nothing;
- `ioutil.Discard`'s value (from `io/ioutil`'s fact), the writer `New(nil)` takes.
-/
module

public import Dsverify.GeneratedProof.github_com.rs.zerolog
public import Net.Proof.net.Base
public import Perennial.Proof.bytes.Base
public import Perennial.Proof.context.Base
public import Perennial.Proof.fmt.Base
public import Perennial.Proof.io.Base
public import Perennial.Proof.math.Base
public import Perennial.Proof.math.rand.Base
public import Perennial.Proof.sort.Base
public import Perennial.Proof.strconv.Base
public import Perennial.Proof.strings.Base
public import Perennial.Proof.sync.Base
public import Perennial.Proof.sync.atomic.Base
public import Perennial.Proof.time.Base
public import Perennial.Proof.unsafe.Base
public import Perennial.Proof.runtime.Base
public import Proof.encoding.json.Base
public import Proof.os.Base
public import Proof.path.filepath.PkgInit
public import Dsverify.Proof.io.ioutil.Base
public import Dsverify.Proof.github_com.rs.zerolog.internal.json.Base
public import Perennial.Proof.sync.PoolDefs

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial

open Iris Iris.BI

namespace github_com.rs.zerolog

section def_
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt Net.netExt] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- The five levels whose `Msg` neither panics nor exits: `Trace` (-1), `Debug`, `Info`, `Warn`,
`Error`. -/
def fiveLevels : List w8 := [W8 (-1), W8 0, W8 1, W8 2, W8 3]

/-- `Level.String` (`log.go`) on the five levels, at the initial `Level*Value`s. -/
def levelString (lv : w8) : GoString :=
  if lv = W8 (-1) then go!"trace" else if lv = W8 0 then go!"debug" else if lv = W8 1 then go!"info"
  else if lv = W8 2 then go!"warn" else go!"error"

/-- `LevelFieldMarshalFunc`'s value `f` maps each of the five levels to its name. -/
def marshalSpec (f : GoFunc) : IProp GF :=
  iprop(∀ lv : w8, {{ ⌜lv ∈ fiveLevels⌝ }} (App (Val #f) (Val #lv)) {{ RET #(levelString lv); True }})

instance marshalSpec_persistent (f : GoFunc) : Persistent (marshalSpec (GF := GF) f) := by
  unfold marshalSpec; infer_instance

/-- What `eventPool` holds (and its `New` returns): an `any` holding an `*Event` at `l`, with the
event and its buffer owned. -/
def eventElem (x : GoAny) : IProp GF :=
  iprop(∃ (l : Loc) (v : Event) (bs : List w8),
    ⌜x = interface.mkOk (go.GoType.PointerType Event.ty) #l⌝ ∗ l ↦ v ∗
    v.buf' ↦* bs ∗ ownSliceCap w8 v.buf' (DFrac.own 1))

/-- The invariant name of `gLevel`'s cell. -/
def gLevelN : Namespace := ndot nroot "zerolog_gLevel"

/-- The package fact (the file header). -/
def zerologInit : IProp GF :=
  iprop((∃ p : Loc, globalAddr gLevel ↦□ p ∗ inv gLevelN (∃ v : w32, p ↦ v)) ∗
    globalAddr LevelFieldName ↦□ go!"level" ∗
    (∃ f : GoFunc, globalAddr LevelFieldMarshalFunc ↦□ f ∗ marshalSpec f) ∗
    globalAddr enc ↦□ (zero_val _root_.Perennial.github_com.rs.zerolog.internal.json.Encoder) ∗
    (∃ (ep : Loc) (f : GoFunc), globalAddr eventPool ↦□ ep ∗ ⌜f ≠ func.nil⌝ ∗
      sync.isPool ep f iprop(True) eventElem) ∗
    (∃ w : GoInterface, globalAddr _root_.Perennial.io.ioutil.Discard ↦□ w))

instance zerologInit_persistent : Persistent (zerologInit (GF := GF)) := by
  unfold zerologInit; infer_instance

instance isPkgInit_inst : IsPkgInit (IProp GF) pkg_id.github_com.rs.zerolog :=
  define_is_pkg_init zerologInit
instance get_isPkgInit_wf_inst : GetIsPkgInitWf (IProp GF) pkg_id.github_com.rs.zerolog :=
  build_get_is_pkg_init_wf

end def_

section access
variable [GooseExts] [GooseSemantics] [GooseInterp] [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [sem : go.Semantics]

/-- `isPkgInit` of zerolog holds its fact. -/
theorem zerologInit_access :
    isPkgInit (PROP := IProp GF) pkg_id.github_com.rs.zerolog ⊢ zerologInit (GF := GF) := by
  with_unfolding_all exact isPkgInit_access (PROP := IProp GF) pkg_id.github_com.rs.zerolog


end access

end github_com.rs.zerolog
end Perennial
