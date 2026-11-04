/-
U4's infrastructure hypotheses (`notes/bbolt-proof-plan.md`; design §5): facts about code outside
bbolt that its error paths need and that no spec of this repository or of Perennial gives yet.
U4's proofs take them as hypotheses (as they take their callees' specs); each is discharged once
its infrastructure lands, and is no trust assumption until then (the linked results would have to
supply it).

- `errnoErrOk` (§5 item 5, D20′): a nonzero errno's `error` (`syscall.Errno`, boxed) is an error
  `fmt` formats by its `Error()`. (2026-11-04) Proved: `errnoErrOk_holds`.
- `goosLinux` (§5 item 3): `runtime.GOOS` is `"linux"` (an axiom `val` in Perennial's `runtime`).
  `DB.grow` (on its success path), `DB.allocate` and `DB.mmap` (when `MaxSize > 0`)
  compare it with `"windows"`, which is stuck on an unknown value. (2026-11-04) Now bbolt's
  package fact (`bboltRootInit`, from the trust-boundary axiom `runtime.GOOS_linux` of
  `Proof/runtime/Init.lean`): `goosLinux_of_pkgInit` gives it from `isPkgInit bbolt`.

- `errMaxSizeOk` (U4c): `ErrMaxSizeReached` is a pointer error (`errors.New`'s) that `fmt` formats:
  `DB.allocate` compares `DB.mmap`'s error with it (`err == ErrMaxSizeReached`, stuck unless one
  side's dynamic type is known comparable) and returns it. bbolt's package facts
  (`bboltErrorsVars`) say only that it is not nil; its initializer (`errors/Init.lean`) knows it is
  `errors.New`'s. To discharge: `bboltErrorsVars`' clause for it as `bboltErrorsInit`'s for
  `ErrBucketNotFound` (`IsPointerError`, with `errorString_fmtErrorOk`'s method spec).
- `pagePoolNew` (U4c): the page pool's `New` is not nil (`Open` sets it), so `Get().([]byte)`
  cannot assert on a nil interface. `dbFixed` holds `∃ f, isPool db.pagePool f pageBuf` with any
  `f`, and `sync.Pool.Get.spec` returns nil for a nil `New`. To discharge: `dbFixed` with
  `⌜f ≠ func.nil⌝`.

(2026-11-04) The error posts of `os`'s `File.Stat`/`Truncate`/`Sync`/`ReadAt`/`WriteAt` now end
with `fmtErrorOkOrNil err` (`Spec/fmt/ErrorOk.lean`; `fmtErrorOkOrNil_ne` gives `fmtErrorOk` of a
non-nil one), and `fmt.Errorf.spec`'s post has the method-set fact (`fmtErrorOk_of_errorf`).
-/
module

public import Spec.fmt.ErrorOk
public import Proof.syscall.ErrorOk
public import Perennial.Code.runtime
public import Proof.go_etcd_io.bbolt.PkgInit
public import Proof.go_etcd_io.bbolt.Inv.Bolt

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI

section infra
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **A nonzero errno's error is `fmtErrorOk`** (§5 item 5). -/
def errnoErrOk : Prop := ∀ e : w64, e ≠ 0 → ⊢ fmtErrorOk (GF := GF) (errnoErr e)

/-- `errnoErrOk` holds (2026-11-04): `syscall.Errno`'s `Error()` is now a trusted model
(`TrustedCode/syscall.lean`, some string), `errnoErr_fmtErrorOk` (`Proof/syscall/ErrorOk.lean`). -/
theorem errnoErrOk_holds [syscall.Assumptions] : errnoErrOk (GF := GF) (hG := hG) :=
  fun e he => errnoErr_fmtErrorOk e he

/-- **`ErrMaxSizeReached` is a pointer error `fmt` formats** (U4c, see the header). -/
def errMaxSizeOk : Prop :=
  isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ⊢
    ∃ e : GoInterfaceOk, globalAddr go_etcd_io.bbolt.errors.ErrMaxSizeReached ↦□ GoInterface.ok e ∗
      ⌜_root_.Perennial.errors.IsPointerError e⌝ ∗ fmtErrorOk (.ok e)

/-- **The page pool's `New` is not nil** (U4c, see the header). -/
def pagePoolNew : Prop :=
  ∀ db sp : Loc, dbFixed (GF := GF) db sp ⊢
    ∃ f : GoFunc, sync.isPool db.[go_etcd_io.bbolt.DB, go!"pagePool"] f pageBuf ∗ ⌜f ≠ func.nil⌝

end infra

/-- **`runtime.GOOS` is `"linux"`** (§5 item 3). -/
def goosLinux [GooseExts] [GoGlobalContext] : Prop :=
  _root_.Perennial.runtime.GOOS = #(go!"linux")

/-- **`runtime.GOARCH` is `"amd64"`** (§5 item 3): the logger calls of `DB.grow`, `DB.munmap`,
`DB.mmap` and `DB.allocate` format it (`%s`), which needs a string value. (2026-11-04) bbolt's
package fact (`bboltRootInit`, the trust-boundary axiom `runtime.GOARCH_amd64`):
`goarchAmd64_of_pkgInit`. -/
def goarchAmd64 [GooseExts] [GoGlobalContext] : Prop :=
  _root_.Perennial.runtime.GOARCH = #(go!"amd64")

/-- `goosLinux` from bbolt's package facts (`bboltRootInit`): in a proof holding
`#Hinit : isPkgInit bbolt`, `ihave %hgoos : ⌜goosLinux⌝ $$ []; · iapply goosLinux_of_pkgInit $$ Hinit`. -/
theorem goosLinux_of_pkgInit [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {hlc : HasLC} {GF : BundledGFunctors} [HeapGS hlc GF] [go.Semantics] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ⊢ ⌜goosLinux⌝ :=
  go_etcd_io.bbolt.bboltRootInit_goos

/-- `goarchAmd64` from bbolt's package facts (`bboltRootInit`), as `goosLinux_of_pkgInit`. -/
theorem goarchAmd64_of_pkgInit [GooseExts] [GooseSemantics] [GooseInterp] [GoGlobalContext]
    {hlc : HasLC} {GF : BundledGFunctors} [HeapGS hlc GF] [go.Semantics] :
    isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ⊢ ⌜goarchAmd64⌝ :=
  go_etcd_io.bbolt.bboltRootInit_goarch

end bbolt
end EtcdGrove
end Perennial
