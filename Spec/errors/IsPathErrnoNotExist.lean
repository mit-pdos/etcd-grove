/-
`errors.Is(err, os.ErrNotExist)` of a `*PathError` of a nonzero errno (`os.errnoPathErr err e`, what the
`os` models return on a failed system call): it answers `e = ENOENT`. Moved out of
`Spec/go_etcd_io/etcd/server/v3/storage/wal/ExistCallees.lean` (2026-11-22, unchanged), so that
`durable`'s `tryRead`, and kvraft's part through it, take it without the WAL's `fileutil` specs.

* **`errIsNotExist err b`**: `errors.Is(err, os.ErrNotExist)` returns `b` (persistent; for any value of
  the `os.ErrNotExist` variable).
* **`errors.IsPathErrnoNotExist.spec`**: true in Go (`errors.Is` unwraps the `*PathError` to the `Errno`,
  whose `Is` compares the target with `oserror.ErrNotExist`). Proved (`Proof/errors/IsPathErrnoNotExist.lean`,
  2026-11-22) over Perennial's `errors.Is`, `syscall.Errno.Is` and `os`'s package fact that `os.ErrNotExist`
  is `oserror.ErrNotExist`.
Lean-first.
-/
module

public import Proof.os.ErrnoPathErr
public import Proof.os.PkgInit

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

/-- **`errors.Is(err, os.ErrNotExist)` returns `b`** (persistent). -/
def errIsNotExist (err : GoInterface) (b : Bool) : IProp GF :=
  iprop(□ ∀ (t : GoInterface) (Φ : val → IProp GF),
    typedPointsto (globalAddr os.ErrNotExist) t DFrac.discard -∗ ▷ Φ #b -∗
      WP (App (App (Val (@! _root_.Perennial.errors.Is)) (Val #err)) (Val #t)) {{ Φ }})

instance errIsNotExist_persistent (err : GoInterface) (b : Bool) :
    Persistent (errIsNotExist (GF := GF) err b) := by
  unfold errIsNotExist; infer_instance

/-- See the file header. -/
abbrev errors.IsPathErrnoNotExist.spec : Prop :=
  ∀ (err : GoInterface) (e : w64), e ≠ 0 →
    ⊢ isPkgInit (PROP := IProp GF) pkg_id.os -∗ os.errnoPathErr (GF := GF) err e -∗
      errIsNotExist (GF := GF) err (decide (e = Fs.ENOENT))

end defs

end EtcdGrove
end Perennial
