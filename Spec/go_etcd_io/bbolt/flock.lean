module
public import Proof.go_etcd_io.bbolt.Init
public import Proof.os.FileModel

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bbolt

open Iris Iris.BI go_etcd_io.bbolt

section spec
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.bbolt.Assumptions]

/-- `flock(db, exclusive, timeout)`: tries `Flock(fd, LOCK_EX or LOCK_SH | LOCK_NB)` until it
succeeds, fails other than with `EWOULDBLOCK`, or (`timeout ≠ 0`) the time is up
(`ErrTimeout`). The lock has no effect here (the process is the file's only user). With
`timeout = 0` and the lock held by another process, it retries forever (not a safety
violation: it never returns). Over the field it reads. -/
abbrev flock.spec : Prop :=
  ∀ (dbl f : Loc) (fd : w64) (dq : DFrac) (exclusive : Bool) (tmo : w64),
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.bbolt ∗
      structFieldRef DB go!"file" dbl ↦{dq} f ∗ osFile f fd }}
    (App (App (App (Val #(functions flock [])) (Val #dbl)) (Val #exclusive)) (Val #tmo))
  {{ (err : GoInterface), RET #err; structFieldRef DB go!"file" dbl ↦{dq} f }}

end spec

end bbolt
end EtcdGrove
end Perennial
