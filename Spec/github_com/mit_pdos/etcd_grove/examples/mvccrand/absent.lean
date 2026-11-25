/- Lean-first (no Rocq counterpart).

`absent(p)` (`examples/mvccrand/start.go`, P3 of the pure-premise plan, 2026-11-24): `os.Lstat(p)`,
then `err != nil && errors.Is(err, os.ErrNotExist)`. Of `p = d/b`, the name `b` of a directory `j`
(the path of `d`, the whole claim on `b`, a share of `d`'s call permission, in the tree's shared mode),
where the file system does not fail (`FsNoErrAt (d/b)`): nothing changed, and **`true` only if `b`
holds nothing**. (Not the converse: `Lstat` of a name holding nothing may fail with another errno.)
Over the file extension's instances, which the spec quantifies (the Link has none).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.mvccrand.Base
public import Proof.runtime.RootClaim

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace mvccrand

open Iris Iris.BI github_com.mit_pdos.etcd_grove.examples.mvccrand
open Fs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.mit_pdos.etcd_grove.examples.mvccrand.Assumptions]

/-- See the file header. -/
abbrev absent.spec : Prop :=
  ∀ [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
    (d b : GoString) (R : Roots) (j : Ino) (qd : Qp) (h : NamesH) (qc : Qp),
  NameOk b → FsNoErrAt (child d b) →
  {{ isPkgInit (PROP := IProp GF) pkg_id.github_com.mit_pdos.etcd_grove.examples.mvccrand ∗
      osInv (GF := GF) ∗ osSharedInv (GF := GF) R ∗ osPathS (GF := GF) R d (DFrac.own qd) j ∗
      osNames (GF := GF) j (.only [b]) (DFrac.own 1) h ∗ osCallPerm (GF := GF) (callKey R d) qc }}
    (App (Val (@! github_com.mit_pdos.etcd_grove.examples.mvccrand.absent)) (Val #(child d b)))
  {{ (res : Bool), RET #res; osPathS R d (DFrac.own qd) j ∗ osNames j (.only [b]) (DFrac.own 1) h ∗
      osCallPerm (callKey R d) qc ∗ ⌜res = true → h.cur !! b = none⌝ }}

end spec

end mvccrand
end EtcdGrove
end Perennial
