/-
`fbr.Read(p)` (the method promoted from the embedded `*bufio.Reader`): `bufio.Reader.Read`'s spec
on the embedded reader. Proved in `LinuxFs/Proof/go_etcd_io/etcd/client/pkg/v3/fileutil/FileBufReader__Read.lean`.
W3a of `notes/wal-fsext-plan.md`; Lean-first.
-/
module

public import LinuxFs.GeneratedProof.go_etcd_io.etcd.client.pkg.v3.fileutil
public import LinuxFs.Proof.bufio.Defs

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions]
variable [bufio_sem : _root_.Perennial.bufio.Assumptions]

/-- See the file header. -/
abbrev go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.Read.spec : Prop :=
  ∀ (fbr b : Loc) (fi err : GoInterface) (dq : DFrac) (ri : GoInterfaceOk) (S : List w8 → IProp GF)
    (E : List w8 → GoInterface → Prop) (r : List w8) (p : GoSlice) (xs : List w8),
  ⊢ io.readerStream ri S E -∗ (□ ∀ r', S r' -∗ ⌜r'.length + 2 ^ 12 < 2 ^ 62⌝) -∗
    {{ ⌜r.length + xs.length < 2 ^ 62⌝ ∗
        fbr ↦{dq} go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err ∗ bufio.ownReader b ri S E r ∗ p ↦* xs }}
      (App (Val (fbr @!! go.GoType.PointerType go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.ty @!! go!"Read")) (Val #p))
    {{ (n : w64) (e : GoInterface), RET (PairV #n #e);
        ∃ ys : List w8, ⌜sint.Z n = ys.length ∧ ys.length ≤ xs.length ∧
          (e ≠ GoInterface.nil → E (r ++ ys) e)⌝ ∗
        p ↦* (ys ++ xs.drop ys.length) ∗ fbr ↦{dq} go_etcd_io.etcd.client.pkg.v3.fileutil.FileBufReader.mk b fi err ∗
        bufio.ownReader b ri S E (r ++ ys) }}

end spec

end EtcdGrove
end Perennial
