/-
The callee specs `wal.Create`'s proof takes as hypotheses that no other spec states yet (W4 of
`notes/wal-fsext-plan.md`, eleventh session). Each is a triple of the real code, stated for
`Create`'s use; none is proved yet (the W4 log says what each needs).

* **`tmpDirH j b h`**: the whole claim on the name `b` of `j` (its history `h`), `b` holding nothing
  or a directory of files only, whose whole claim is held too: what `Create` keeps of its temporary
  directory `nm.tmp` (a leftover's, `walAreaRes`), and what `RemoveAll`/`CreateDirAll` leave of it.
* **`wal.Exist.specCreate`** (W12 states `Exist` over `walDirIs`; `Create` needs only that it
  returns): `Exist(dir)` with `Create`'s resources, unchanged.
* **`fileutil.CreateDirAll.specTmp`**: `CreateDirAll.spec` (proved, `name` absent) extended to a
  `name` holding a directory of files (a leftover `nm.tmp` that `Exist` missed, a `Stat` error, or
  that `RemoveAll` returned `nil` on, `ENOENT` with no effect: `os.RemoveAll.specDirS`'s header), and
  its error arm narrowed to `tmpDirH` (the proved spec's `osSubtreeH`: `TouchDirAll`'s `MkdirAll`
  creates one directory, `IsDirWriteable` a file in it). Success: as `CreateDirAll.spec` (an empty
  directory: `ReadDir` found none).
* **`os.RemoveAll.specAbsentN`**: `os.RemoveAll.specAbsentS` (proved) for a fraction of a claim on any
  names holding `b` (the proved one takes `.only [b]`; the extension's leaf steps,
  `wp_osUnlinkS_none`/`wp_osRmdirS_none`, take `.only [b]`, and the absent case logs nothing, so
  their generalization to `N ∋ b` is the proof). `renameWAL`'s `RemoveAll(dir)` and `Create`'s
  deferred `RemoveAll(dir.tmp)` after the rename hold half of the creating claim `.only [nm, nm.tmp]`.
Lean-first.
-/
module

public import LinuxFs.Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll
public import LinuxFs.Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import LinuxFs.GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section defs
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]

/-- **The whole of the name `b` of `j` (its claim's history `h`), holding nothing or a directory of
files** (whose whole claim is held). -/
def tmpDirH (j : Ino) (b : GoString) (h : NamesH) : IProp GF :=
  iprop(osNames j (.only [b]) (DFrac.own 1) h ∗
    (⌜h.cur !! b = none⌝ ∨ ∃ (J : Ino) (hJ : NamesH),
      ⌜h.cur !! b = some (.dir J) ∧ FilesOnly hJ.cur⌝ ∗ osNames J (.except []) (DFrac.own 1) hJ))

end defs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev wal.Exist.specCreate [go_etcd_io.etcd.server.v3.storage.wal.Assumptions] (C : WalEnc.WalCodec)
    (Mr : WalEnc.WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp),
  InArea r dir nm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk C Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
      WalFs.walUnlockedTok }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Exist)) (Val #dir))
  {{ (b : Bool), RET #b; osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm 1 ∗
      WalFs.walUnlockedTok }}

/-- See the file header. -/
abbrev fileutil.CreateDirAll.specTmp [go_etcd_io.etcd.client.pkg.v3.fileutil.Assumptions] : Prop :=
  ∀ (lg : Loc) (R : Roots) (jp : Ino) (d parent name : GoString) (qp : Qp) (h : NamesH),
  d = child parent name → NameOk name → d.length < 2 ^ 60 →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.client.pkg.v3.fileutil ∗
      zapLoggerOk (GF := GF) lg ∗ osInv ∗ osSharedInv R ∗ osPathS R parent (DFrac.own qp) jp ∗
      osCallPerm 1 ∗ tmpDirH jp name h }}
    (App (App (Val (@! go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll)) (Val #lg)) (Val #d))
  {{ (err : GoInterface), RET #err; osPathS R parent (DFrac.own qp) jp ∗ osCallPerm 1 ∗
      ((⌜err ≠ interface.nil⌝ ∗ ∃ h', tmpDirH jp name h') ∨
        (⌜err = interface.nil⌝ ∗ ∃ (h' hJ : NamesH) (J : Ino) (n : Nat),
          ⌜h'.cur !! name = some (.dir J) ∧ h'.next ≤ n ∧ hJ.cur = ∅⌝ ∗
          osNames jp (.only [name]) (DFrac.own 1) h' ∗ osNames J (.except []) (DFrac.own 1) hJ ∗
          osCommitLb n)) }}

/-- See the file header. -/
abbrev os.RemoveAll.specAbsentN [os.Assumptions] : Prop :=
  ∀ (d b : GoString) (j : Ino) (R : Roots) (qd : Qp) (N : NameSet) (dqn : DFrac) (h : NamesH)
    (qc : Qp),
  NameOk b → N.Mem b → h.cur !! b = none →
  {{ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j N dqn h ∗ osCallPerm qc }}
    (App (Val (@! os.RemoveAll)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osNames j N dqn h ∗
      osCallPerm qc ∗ fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
