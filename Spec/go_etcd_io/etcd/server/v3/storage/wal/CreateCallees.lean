/-
The callee specs `wal.Create`'s proof takes as hypotheses that no other spec states yet (W4 of
`notes/wal-fsext-plan.md`, eleventh session). Each is a triple of the real code, stated for
`Create`'s use; none is proved yet (the W4 log says what each needs).

* **`tmpAny j b h`** (`tmpCls`): the whole claim on the name `b` of `j` (its history `h`), `b` holding
  anything, and the whole claims of every directory under it, among which no cycle (`SubCover`,
  `ClRanked`): what `Create` keeps of its temporary directory `nm.tmp` (a crash's leftover, `walAreaRes`),
  what `os.RemoveAll.specSubS` takes and gives back. (Until 2026-11-22 `tmpDirH`, a directory of files
  only, which needed the boot premise `BootFoNmTmp`: ledger 2026-11-22.)
* **`wal.Exist.specCreate`** (W12 states `Exist` over `walDirIs`): `Exist(dir)` with `Create`'s
  resources, unchanged (and `NameOk nm`, which `ReadDir`'s specs need of the name it reads; `walNameOk`
  allows a NUL byte); on `false`, the name free in the area (`walAreaResFree`: in the program's claim,
  nothing there, not registered), what `Create` starts from whatever its client's view of `dir`
  (`notes/wal-units/fresh.md`; until then `Create` read the absence off a `walAbsent` update). Proved:
  `wal.Exist.wp_specCreate`.
* (`fileutil.CreateDirAll.specTmp`, `CreateDirAll` of a `name` holding a directory of files, was here
  until 2026-11-22: under `wal.Create.spec`'s no-failure premise on `dir.tmp` and the area, `Create` calls
  `CreateDirAll` only on an absent `nm.tmp`, `CreateDirAll.spec`; ledger 2026-11-22.)
* **`os.RemoveAll.specAbsentN`**: `os.RemoveAll.specAbsentS` (proved) for a fraction of a claim on any
  names holding `b` (the proved one takes `.only [b]`; the extension's leaf steps,
  `wp_osUnlinkS_none`/`wp_osRmdirS_none`, take `.only [b]`, and the absent case logs nothing, so
  their generalization to `N ∋ b` is the proof). `renameWAL`'s `RemoveAll(dir)` and `Create`'s
  deferred `RemoveAll(dir.tmp)` after the rename hold half of the creating claim `.only [nm, nm.tmp]`.
Lean-first.
-/
module

public import Spec.go_etcd_io.etcd.client.pkg.v3.fileutil.CreateDirAll
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.PkgInit
public import Proof.go_etcd_io.etcd.server.v3.storage.wal.CreateFree
public import GeneratedProof.go_etcd_io.etcd.server.v3.storage.wal

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI
open Fs WalEnc WalFs

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext] [go.BasicIntoValInj]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF] [W : WalGS GF]
variable [sem : go.Semantics]

/-- See the file header. -/
abbrev wal.Exist.specCreate [go_etcd_io.etcd.server.v3.storage.wal.Assumptions] (C : WalEnc.WalCodec)
    (Mr : WalEnc.WalMarshal) : Prop :=
  ∀ (R : Roots) (jr : Ino) (r dir nm : GoString) (qp : Qp),
  InArea r dir nm → NameOk nm →
  {{ isPkgInit (PROP := IProp GF) pkg_id.go_etcd_io.etcd.server.v3.storage.wal ∗
      WalFs.walAreaOk C Mr R jr r ∗ osPathS R r (DFrac.own qp) jr ∗ walAreaRes jr ∗ osCallPerm (callKey R r) 1 ∗
      WalFs.walUnlockedTok }}
    (App (Val (@! go_etcd_io.etcd.server.v3.storage.wal.Exist)) (Val #dir))
  {{ (b : Bool), RET #b; osPathS R r (DFrac.own qp) jr ∗
      ((⌜b = true⌝ ∗ walAreaRes jr) ∨ (⌜b = false⌝ ∗ WalFs.walAreaResFree jr nm)) ∗ osCallPerm (callKey R r) 1 ∗
      WalFs.walUnlockedTok }}

/-- **What `Create` holds under its temporary name, whatever it is** (`walAreaRes`'s claims tagged
with `nm.tmp`): the whole claims `ct` of every directory under the entry `e` (`SubCover`), with no cycle
among them (`ClRanked`): what `os.RemoveAll.specSubS` takes. -/
def tmpCls (e : Option Node) : IProp GF :=
  iprop(∃ ct : List Claim, osClaimsW ct ∗ ⌜SubCover ct e ∧ ClRanked ct⌝)

/-- **The whole of the name `b` of `j` (its claim's history `h`), and of everything under it** (what a
crash may have left at `Create`'s `nm.tmp`). -/
def tmpAny (j : Ino) (b : GoString) (h : NamesH) : IProp GF :=
  iprop(osNames j (.only [b]) (DFrac.own 1) h ∗ tmpCls (h.cur !! b))

/-- See the file header. -/
abbrev os.RemoveAll.specAbsentN [os.Assumptions] : Prop :=
  ∀ (d b : GoString) (j : Ino) (R : Roots) (qd : Qp) (N : NameSet) (dqn : DFrac) (h : NamesH)
    (qc : Qp),
  NameOk b → N.Mem b → h.cur !! b = none →
  {{ isPkgInit (PROP := IProp GF) pkg_id.os ∗ osInv (GF := GF) ∗ osSharedInv R ∗ osPathS R d (DFrac.own qd) j ∗
      osNames j N dqn h ∗ osCallPerm (callKey R d) qc }}
    (App (Val (@! os.RemoveAll)) (Val #(child d b)))
  {{ (err : GoInterface), RET #err; osPathS R d (DFrac.own qd) j ∗ osNames j N dqn h ∗
      osCallPerm (callKey R d) qc ∗ fmtErrorOkOrNil err }}

end spec

end EtcdGrove
end Perennial
