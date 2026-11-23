/- Lean-first (no Rocq counterpart).

# The etcd examples' extensions over the network: `[idIssueExt, fsExt, netExt]` (2026-11-23)

`etcdFsExts` (`FsExts.lean`: the request ids' issue record and the Linux file extension at `etcdFsSem`) with the
net extension: the extensions of an etcd program on a machine of a distributed deployment (`putget_safe`,
`notes/putget-dist-plan.md`; the plan's option (i) bundle, `notes/etcd-dist-plan.md` §9), and of a
single-process etcd program that listens (`single-process-restore`). Each extension's semantics and ghost
state is its own (the file extension's at `etcdFsSem`); the `HasExt` instances by computation; and the
interpretations' conditions on the initial states, from the network's start and each machine's `FsInit`
(`etcdNetExts_initP`: `etcdFsSem`, `Fs.fsSemWithS`, keeps `ExtSemantics`'s default `initLocal`, so `FsInit` is
the statement's to give).
-/
module

public import Robustness.Statement
public import Perennial.GooseLang.InitAdequacy
public import GooseLang.Ext.Net.Ghost
public import GooseLang.Ext.IdIssue.Specs
public import Proof.github_com.mit_pdos.etcd_grove.examples.lib.etcdstart.FsExts

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProgramLogic Iris.Std

/-! ## The extensions -/

/-- **The etcd examples' extensions over the network**: the request ids' issue record (`idutil`'s generator: the member's),
the Linux file extension (the member's WAL, backend and snapshots; every machine's `fileutil`
initializer) and the net extension (the member's listener, the client's connection): the etcd
examples' `etcdFsExts` with the net extension (`notes/etcd-dist-plan.md`, D2's `net` half, option (i)). -/
@[reducible] def etcdNetExts : GooseExts := ⟨[idIssueExt, Fs.fsExt, Net.netExt]⟩

attribute [local instance] etcdNetExts

/-- Their semantics: the issue record's, the file extension's restricted by `etcdSQ` (`etcdFsSem`: no
file system call fails; `examples/lib/etcdstart/FsExts.lean`), the net extension's (every fault it
allows: bytes delayed, a direction cut at any read or write, a dial refused). -/
@[reducible] def etcdNetExtsSemantics : GooseSemantics :=
  ⟨(idIssue_semantics, etcdFsSem, Net.net_semantics, ⟨⟩)⟩

/-- Their ghost state: each extension's own. -/
@[reducible] def etcdNetExtsInterp : GooseInterp := ⟨(idIssue_interp, Fs.fs_interp, Net.net_interp, ⟨⟩)⟩

attribute [local instance] etcdNetExtsSemantics etcdNetExtsInterp etcdFsSem

set_option linter.defProp false in
/-- The programs have the issue record (by computation). -/
@[reducible] def etcdNetExts_hasIdIssue : HasExt idIssueExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
/-- The programs have the Linux file extension, at `etcdFsSem` (by computation). -/
@[reducible] def etcdNetExts_hasFs : letI := etcdFsSem; HasExt Fs.fsExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl

set_option linter.defProp false in
/-- The programs have the net extension (by computation). -/
@[reducible] def etcdNetExts_hasNet : HasExt Net.netExt where
  registered := rfl
  sem_eq := rfl
  interp_eq := rfl


attribute [local instance] etcdNetExts_hasIdIssue etcdNetExts_hasFs etcdNetExts_hasNet

/-- **The interpretations' conditions on the machines' initial states**, for `etcdNetExts`: the network's
from `Robust`'s `extsInitGlobal` (no connection), each machine's files from `FsInit` (the issue record's
are `True`). -/
theorem etcdNetExts_initP (g : GlobalState) (nodes : List (Expr × state))
    (Hfs : ∀ m, m ∈ nodes → Fs.FsInit (extLocal Fs.fsExt m.2.world)) :
    extsInitGlobal g → (∀ m, m ∈ nodes → extsInitLocal m.2 g) →
      extsInitgP g.globalWorld ∧ ∀ m, m ∈ nodes → extsInitP m.2.world g.globalWorld :=
  fun hg _ => ⟨⟨trivial, trivial, hg.2.2.1, trivial⟩, fun m hm => ⟨trivial, Hfs m hm, trivial, trivial⟩⟩

open Iris.ProofMode in
/-- **The file extension's start resources on a machine of `etcdNetExts`** (`etcdFs_start`'s, without the
files): from the machine's local start resources, the invariant of the mapped cells and the tree's whole
history (what `wp_walAreas` takes; the net extension's, the listeners, are not taken). -/
theorem etcdNetFs_start [GoGlobalContext] {GF : BundledGFunctors} [hG : HeapGS .hasLC GF] (σ : state) :
    ⊢ extsLocalStart (GF := GF) σ.world ={⊤}=∗
      Fs.osInv (L := hG.goose_localGS) ∗
      Fs.osTree (L := hG.goose_localGS) (DFrac.own 1) (extLocal Fs.fsExt σ.world).fs.roots
        ((extLocal Fs.fsExt σ.world).fs.treeDur, []) := by
  haveI : Fs.FsSemOk := etcdFsSemOk
  have Hl : extsLocalStart (GF := GF) σ.world ⊢
      Fs.osStart (Fs.gooseOsGS (L := hG.goose_localGS)) (extLocal Fs.fsExt σ.world) :=
    (sep_elim_right (P := iprop(True))).trans sep_elim_left
  iintro Hs
  icases Hl $$ Hs with Hs
  unfold Fs.osStart Fs.osStartF Fs.treeStart
  icases Hs with ⟨⟨-, -, Hv⟩, Hd⟩
  imod Fs.osInv_alloc (L := hG.goose_localGS) ⊤ $$ Hv with #Hinv
  imodintro
  iframe Hinv
  unfold Fs.osTree; iexact Hd

end EtcdGrove
end Perennial

end
