-- The copy for the part `KvRaft/` of `WalTester/Proof/github_com/mit_pdos/etcd_grove/examples/lib/durable/Defs.lean` (etc/copy-part.py; rerun it, do not edit).
/- Lean-first (no Rocq counterpart).

# `examples/lib/durable` over `fsExt`: its vocabulary (W4c U2, `notes/wal-fsext-w4c-plan.md`)

A durable file `f` (`DFile`: the directory `f.d`, of inode `f.J`, and the base name `f.b`; its
temporary is `f.d/.durable-f.b`, `DFile.tmp`) in the tree's shared mode
(`GooseLang/Ext/Fs/TreeShared.lean`). Its state as a client sees it is `DurSt`: `cur`, what a `Read`
returns now (`none`: no file), and `alt`, while a `Write` is between its rename and the directory's
sync, the value before it (`some old`; `none` otherwise). A crash leaves the file holding `cur` or,
if `alt = some old`, `old` (`durInv_crash`): a `Write`'s rename may or may not survive a crash until
the directory is synced, and the specs say so instead of hiding it (a `Write` is two atomic updates:
the rename, `cur := data, alt := some cur`; the sync, `alt := none`).

The resources:
* `durSt γ s`: the client's half of the state (a ghost variable; the invariant has the other half).
  A client keeps it in its own crash invariant and gives it to the specs through atomic updates (as
  it kept `durableOwnM` with `durableExt`).
* `durInv γ f R`: the crash invariant (namespace `durN`): the other half of the state, half of the
  claims on `f.b` and on the temporary's name, a commit lower bound, half of the resources of every
  inode `f.b` may hold after a crash (`DCand`, its contents synced), and the facts tying them
  (`DurOk`); or, after the crash lemma took it, `crashed` and the crash token.
* `durHandle γ f R`: what a call holds (exclusive; the package's mutex is not what serializes the
  calls in the proof, the handle is): the other halves of the claims and of the current inode's
  resources, the temporary's file whole (if there is one), a fraction of the directory's spine,
  and the physical state's other half.
-/
module

public import KvRaft.GeneratedProof.github_com.mit_pdos.etcd_grove.examples.lib.durable
public import Proof.os.SharedAu
public import Spec.os.OpenFileTruncS
public import Proof.path.filepath.Names

@[expose] public section

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace DurFs

open Iris Iris.BI Iris.ProgramLogic Iris.Std ProofMode Fs

/-! ## Files and names -/

/-- A durable file: its directory's path `d` and inode `J`, its base name `b`. -/
structure DFile where
  d : GoString
  J : Ino
  b : GoString

/-- The file's path. -/
def DFile.name (f : DFile) : GoString := child f.d f.b

/-- The temporary's base name: `.durable-` and the file's. -/
def DFile.tb (f : DFile) : GoString := go!".durable-" ++ f.b

/-- The temporary's path. -/
def DFile.tmp (f : DFile) : GoString := child f.d f.tb

/-- **A file durable can manage**: a clean absolute directory, a clean base name whose temporary's
name is valid too, and paths short enough for `filepath`'s and `os`'s bounds. -/
def DFile.Ok (f : DFile) : Prop :=
  filepath.CleanAbs f.d ∧ path.cleanSeg f.b ∧ path.cleanSeg f.tb ∧ NameOk f.b ∧ NameOk f.tb ∧
    f.d.length + f.tb.length < 2 ^ 40

/-! ## The state -/

/-- **The state of a durable file** as a client sees it: `cur`, its contents now (`none`: no file);
`alt`, while a `Write`'s rename may still be lost to a crash, the contents before it. -/
structure DurSt where
  cur : Option GoString
  alt : Option (Option GoString)

variable [GooseExts] [GoGlobalContext] in
/-- What `Read` returns of the contents `v`. -/
def readRes (v : Option GoString) : val := PairV (#(v.getD [])) (#v.isSome)

instance DurSt.countable : Pos.Countable DurSt :=
  Pos.Countable.ofInjective (fun s => Pos.Countable.encode (s.cur, s.alt))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h; subst h1 h2; rfl)

/-- An inode the file may hold after a crash: its `OsMeta` (size and crash bounds the contents' length)
and contents (every byte durable). -/
structure DCand where
  i : Ino
  m : OsMeta
  v : GoString

/-- A candidate's `OsMeta` says a crash leaves it at its size; its contents fit a Go slice (as
`Write`'s `data`: a `ReadAt` of any length reads them back). -/
def DCand.Ok (c : DCand) : Prop :=
  c.m.size = c.v.length ∧ c.m.lo = c.m.size ∧ c.m.hi = c.m.size ∧ c.v.length < 2 ^ 63

/-- **The physical state**: the claims' histories of the file's name (`hb`) and of the
temporary's (`ht`), a commit lower bound `nc`, the candidates, and the state's `alt` (a copy, so
that the handle knows it: the state is determined by the physical state, `DurOk.alt`). -/
structure DurPhys where
  hb : NamesH
  ht : NamesH
  nc : Nat
  cands : List DCand
  alt : Option (Option GoString)

instance DCand.countable : Pos.Countable DCand :=
  Pos.Countable.ofInjective (fun c => Pos.Countable.encode (c.i, c.m, c.v))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3⟩ := h; subst h1 h2 h3; rfl)

instance DurPhys.countable : Pos.Countable DurPhys :=
  Pos.Countable.ofInjective (fun p => Pos.Countable.encode (p.hb, p.ht, p.nc, p.cands, p.alt))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl)

/-- **What a crash may leave at the file's name** `o` is allowed by the state `s`: nothing if `cur` or
`alt` is no file; a candidate's inode with the contents `cur` or `alt`'s. -/
def OutOk (s : DurSt) (cs : List DCand) : Option Node → Prop
  | none => s.cur = none ∨ s.alt = some none
  | some (.file i) => ∃ c ∈ cs, c.i = i ∧ (s.cur = some c.v ∨ s.alt = some (some c.v))
  | some (.dir _) => False

/-- **No version of the history `h` holds a directory at the name `b`**: neither at boot nor after
any of its logged entries (so neither does what a crash leaves there, `NamesH.valAfter`). -/
def NoDirH (h : NamesH) (b : GoString) : Prop :=
  (∀ J, h.boot !! b ≠ some (.dir J)) ∧ ∀ xe ∈ h.ents, ∀ J, xe.2.2 !! b ≠ some (.dir J)

/-- A new version holding no directory at `b` keeps `NoDirH`. -/
theorem NoDirH.log {h : NamesH} {b : GoString} (hn : NoDirH h b) (x : Nat) (e : LogEntry)
    (E : Ents) (hE : ∀ J, E !! b ≠ some (.dir J)) : NoDirH (h.log x e E) b := by
  refine ⟨hn.1, fun xe hxe J => ?_⟩
  simp only [NamesH.log, List.mem_append, List.mem_singleton] at hxe
  rcases hxe with hxe | rfl
  · exact hn.2 xe hxe J
  · exact hE J

/-- **The invariant's facts** of the file `f`, the state `s`, the physical state `p`: every crash that
keeps the entries below the commit bound leaves the name as `OutOk` allows; the name holds, now,
`cur` (a candidate's inode); the temporary's name holds no directory; with no rename to lose
(`alt = none`), every entry of the name is below the commit bound; the candidates are `Ok`, at
distinct inodes; `alt` is the physical state's copy; no version of the temporary's history holds a
directory (a crash leaves none there, `durInv_crash`). -/
structure DurOk (f : DFile) (s : DurSt) (p : DurPhys) : Prop where
  crash : ∀ K : Nat → Prop, (∀ y e E, (y, e, E) ∈ p.hb.ents → y < p.nc → K y) →
    OutOk s p.cands (p.hb.valAfter f.J K f.b)
  cur : match s.cur with
    | none => p.hb.cur !! f.b = none
    | some v => ∃ c ∈ p.cands, c.v = v ∧ p.hb.cur !! f.b = some (.file c.i)
  tmp : ∀ J, p.ht.cur !! f.tb ≠ some (.dir J)
  synced : s.alt = none → p.hb.next ≤ p.nc
  cands : ∀ c ∈ p.cands, c.Ok
  inj : (p.cands.map DCand.i).Nodup
  alt : s.alt = p.alt
  tmpH : NoDirH p.ht f.tb

/-- **What the file's name holds under the physical state `p`**: no file (`none`), or a candidate's
inode and its contents. -/
def DurPhys.CurIs (f : DFile) (p : DurPhys) (v : Option GoString) : Prop :=
  match p.hb.cur !! f.b with
  | none => v = none
  | some (.file i) => ∃ c ∈ p.cands, c.i = i ∧ v = some c.v
  | some (.dir _) => False

/-! ## Ghost state -/

/-- The ghost names of a durable file. -/
structure DurGS where
  γs : GName
  γp : GName
  γc : GName

/-- The invariant's namespace. -/
def durN : Namespace := nroot .@ "durable"

/-- The mask of durable's atomic updates: `os`'s, without the invariant. -/
def durAuMask : CoPset := osAuMask \ ↑durN

section ghost
variable {GF : BundledGFunctors} [AllG GF]

/-- **The client's half of the state.** -/
def durSt (γ : DurGS) (s : DurSt) : IProp GF := ghostVar γ.γs (1 : Qp).half s

/-- The physical state's halves. -/
def durPhys (γ : DurGS) (p : DurPhys) : IProp GF := ghostVar γ.γp (1 : Qp).half p

/-- The generation's crash token of the file. -/
def durCrashTok (γ : DurGS) : IProp GF := token γ.γc

instance durSt_timeless (γ : DurGS) (s : DurSt) : Timeless (durSt (GF := GF) γ s) := by
  unfold durSt; infer_instance

end ghost

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics fsExt] [FsSemOk] [HasExt fsExt]
  [GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [G : GooseGlobalGS hlc GF] [L : GooseLocalGS GF]

/-- A candidate's resources, with the fraction `dq`. -/
def candRes (c : DCand) (dq : DFrac) : IProp GF :=
  iprop(osMeta (L := L) c.i dq c.m ∗ osBytes (L := L) c.i 0 dq (c.v.map durB))

/-- **The crash invariant's contents**. -/
def durInvBody (γ : DurGS) (f : DFile) : IProp GF :=
  iprop(∃ (s : DurSt) (p : DurPhys),
    ghostVar γ.γs (1 : Qp).half s ∗ durPhys γ p ∗
    osNames (L := L) f.J (.only [f.b]) (DFrac.own (1 : Qp).half) p.hb ∗
    osNames (L := L) f.J (.only [f.tb]) (DFrac.own (1 : Qp).half) p.ht ∗
    osCommitLb (L := L) p.nc ∗ ([∗list] c ∈ p.cands, candRes (L := L) c (DFrac.own (1 : Qp).half)) ∗
    ⌜DurOk f s p⌝)

/-- **The crash invariant of the file `f`** (generation `L`): its contents, or the crash and the
crash token once the crash lemma took them. -/
def durInv (γ : DurGS) (f : DFile) : IProp GF :=
  inv durN iprop(durInvBody (L := L) γ f ∨ (crashed (hC := L.goose_crashGS) ∗ durCrashTok γ))

instance durInv_persistent (γ : DurGS) (f : DFile) : Persistent (durInv (L := L) γ f) := by
  unfold durInv; infer_instance

/-- The temporary's file, whole, if its name holds one (what an `O_TRUNC` open truncates). -/
def tmpRes (f : DFile) (ht : NamesH) : IProp GF :=
  match ht.cur !! f.tb with
  | some (.file i) => trFile (hG := ⟨G, L⟩) i False
  | _ => iprop(emp)

/-- The current inode's other half, if the name holds a file. -/
def curRes (f : DFile) (p : DurPhys) : IProp GF :=
  match p.hb.cur !! f.b with
  | some (.file i) => iprop(∃ c : DCand, ⌜c ∈ p.cands ∧ c.i = i⌝ ∗ candRes (L := L) c (DFrac.own (1 : Qp).half))
  | _ => iprop(emp)

/-- The handle at the physical state `p`. -/
def durHandleP (γ : DurGS) (f : DFile) (R : Roots) (p : DurPhys) : IProp GF :=
  iprop(∃ qd : Qp, durPhys γ p ∗
    osNames (L := L) f.J (.only [f.b]) (DFrac.own (1 : Qp).half) p.hb ∗
    osNames (L := L) f.J (.only [f.tb]) (DFrac.own (1 : Qp).half) p.ht ∗
    curRes (L := L) f p ∗ tmpRes (L := L) f p.ht ∗ osPathS (L := L) R f.d (DFrac.own qd) f.J)

/-- **A call's handle on the file `f`** in the roots `R`: the physical state's other half, the
claims' other halves, the current inode's other half, the temporary's file, a fraction of the
directory's spine. Exclusive (the claims' halves). Between calls no `Write` is between its rename
and its commit (`alt = none`). -/
def durHandle (γ : DurGS) (f : DFile) (R : Roots) : IProp GF :=
  iprop(∃ p : DurPhys, durHandleP γ f R p ∗ ⌜p.alt = none⌝)

/-- The second update of a `Write`: the directory's sync, `alt := none`. It may use the generation's
`notCrashed` (given before the update, returned with its result): the sync is a ghost step after
`Sync` returns, where `Write`'s proof holds the token (`durInv_commit`), and a client whose own
update needs it there (kvraft's `persist`, firing raft's batch *enter*, `readyEnter`, at the sync: a
crash before it may keep the old file) gets it. A client that needs no token gives a plain atomic
update (`durWriteSync_of_au`). (2026-11-22, notes/kvraft-part.md, "`persist`".) -/
abbrev durWriteSync (γ : DurGS) (Ψ : IProp GF) : IProp GF :=
  iprop(notCrashed (hC := L.goose_crashGS) -∗ AU <{ ∃∃ s : DurSt, durSt (GF := GF) γ s }> @ durAuMask, ∅
    <{ durSt (GF := GF) γ ⟨s.cur, none⟩, COMM notCrashed (hC := L.goose_crashGS) ∗ Ψ }>)

/-- An atomic update's postcondition weakened (Rocq Iris's `atomic_update_wand`, absent from the
Lean port: `notes/perennial-changes.md`; as raft's `TracedCap.aupd_wand_post`). -/
theorem durAupd_wand_post {TA TB : Std.Tele} {Eo Ei : CoPset} {α : TA.Arg → IProp GF}
    {β Φ1 Φ2 : TA.Arg → TB.Arg → IProp GF} :
    iprop(atomic_update Eo Ei α β Φ1 ∗ (∀.. x, ∀.. y, Φ1 x y -∗ Φ2 x y)) ⊢ atomic_update Eo Ei α β Φ2 := by
  have h := aupd_intro (P := iprop(True))
    (Q := iprop(atomic_update Eo Ei α β Φ1 ∗ (∀.. x, ∀.. y, Φ1 x y -∗ Φ2 x y))) (α := α) (β := β)
    (Φ := Φ2) (Eo := Eo) (Ei := Ei) (by
      iintro ⟨-, ⟨HAU, HW⟩⟩
      ihave Hacc : atomic_acc Eo Ei α (atomic_update Eo Ei α β Φ1) β Φ1 $$ [HAU]
      · iapply aupd_aacc; iexact HAU
      iapply atomic_acc_wand $$ [HW] Hacc
      isplit
      · iintro HAU'; iframe
      · iexact HW)
  iintro H
  iapply h
  isplit
  · ipureintro; trivial
  · iexact H

/-- **A plain sync update is one** (`durWriteSync`, the token passed through). -/
theorem durWriteSync_of_au (γ : DurGS) (Ψ : IProp GF) :
    iprop(AU <{ ∃∃ s : DurSt, durSt (GF := GF) γ s }> @ durAuMask, ∅
      <{ durSt (GF := GF) γ ⟨s.cur, none⟩, COMM Ψ }>) ⊢ durWriteSync (L := L) γ Ψ := by
  iintro HAU Hnc
  iapply durAupd_wand_post
  iframe HAU
  isimp only [tforall_cons, tforall_nil, Std.Tele.app, ULift.down]
  iintro %_ HΨ
  iframe

/-- The first update of a `Write` of `data`: the rename, `cur := data, alt := some cur`; then the
second (`durWriteSync`). -/
abbrev durWriteAU (γ : DurGS) (data : GoString) (Ψ : IProp GF) : IProp GF :=
  iprop(AU <{ ∃∃ s : DurSt, durSt (GF := GF) γ s }> @ durAuMask, ∅
    <{ durSt (GF := GF) γ ⟨some data, some s.cur⟩, COMM durWriteSync γ Ψ }>)

/-- **What a `Write` of `data` still owes its client** at the handle's physical state `p`: both
updates (no rename yet: `alt = none`), or the second (a rename done: `alt ≠ none`, the name holding
`data`). -/
def durWOwe (γ : DurGS) (f : DFile) (data : GoString) (p : DurPhys) (Ψ : IProp GF) : IProp GF :=
  iprop((⌜p.alt = none⌝ ∗ durWriteAU γ data Ψ) ∨
    (⌜p.alt ≠ none ∧ p.CurIs f (some data)⌝ ∗ durWriteSync γ Ψ))

end res

end DurFs
end EtcdGrove
end Perennial
