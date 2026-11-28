/-
(hraft_robust R3) The disk's crash invariant and lock invariant (`dir/raft`, `*Disk`), as R3's `DISKCRASH.md`
designs them.

* `DiskGen`: a generation's names (durable's, the client views' halves `γl`/`γs`, the window record `γw`
  shared by the crash invariant and the lock invariant, the crash token `γk`).
* `diskInv g Wl Ws Wf` (namespace `diskN`, inside `storeN` and `durAuMask`): `durable`'s client state and the
  window record's half, and, until the crash lemma takes them with `γk`, the client views' other halves at
  the record's image, which is `Ok`, and the window's facts: idle (the file holds the image), open (a write's
  rename done and not yet committed to the client: the file holds the new image, the old one may survive a
  crash, and the client's window resource `winOf Wl Ws op` is held), fresh (the first start's `Fresh`, before
  its write is synced: the client's `Wf`). (`durSt` and the record are outside the crashed side, as kvraft's
  `kdFileBody`: the rename's atomic update, which has no crash token, moves them on either side.)
* `diskLockInv g d` (`d.mu`): `d`'s memory at the record's image, idle, durable's handle and a call permission.
* `isDisk g d Wl Ws Wf`: the persistent handle.
-/
module

public import Dsverify.Proof.github_com.hashicorp.raft.examples.hraftnet.disk.Img
public import Dsverify.Proof.github_com.mit_pdos.etcd_grove.examples.lib.durable.Defs

@[expose] public section

noncomputable section

namespace Perennial

namespace github_com.hashicorp.raft.examples.hraftnet.disk

open Iris Iris.BI Iris.ProofMode github_com.hashicorp.raft proto EtcdGrove

/-! ## The abstract state and the writes -/

/-- The two stores' state, as `dir/raft` holds it, plus the volatile `staged`. -/
structure DiskAbs where
  L : LogAbs
  S : StableAbs

/-- A write of `dir/raft`: a log write or a stable write. -/
inductive DiskOp
  | log (o : LogOp)
  | stab (o : StableOp)

/-- The state after the write `op` (the contracts' updates; `del`'s `hi'` the largest index left). -/
def DiskOp.apply : DiskOp → DiskAbs → DiskAbs
  | .log (.store first es), D => { D with L := D.L.store first es }
  | .log (.del _ mn mx), D => { D with L := D.L.delete mn mx (maxKey (LogAbs.del D.L.m mn mx)) }
  | .stab (.setU k v), D => { D with S := { D.S with ints := D.S.ints.insert k v } }
  | .stab (.set k vb), D => { D with S := { D.S with bytes := D.S.bytes.insert k vb } }

/-- What a restart reads: `staged` is volatile. -/
def DiskAbs.crash (D : DiskAbs) : DiskAbs := { D with L := { D.L with staged := W64 0 } }

/-- The abstract state of the image `I` with `stg` staged. -/
def DiskAbs.of (I : DiskImg) (stg : w64) : DiskAbs := ⟨I.absL stg, I.absS⟩

/-- The abstract state a restart reads from the image `I`. -/
def absImg (I : DiskImg) : DiskAbs := DiskAbs.of I (W64 0)

/-- **`v` (what `durable.Read` returns) decodes to the state `D`** (`staged = 0`). -/
def imgHolds (v : Option GoString) (D : DiskAbs) : Prop :=
  ∃ I : DiskImg, I.Ok ∧ v = some (encImg I) ∧ absImg I = D.crash

theorem crash_of (I : DiskImg) (stg : w64) : (DiskAbs.of I stg).crash = absImg I := rfl

/-- The window: idle; a write `op` to the image `I'` between its rename and its commit (`sy`: its directory
synced); the first start's `Fresh` before its write is synced (`r`: its rename done, the file holds the
record's image). -/
inductive DiskWin
  | idle
  | open (op : DiskOp) (I' : DiskImg) (sy : Bool)
  | fresh (r : Bool)

/-! ## Countable encodings (for the ghost variables) -/

instance dent_countable : Pos.Countable DEnt :=
  Pos.Countable.ofInjective (fun e => Pos.Countable.encode (e.idx, e.term, e.ty, e.data, e.ext))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h; subst h1 h2 h3 h4 h5; rfl)

instance diskImg_countable : Pos.Countable DiskImg :=
  Pos.Countable.ofInjective (fun I => Pos.Countable.encode (I.ents, I.kv, I.ikv, I.commit))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a; cases b; simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h; subst h1 h2 h3 h4; rfl)

def logOpEnc : LogOp → (Nat × RLog) ⊕ (Bool × Nat × Nat)
  | .store f es => .inl (f, es)
  | .del t a b => .inr (t, a, b)

def stableOpEnc : StableOp → (List w8 × w64) ⊕ (List w8 × List w8)
  | .setU k v => .inl (k, v)
  | .set k v => .inr (k, v)

def diskOpEnc : DiskOp → ((Nat × RLog) ⊕ (Bool × Nat × Nat)) ⊕ ((List w8 × w64) ⊕ (List w8 × List w8))
  | .log o => .inl (logOpEnc o)
  | .stab o => .inr (stableOpEnc o)

def diskWinEnc : DiskWin → Option (Bool ⊕ ((((Nat × RLog) ⊕ (Bool × Nat × Nat)) ⊕ ((List w8 × w64) ⊕ (List w8 × List w8))) × DiskImg × Bool))
  | .idle => none
  | .fresh r => some (.inl r)
  | .open op I sy => some (.inr (diskOpEnc op, I, sy))

theorem diskOpEnc_inj (a b : DiskOp) (h : diskOpEnc a = diskOpEnc b) : a = b := by
  cases a with
  | log o => cases b with
    | log o' => cases o <;> cases o' <;> simp_all [diskOpEnc, logOpEnc]
    | stab o' => simp [diskOpEnc] at h
  | stab o => cases b with
    | log o' => simp [diskOpEnc] at h
    | stab o' => cases o <;> cases o' <;> simp_all [diskOpEnc, stableOpEnc]

instance diskWin_countable : Pos.Countable DiskWin :=
  Pos.Countable.ofInjective (fun w => Pos.Countable.encode (diskWinEnc w))
    (fun a b h => by
      have h := Pos.encode_inj h
      cases a <;> cases b <;> simp only [diskWinEnc, Option.some.injEq, Prod.mk.injEq, reduceCtorEq,
        Sum.inl.injEq, Sum.inr.injEq] at h
      all_goals first | rfl | (subst h; rfl) | (obtain ⟨h1, h2, h3⟩ := h; rw [diskOpEnc_inj _ _ h1, h2, h3]))

/-! ## Names -/

/-- **A generation's names** (see the file header). -/
structure DiskGen where
  γd : DurFs.DurGS
  f : DurFs.DFile
  R : Fs.Roots
  γl : GName
  γs : GName
  γw : GName
  γk : GName

/-- **The disk's invariant's namespace.** -/
def diskN : Namespace := storeN .@ "disk"

theorem diskN_sub_storeN : (↑diskN : CoPset) ⊆ ↑storeN := nclose_subseteq _ _

set_option maxRecDepth 100000 in
/-- The invariant is open inside `durable`'s atomic updates. -/
theorem diskN_sub_durAu : (↑diskN : CoPset) ⊆ DurFs.durAuMask := by
  intro x hx
  have h1 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "osfs" (by decide)) x hx
  have h2 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "osfsShared" (by decide)) x hx
  have h3 := nclose_subseteq' _ (mask_ndot_ne' nroot "hraftstore" "durable" (by decide)) x hx
  rw [Std.LawfulSet.mem_diff] at h1 h2 h3
  unfold DurFs.durAuMask Fs.osAuMask
  rw [Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff, Std.LawfulSet.mem_diff]
  exact ⟨⟨⟨CoPset.mem_full, h1.2⟩, h2.2⟩, h3.2⟩

/-- `diskN` is outside `durable`'s namespace. -/
theorem diskN_not_durN (x : Pos) (hx : x ∈ (↑diskN : CoPset)) : x ∉ (↑DurFs.durN : CoPset) := by
  have := diskN_sub_durAu x hx
  unfold DurFs.durAuMask at this
  rw [Std.LawfulSet.mem_diff] at this
  exact this.2

section res
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : github_com.hashicorp.raft.examples.hraftnet.disk.Assumptions]

/-- **The log store's view** (`isLogStore`'s `own`). -/
def diskOwnL (g : DiskGen) (A : LogAbs) : IProp GF := ghostVar g.γl (1 : Qp).half A

/-- **The stable store's view** (`isStableStore`'s `own`). -/
def diskOwnS (g : DiskGen) (S : StableAbs) : IProp GF := ghostVar g.γs (1 : Qp).half S

/-- The window resource the write `op` holds: the client's families. -/
def winOf (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) : DiskOp → IProp GF
  | .log o => Wl o
  | .stab o => Ws o

/-- The window record's value. -/
abbrev DiskRec : Type := DiskImg × w64 × DiskWin

/-- **The window's facts and resources** (see the file header). -/
def diskWinRes (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) (I : DiskImg) (stg : w64)
    (s : DurFs.DurSt) : DiskWin → IProp GF
  | .idle => iprop(⌜s = ⟨some (encImg I), none⟩⌝)
  | .open op I' sy => iprop(⌜I'.Ok ∧ DiskAbs.of I' stg = op.apply (DiskAbs.of I stg) ∧ s.cur = some (encImg I') ∧
      (s.alt = none ∨ (sy = false ∧ s.alt = some (some (encImg I))))⌝ ∗ winOf Wl Ws op)
  | .fresh r => iprop(Wf ∗ ⌜r = true → s.cur = some (encImg I)⌝)

/-- **The invariant's contents** (see the file header). -/
def diskBody (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) : IProp GF :=
  iprop(∃ (I : DiskImg) (stg : w64) (w : DiskWin) (s : DurFs.DurSt),
    DurFs.durSt g.γd s ∗ ghostVar g.γw (1 : Qp).half ((I, stg, w) : DiskRec) ∗
    ((ghostVar g.γl (1 : Qp).half (I.absL stg) ∗ ghostVar g.γs (1 : Qp).half I.absS ∗ ⌜I.Ok⌝ ∗
        diskWinRes Wl Ws Wf I stg s w) ∨
      crashed ∗ token g.γk))

/-- **The disk's crash invariant.** -/
def diskInv (g : DiskGen) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) : IProp GF :=
  inv diskN (diskBody g Wl Ws Wf)

instance diskInv_persistent g Wl Ws Wf : Persistent (diskInv (GF := GF) g Wl Ws Wf) := by
  unfold diskInv; infer_instance

/-- **The lock invariant** of `d.mu`. -/
def diskLockInv (g : DiskGen) (d : Loc) : IProp GF :=
  iprop(∃ (I : DiskImg) (stg : w64) (qc : Qp),
    diskMem d I stg ∗ ghostVar g.γw (1 : Qp).half ((I, stg, DiskWin.idle) : DiskRec) ∗ ⌜I.Ok⌝ ∗
    DurFs.durHandle g.γd g.f g.R ∗ Fs.osCallPerm (Fs.callKey g.R g.f.d) qc)

/-- **The handle on `*Disk` `d`** of the generation `g`, with the client's window families. -/
def isDisk (g : DiskGen) (d : Loc) (Wl : LogOp → IProp GF) (Ws : StableOp → IProp GF) (Wf : IProp GF) :
    IProp GF :=
  iprop(∃ mu : Loc,
    isPkgInit (PROP := IProp GF) pkg_id.github_com.hashicorp.raft.examples.hraftnet.disk ∗
    d.[Disk, go!"mu"] ↦□ mu ∗ sync.isMutex mu (diskLockInv g d) ∗ d.[Disk, go!"file"] ↦□ g.f.name ∗
    diskInv g Wl Ws Wf ∗ DurFs.durInv g.γd g.f ∗ Fs.osInv ∗ Fs.osSharedInv g.R ∗ ⌜g.f.Ok⌝)

instance isDisk_persistent g d Wl Ws Wf : Persistent (isDisk (GF := GF) g d Wl Ws Wf) := by
  unfold isDisk; infer_instance

end res

end github_com.hashicorp.raft.examples.hraftnet.disk

end Perennial
