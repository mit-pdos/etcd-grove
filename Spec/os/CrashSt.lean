/-
Crash-aware specs of the `os`, `syscall` and `golang.org/x/sys/unix` calls minibolt makes on its
database file, over the generic crash invariant (`csInv N P R γ Good Ok`, `Proof/os/CrashSt.lean`:
the file at the path `P` in the roots `R`, and half of the tree's history): the caller holds its
part of the file (`csOwnF γ s`; with its half of the history, `csOwn P R γ s V`, for the open) and
shows `Ok` of each state the call passes through. Proved in `Proof/os/CrashStSpec.lean`.
Lean-first (no Rocq counterpart).

* `os.OpenFile.specCrashS`: `P = d/b`, `d` a directory; absent or idle, to `csOpenSt` of it
  (created, its `create` logged, if absent); on failure maybe.
* `os.File.WriteAt.specCrashS`: idle, the write starting inside the file, to an idle state the
  loop reached (`WReach C`: each attempt writes a prefix of the rest of the data, of a length the
  semantics allows, `PwCut C`, from the `nn` bytes a short write left written), with the data written on success. The caller shows `Ok` of
  every state the loop may pass through: each `WReach` state idle, and with the next attempt in
  flight. The write misses the frozen bytes, and the mapped cells of its range are passed through
  (`mcellsAny`).
* `os.File.Truncate.specCrashS`: idle, growing: to grown (`csGrownOwn`: by bytes `zs`, zeros if the
  file's `OsMeta` says so), or on failure maybe not (`ftFail`); `Ok` of each `TReach` state, idle
  and with a truncate in flight.
* `syscall.Fdatasync.specCrashS` and `os.File.Sync.specCrashS`: idle `H ++ (F ++ T)` (`F` the
  frozen bytes) to `csSynced hd` (the bytes after the frozen ones synced, keeping the ones before
  them, shown clean, among the durable bytes known; or, `hd`, the ones before them), which the
  caller shows `Ok`; on failure `ok` is lost.
* `golang_org.x.sys.unix.Mmap.specCrashS`/`Munmap.specCrashS`: the mappings change.
-/
module

public import Proof.os.CrashStOps
public import Spec.golang_org.x.sys.unix.Mmap
public import Spec.golang_org.x.sys.unix.Munmap

@[expose] public section

noncomputable section

namespace Perennial

open Fs

/-- The states a `WriteAt` of `data` at `off` reaches from `m`, `bs`, `nn` of the data's bytes
written: each attempt writes a prefix of the rest of the data (from `off + nn`) of a length `k` the
semantics allows (`C (off + nn) len k` of an attempt of `len` bytes: `PwCut C`), and a short write
that wrote `k > 0` bytes moves `nn` on by `k`. -/
inductive WReach (C : Nat → Nat → Nat → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (off : Nat)
    (data : List w8) : Nat → OsMeta → List (w8 × Bool) → Prop
  | refl : WReach C m bs off data 0 m bs
  | step {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)} (k nn' : Nat) :
      WReach C m bs off data nn m' bs' → nn < data.length → k ≤ data.length - nn →
      ((data.drop nn).length < 2 ^ 64 → C (off + nn) (data.drop nn).length k) →
      (nn' = nn ∨ nn' = nn + k) →
      WReach C m bs off data nn'
        (finMeta m' (off + nn) (data.drop nn) k) (finBytes m' bs' (off + nn) (data.drop nn) k)

theorem WReach.narrow {C : Nat → Nat → Nat → Prop} {m : OsMeta} {bs : List (w8 × Bool)} {off : Nat}
    {data : List w8} {nn : Nat} {m' : OsMeta} {bs' : List (w8 × Bool)}
    (h : WReach C m bs off data nn m' bs')
    (hl : bs.length = m.size) (hoff : off ≤ m.size) : Narrow m bs off data m' bs' := by
  induction h with
  | refl => exact narrow_refl off data hl
  | step k nn' _ hnn hk _ _ ih =>
    exact narrow_fin ih hoff _ (Nat.le_of_lt hnn) (by rw [List.length_drop]; exact hk)

/-- The states a growing `Truncate` to `sz` reaches from `m`, `bs`: unchanged, the size bound
widened and the versions known forgotten (a failed attempt), grown (by bytes `zs`, zeros if the file's `OsMeta` says so). -/
inductive TReach (m : OsMeta) (bs : List (w8 × Bool)) (sz : Nat) :
    OsMeta → List (w8 × Bool) → Prop
  | refl : TReach m bs sz m bs
  | ft : TReach m bs sz (ftFail m sz) bs
  | grown (zs : List w8) : zs.length = sz - m.size →
      (m.zero = true → zs = List.replicate (sz - m.size) 0) →
      TReach m bs sz (m.grown sz) (bs ++ zs.map (·, false))

namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.OpenFile.specCrashS : Prop :=
  ∀ (d b : GoString) (perm : w32) (N : Namespace) (R : Roots) (V : Hist) (j : Ino) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (s : CState),
  NameOk b → lookupH R V d = some (.dir j) →
  (s = none ∨ ∃ i m bs fa fb, s = some (i, ⟨m, bs, fa, fb, .idle⟩)) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (s = none → ∀ i, Ok (csNew i)) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N (child d b) R γ Good Ok ∗
      csOwn (GF := GF) (child d b) R γ s V }}
    (App (App (App (Val (@! os.OpenFile)) (Val #(child d b))) (Val #(W64 0x42))) (Val #perm))
  {{ (f : Loc) (err : GoInterface), RET (PairV #f #err);
      (∃ (fd : w64) (i : Ino), ⌜err = interface.nil ∧ 0 ≤ fd.toInt ∧ (s = none ∨ sIno s = some i)⌝ ∗
          os.ownFile f fd (child d b) (DFrac.own 1) ∗ osFd fd (DFrac.own 1) ⟨i, true, true⟩ ∗
          csOwn (child d b) R γ (csOpenSt j b V i s).1 (csOpenSt j b V i s).2) ∨
      (⌜err ≠ interface.nil ∧ f = null⌝ ∗ (csOwn (child d b) R γ s V ∨
          ∃ i : Ino, csOwn (child d b) R γ (csOpenSt j b V i s).1 (csOpenSt j b V i s).2)) }}

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.File.WriteAt.specCrashS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice) (data : List w8)
    (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (P : GoString) (R : Roots)
    (γ : GName) (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta)
    (bs : List (w8 × Bool)) (fa fb : Nat) (C : Nat → Nat → Nat → Prop), PwCut C →
  d.writable = true → 0 ≤ off.toInt → off.toNat ≤ m.size → off.toNat + data.length < 2 ^ 63 →
  0 < data.length → data.length ≤ 0x40000000 →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → (off.toNat + data.length ≤ fa ∨ fb ≤ off.toNat) →
  (∀ nn m' bs', WReach C m bs off.toNat data nn m' bs' →
    Ok (some (d.ino, ⟨m', bs', fa, fb, .idle⟩)) ∧ (nn < data.length → ∀ t,
      Ok (some (d.ino, ⟨m', bs', fa, fb, .write t (off.toNat + nn) (data.drop nn)⟩)))) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      csOwnF (GF := GF) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)) ∗
      mcellsAny (GF := GF) m.maps off.toNat (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      mcellsAny m.maps off.toNat (off.toNat + data.length) ∗
      ∃ (nn : Nat) (m' : OsMeta) (bs' : List (w8 × Bool)),
        ⌜WReach C m bs off.toNat data nn m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ off.toNat + data.length ≤ m'.size ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil))⌝ ∗
        csOwnF γ (some (d.ino, ⟨m', bs', fa, fb, .idle⟩)) }}

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.File.Truncate.specCrashS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64) (dq : DFrac) (d : OsFd)
    (N : Namespace) (P : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop)
    (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool)) (fa fb hi : Nat),
  0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat → MapsBelow m.maps hi →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ m' bs', TReach m bs sz.toNat m' bs' →
    Ok (some (d.ino, ⟨m', bs', fa, fb, .idle⟩)) ∧
      ∀ t, Ok (some (d.ino, ⟨m', bs', fa, fb, .trunc t sz.toNat⟩))) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnF (GF := GF) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)) ∗
      mcellsAny (GF := GF) m.maps m.size hi }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ csGrownOwn d.ino γ m bs fa fb sz.toNat hi) ∨
       (⌜err ≠ interface.nil⌝ ∗
         (csGrownOwn d.ino γ m bs fa fb sz.toNat hi ∨
          (csOwnF γ (some (d.ino, ⟨ftFail m sz.toNat, bs, fa, fb, .idle⟩)) ∗
            mcellsAny m.maps m.size hi)))) }}

variable [os.Assumptions] in
/-- See the file header. -/
abbrev os.File.Sync.specCrashS : Prop :=
  ∀ (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd) (N : Namespace)
    (P : GoString) (R : Roots) (γ : GName) (Good : Option OsFile → Prop) (Ok : CState → Prop)
    (m : OsMeta) (H F T : List (w8 × Bool)) (fa fb : Nat) (hd : Bool),
  H.length = fa → fa + F.length = fb → (hd = false → ∀ y ∈ H, y.2 = true) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok (some (d.ino, csSynced hd m H F T fa fb)) →
  Ok (some (d.ino, ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩)) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good Ok ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗
      csOwnF (GF := GF) γ (some (d.ino, ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ csOwnF γ (some (d.ino, csSynced hd m H F T fa fb))) ∨
       (⌜err ≠ interface.nil⌝ ∗
         csOwnF γ (some (d.ino, ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩)))) }}

variable [syscall.Assumptions] in
/-- See the file header. -/
abbrev syscall.Fdatasync.specCrashS : Prop :=
  ∀ (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta) (H F T : List (w8 × Bool))
    (fa fb : Nat) (hd : Bool),
  H.length = fa → fa + F.length = fb → (hd = false → ∀ y ∈ H, y.2 = true) →
  ↑osN ⊆ (⊤ : CoPset) \ ↑N → Ok (some (d.ino, csSynced hd m H F T fa fb)) →
  Ok (some (d.ino, ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩)) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good Ok ∗ osFd (GF := GF) fd dq d ∗
      csOwnF (GF := GF) γ (some (d.ino, ⟨m, H ++ (F ++ T), fa, fb, .idle⟩)) }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ csOwnF γ (some (d.ino, csSynced hd m H F T fa fb))) ∨
       (⌜e ≠ 0⌝ ∗
         csOwnF γ (some (d.ino, ⟨{ m with ok := false }, H ++ (F ++ T), fa, fb, .idle⟩)))) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- See the file header. -/
abbrev golang_org.x.sys.unix.Mmap.specCrashS : Prop :=
  ∀ (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (P : GoString) (R : Roots)
    (γ : GName) (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta)
    (bs : List (w8 × Bool)) (fa fb : Nat),
  d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ base : Loc,
    Ok (some (d.ino, ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩))) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good Ok ∗ osFd (GF := GF) fd dq d ∗
      csOwnF (GF := GF) γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)) }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          csOwnF γ
            (some (d.ino, ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, fa, fb, .idle⟩)) ∗
          ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil⌝ ∗ csOwnF γ (some (d.ino, ⟨m, bs, fa, fb, .idle⟩)))) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- See the file header. -/
abbrev golang_org.x.sys.unix.Munmap.specCrashS : Prop :=
  ∀ (base : Loc) (len : w64) (i : Ino) (N : Namespace) (P : GoString) (R : Roots) (γ : GName)
    (Good : Option OsFile → Prop) (Ok : CState → Prop) (m : OsMeta) (bs : List (w8 × Bool))
    (fa fb : Nat) (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  Ok (some (i, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)) →
  {{ osInv (GF := GF) ∗ csInv (GF := GF) N P R γ Good Ok ∗
      csOwnF (GF := GF) γ (some (i, ⟨m, bs, fa, fb, .idle⟩)) ∗ cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ (e : w64), RET #(errnoErr e);
      (⌜e = 0⌝ ∗ csOwnF γ (some (i, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩))) ∨
      (⌜e ≠ 0⌝ ∗
        (csOwnF γ (some (i, ⟨{ m with maps := GMap.delete base m.maps }, bs, fa, fb, .idle⟩)) ∨
         (csOwnF γ (some (i, ⟨m, bs, fa, fb, .idle⟩)) ∗ cellsR base 0 len.toNat vf))) }}

end spec

end EtcdGrove
end Perennial
