/-
The local crash specs of `Spec/os/CrashStIL.lean`, `Spec/os/CrashStILLong.lean` and
`Spec/os/CrashStILA.lean` over `csInvIR N i γ γa γc Ok R` (`Proof/os/CrashStIR.lean`): the crash
invariant whose open alternative holds the client's resource `R a` (bbolt's: its committed data's
version, history and synced mark, `Proof/go_etcd_io/bbolt/Inv/BFile.lean`'s `bR`). Each is its
`csInvI` statement with `csInvIR … R` for `csInvI …` (a timeless `R`); the call keeps `R` (its value
does not change), but `syscall.Fdatasync.specCrashILAR`, whose value moves from `a` to `a'`, takes
`R a ⊣⊢ R a'` (a client resource that reads only what the move keeps). The `csInvI` statements are the case `R := fun _ => emp` (`csInvI_R`). Proved in
`Proof/os/CrashStILSpec.lean`, `Proof/os/CrashStILLong.lean`, `Proof/os/CrashStILASpec.lean`.
Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashStILLong
public import Spec.os.CrashStILA
public import Proof.os.CrashStIR

@[expose] public section

noncomputable section

namespace Perennial

open Fs

namespace EtcdGrove

open Iris Iris.BI

section spec
variable [GooseExts] [GooseSemantics] [GooseInterp] [ExtSemantics Fs.fsExt] [Fs.FsSemOk] [HasExt Fs.fsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

variable [os.Assumptions] in
/-- `os.File.WriteAt.specCrashIL` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev os.File.WriteAt.specCrashILR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (data : List w8) (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)] (a : A) (m : OsMeta) (bs xs : List ByteG),
  d.ino = i → d.writable = true → 0 ≤ off.toInt → off.toNat + data.length ≤ m.size →
  off.toNat + data.length ≤ maxBytes → off.toNat + data.length < 2 ^ 63 → 0 < data.length → data.length ≤ 0x40000000 →
  xs.length = data.length → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ nn m' bs', WReach m bs off.toNat data nn m' bs' →
    Ok a ⟨m', bs', 0, 0, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off.toNat + nn) (data.drop nn) n →
      Ok a ⟨m', bs', 0, 0, .write t (off.toNat + nn) (data.drop nn) n⟩)) →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      osBytes (GF := GF) i off.toNat (DFrac.own (1 : Qp).half) xs ∗
      mcellsAny (GF := GF) m.maps off.toNat (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      mcellsAny m.maps off.toNat (off.toNat + data.length) ∗
      ∃ (nn : Nat) (m' : OsMeta) (bs' : List ByteG),
        ⌜xs = (bs.drop off.toNat).take data.length ∧ WReach m bs off.toNat data nn m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ nn = data.length ∧
              m'.size = m.size ∧ m'.maps = m.maps ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil ∧ ¬ FsNoErr))⌝ ∗
        csOwnIL i γ γa ⟨m', bs', 0, 0, .idle⟩ a ∗
        osBytes i off.toNat (DFrac.own (1 : Qp).half) ((bs'.drop off.toNat).take data.length) }}

variable [os.Assumptions] in
/-- `os.File.Truncate.specCrashIL` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev os.File.Truncate.specCrashILR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64)
    (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)]
    (a : A) (m : OsMeta) (bs : List ByteG),
  d.ino = i → 0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat →
  sz.toNat ≤ maxBytes → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ m' bs', TReach m bs sz.toNat m' bs' →
    Ok a ⟨m', bs', 0, 0, .idle⟩ ∧ ∀ t n, Ok a ⟨m', bs', 0, 0, .trunc t sz.toNat n⟩) →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ ∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
          csGrownL (GF := GF) (csTokI γ γa a) i m0 bs sz.toNat n) ∨
       (⌜err ≠ interface.nil ∧ ¬ FsNoErr⌝ ∗
         ((∃ n m0, ⌜m0 = m ∨ m0 = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat⌝ ∗
          csGrownL (GF := GF) (csTokI γ γa a) i m0 bs sz.toNat n) ∨
          (csOwnIL i γ γa ⟨m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat,
              bs, 0, 0, .idle⟩ a ∗
            mcellsAny m.maps m.size (rsHi true m.size sz.toNat))))) }}

variable [os.Assumptions] in
/-- `os.File.Sync.specCrashIL` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev os.File.Sync.specCrashILR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf dq : DFrac) (d : OsFd)
    (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)] (a : A) (m : OsMeta)
    (bs : List ByteG) (c : Nat → Bool),
  d.ino = i → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ b, b < m.size → m.dlo ≤ b → b < m.dhi → c b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1) →
  Ok a (csSynced m [] [] bs 0 0) →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      cBytes (GF := GF) i (fun _ => DFrac.own (1 : Qp).half) c 0 bs }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Sync")) (Val #()))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ((⌜err = interface.nil⌝ ∗ csOwnIL i γ γa (csSynced m [] [] bs 0 0) a ∗
          cBytes i (fun _ => DFrac.own (1 : Qp).half) c 0 (bs.map (fun x => durB x.1))) ∨
       (⌜err ≠ interface.nil ∧ ¬ FsNoErr⌝ ∗ csOwnIL i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
          cBytes i (fun _ => DFrac.own (1 : Qp).half) c 0 bs)) }}

variable [syscall.Assumptions] in
/-- `syscall.Fdatasync.specCrashIL` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev syscall.Fdatasync.specCrashILR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)] (a : A) (m : OsMeta) (bs : List ByteG) (c : Nat → Bool),
  d.ino = i → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ b, b < m.size → m.dlo ≤ b → b < m.dhi → c b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1) →
  Ok a (csSynced m [] [] bs 0 0) →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ osFd (GF := GF) fd dq d ∗
      csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      cBytes (GF := GF) i (fun _ => DFrac.own (1 : Qp).half) c 0 bs }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ csOwnIL i γ γa (csSynced m [] [] bs 0 0) a ∗
          cBytes i (fun _ => DFrac.own (1 : Qp).half) c 0 (bs.map (fun x => durB x.1))) ∨
       (⌜e ≠ 0 ∧ ¬ FsNoErr⌝ ∗ csOwnIL i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
          cBytes i (fun _ => DFrac.own (1 : Qp).half) c 0 bs)) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- `golang_org.x.sys.unix.Mmap.specCrashIL` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev golang_org.x.sys.unix.Mmap.specCrashILR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (fd off len prot fl : w64) (dq : DFrac) (d : OsFd) (N : Namespace)
    (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)] (a : A) (m : OsMeta) (bs : List ByteG),
  d.ino = i → d.readable = true → off = 0 → 0 < len.toInt → prot.toNat = PROT_READ →
  (fl.toNat = MAP_SHARED ∨ fl.toNat = MAP_SHARED + MAP_POPULATE) → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ base : Loc, Ok a ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, 0, 0, .idle⟩) →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ osFd (GF := GF) fd dq d ∗
      csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a }}
    (App (App (App (App (App (Val (@! golang_org.x.sys.unix.Mmap)) (Val #fd)) (Val #off))
      (Val #len)) (Val #prot)) (Val #fl))
  {{ (sl : GoSlice) (e : w64), RET (PairV #sl #(errnoErr e)); osFd fd dq d ∗
      ((∃ base : Loc, ⌜e = 0 ∧ sl = ⟨base, len, len⟩⌝ ∗
          csOwnIL i γ γa ⟨{ m with maps := <[base := len.toNat]> m.maps }, bs, 0, 0, .idle⟩ a ∗
          ∃ bs0 : List w8, ⌜bs0.length = m.size⌝ ∗
            cellsR base 0 len.toNat (fun i => toCellVal bs0[i]?)) ∨
       (⌜e ≠ 0 ∧ sl = slice.nil ∧ ¬ FsNoErr⌝ ∗ csOwnIL i γ γa ⟨m, bs, 0, 0, .idle⟩ a)) }}

variable [golang_org.x.sys.unix.Assumptions] in
/-- `golang_org.x.sys.unix.Munmap.specCrashIL` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev golang_org.x.sys.unix.Munmap.specCrashILR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (base : Loc) (len : w64) (i : Ino) (N : Namespace)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)] (a : A) (m : OsMeta) (bs : List ByteG)
    (vf : Nat → val),
  0 < len.toInt → m.maps !! base = some len.toNat → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  Ok a ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩ →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗
      csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗ cellsR (GF := GF) base 0 len.toNat vf }}
    (App (Val (@! golang_org.x.sys.unix.Munmap)) (Val #(⟨base, len, len⟩ : GoSlice)))
  {{ (e : w64), RET #(errnoErr e);
      (⌜e = 0⌝ ∗ csOwnIL i γ γa ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩ a) ∨
      (⌜e ≠ 0 ∧ ¬ FsNoErr⌝ ∗
        (csOwnIL i γ γa ⟨{ m with maps := GMap.delete base m.maps }, bs, 0, 0, .idle⟩ a ∨
         (csOwnIL i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗ cellsR base 0 len.toNat vf))) }}

variable [os.Assumptions] in
/-- `os.File.WriteAt.specCrashILLong` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev os.File.WriteAt.specCrashILLongR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sl : GoSlice)
    (data : List w8) (dqs : DFrac) (off : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)] (a : A) (m : OsMeta) (bs xs : List ByteG),
  d.ino = i → d.writable = true → 0 ≤ off.toInt → off.toNat + data.length ≤ m.size →
  off.toNat + data.length ≤ maxBytes → off.toNat + data.length < 2 ^ 63 → 0 < data.length →
  xs.length = data.length → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ nn m' bs', WReachC m bs off.toNat data nn m' bs' →
    Ok a ⟨m', bs', 0, 0, .idle⟩ ∧ (nn < data.length → ∀ t n,
      PwFresh m' bs' (off.toNat + nn) (wchunk data nn) n →
      Ok a ⟨m', bs', 0, 0, .write t (off.toNat + nn) (wchunk data nn) n⟩)) →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ os.ownFile (GF := GF) f fd name dqf ∗
      sl ↦*{dqs} data ∗ osFd (GF := GF) fd dq d ∗
      csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      osBytes (GF := GF) i off.toNat (DFrac.own (1 : Qp).half) xs ∗
      mcellsAny (GF := GF) m.maps off.toNat (off.toNat + data.length) }}
    (App (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"WriteAt")) (Val #sl))
      (Val #off))
  {{ (n : w64) (err : GoInterface), RET (PairV #n #err);
      os.ownFile f fd name dqf ∗ sl ↦*{dqs} data ∗ osFd fd dq d ∗
      mcellsAny m.maps off.toNat (off.toNat + data.length) ∗
      ∃ (nn : Nat) (m' : OsMeta) (bs' : List ByteG),
        ⌜xs = (bs.drop off.toNat).take data.length ∧ WReachC m bs off.toNat data nn m' bs' ∧
          ((n = W64 data.length ∧ err = interface.nil ∧ nn = data.length ∧
              m'.size = m.size ∧ m'.maps = m.maps ∧
              ∀ i < data.length, (bs'[off.toNat + i]?).map Prod.fst = data[i]?) ∨
           (n = W64 0 ∧ err ≠ interface.nil ∧ ¬ FsNoErr))⌝ ∗
        csOwnIL i γ γa ⟨m', bs', 0, 0, .idle⟩ a ∗
        osBytes i off.toNat (DFrac.own (1 : Qp).half) ((bs'.drop off.toNat).take data.length) }}

variable [os.Assumptions] in
/-- `os.File.Truncate.specCrashILBig` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call). -/
abbrev os.File.Truncate.specCrashILBigR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (f : Loc) (fd : w64) (name : GoString) (dqf : DFrac) (sz : w64)
    (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino) (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)]
    (a : A) (m : OsMeta) (bs : List ByteG),
  d.ino = i → 0 ≤ fd.toInt → d.writable = true → 0 ≤ sz.toInt → m.size ≤ sz.toNat →
  maxBytes < sz.toNat → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ m', (m' = m ∨ m' = m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat) →
    Ok a ⟨m', bs, 0, 0, .idle⟩ ∧ ∀ t n, Ok a ⟨m', bs, 0, 0, .trunc t sz.toNat n⟩) →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ os.ownFile (GF := GF) f fd name dqf ∗
      osFd (GF := GF) fd dq d ∗ csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      mcellsAny (GF := GF) m.maps m.size (rsHi true m.size sz.toNat) }}
    (App (Val (f @!! go.GoType.PointerType os.File.ty @!! go!"Truncate")) (Val #sz))
  {{ (err : GoInterface), RET #err; os.ownFile f fd name dqf ∗ osFd fd dq d ∗
      ⌜err ≠ interface.nil⌝ ∗ fmtErrorOk err ∗
      csOwnIL i γ γa ⟨m.announce (min m.size sz.toNat) (rsHi true m.size sz.toNat) sz.toNat,
        bs, 0, 0, .idle⟩ a ∗
      mcellsAny m.maps m.size (rsHi true m.size sz.toNat) }}

variable [syscall.Assumptions] in
/-- `syscall.Fdatasync.specCrashILA` over `csInvIR` (the crash invariant with the client resource `R`, kept
unchanged by the call, or moved with the value: `R a ⊣⊢ R a'`). -/
abbrev syscall.Fdatasync.specCrashILAR : Prop :=
  ∀ {A : Type} [Pos.Countable A] (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (R : A → IProp GF) [∀ a, Timeless (R a)] (a a' : A) (m : OsMeta) (bs : List ByteG)
    (c : Nat → Bool),
  d.ino = i → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ b, b < m.size → m.dlo ≤ b → b < m.dhi → c b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1) →
  Ok a' (csSynced m [] [] bs 0 0) → (R a ⊣⊢ R a') →
  {{ osInv (GF := GF) ∗ csInvIR (GF := GF) N i γ γa γc Ok R ∗ osFd (GF := GF) fd dq d ∗
      csOwnIL (GF := GF) i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
      cBytes (GF := GF) i (fun _ => DFrac.own (1 : Qp).half) c 0 bs }}
    (App (Val (@! syscall.Fdatasync)) (Val #fd))
  {{ (e : w64), RET #(errnoErr e); osFd fd dq d ∗
      ((⌜e = 0⌝ ∗ csOwnIL i γ γa (csSynced m [] [] bs 0 0) a' ∗
          cBytes i (fun _ => DFrac.own (1 : Qp).half) c 0 (bs.map (fun x => durB x.1))) ∨
       (⌜e ≠ 0 ∧ ¬ FsNoErr⌝ ∗ csOwnIL i γ γa ⟨m, bs, 0, 0, .idle⟩ a ∗
          cBytes i (fun _ => DFrac.own (1 : Qp).half) c 0 bs)) }}

end spec

end EtcdGrove
end Perennial
