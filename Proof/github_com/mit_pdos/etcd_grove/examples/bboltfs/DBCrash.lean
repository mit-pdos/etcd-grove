/-
minibolt's open `DB` over the crash invariant of its file (`csInv`, `Proof/os/CrashSt.lean`):
`DB.lean`'s representation predicate with the writer's part of the file as a state of the crash
invariant, for the crash-aware specs of `Open`, `commit` and `Close`. Lean-first (no Rocq
counterpart).

**What changes from `DB.lean`.** The file's `OsMeta` and bytes are no longer held by `rwlock` and
`metalock` directly: the crash invariant `csInv dbCrashN p γc (dbOk p)` holds half of each byte
not frozen, half the `OsMeta` and the frozen bytes (discarded), and keeps every state it passes
through `dbOk` (`CrashOkS (P1 p) p Good`: every image a crash may leave is `goodImg`).
- `rwlock` (`rwRC`): `writerFileC` holds the writer's part of that state, `csOwn p γc (some ⟨m,
  bs, 8192, 4096 * hwm, .idle⟩)`, in place of the whole `OsMeta`, its half of the meta pages and
  its whole tail: the committed pages `[8192, 4096 * hwm)` are frozen (their `pageIs` copies come
  from `cs_freeze`), every other byte is the writer's half (the invariant holds the other). While
  not failed, the state is one a commit may start from (`commitClean`: valid meta pages, both
  meta slots and the current root page clean, the current meta in slot `txid % 2`, the size
  since the last sync covering the high water mark, the current root page `bootOk`), and its
  meta pages are `mp`.
- `metalock` (`metaRC`): `metaR` without its half of the meta-page bytes (the invariant holds
  that half now; commit's meta `WriteAt` needs only the writer's `csOwn`).
- `mmaplock` (`mapR`), the mapping invariant, the reader pool: as in `DB.lean`.

`bootOk` is `BootMinibolt`'s check of the current root page (`CrashGood.lean`): its crash
invariant (`Good`) needs it of every committed transaction, so the client's predicate on
transactions (`γ.vp`) must imply it (`isDBC`'s `vpBoot`).
-/
module

public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB
public import Proof.github_com.mit_pdos.etcd_grove.examples.bboltfs.CrashImg
public import Spec.github_com.mit_pdos.etcd_grove.examples.bboltfs.DB__initCrash

@[expose] public section

set_option linter.iris.style.nameCheck false

noncomputable section

namespace Perennial
namespace EtcdGrove
namespace bboltfs

open Iris Iris.BI Iris.ProgramLogic Iris.Std github_com.mit_pdos.etcd_grove.examples.bboltfs

/-- The namespace of the database file's crash invariant. -/
def dbCrashN : Namespace := nroot .@ "minibolt_crash"

/-- minibolt's obligation on the states of its file: every image a crash may leave is good. -/
abbrev dbOk [GooseExts] (p : GoString) : CState → Prop := CrashOkS (P1 p) p Good

section pure
variable [GooseExts]

/-- `commitClean` does not look at the mappings or `ok`. -/
theorem commitClean_meta {m m' : OsMeta} {bs : List (w8 × Bool)} (h : commitClean m bs)
    (hhi : m'.hi = m.hi) (hlo : m'.lo = m.lo) : commitClean m' bs :=
  ⟨hhi ▸ h.hi, hlo ▸ h.lo, h.ok, h.slot, hlo ▸ h.pg, h.boot, h.metas, h.root⟩

/-- The writer's idle states while not failed are `dbOk`, whatever the mappings (`Mmap`'s and
`Munmap`'s obligations). -/
theorem writer_okS {p : GoString} {m : OsMeta} {bs : List (w8 × Bool)} (fa fb : Nat)
    (hl : bs.length = m.size) (h : commitClean m bs) (M : GMap Loc Nat) :
    dbOk p (some ⟨{ m with maps := M }, bs, fa, fb, .idle⟩) :=
  commitClean_okS (p := p) ⟨{ m with maps := M }, bs, fa, fb, .idle⟩ hl rfl
    (commitClean_meta h rfl rfl)

/-- After `init` (`DB.init.specCrash`'s post), a commit may start: the writer's invariant. -/
theorem init_commitClean {m : OsMeta} {xs : List (w8 × Bool)} (hsz : m.size ≤ 2 ^ 30) :
    commitClean (initDoneMeta m xs) (initFile xs) := by
  have hil := initBytes_length
  simp only [pageBytes] at hil
  have hfst : (initFile xs).map Prod.fst = initBytes ++ (xs.map Prod.fst).drop 16384 := by
    unfold initFile; rw [List.map_map]; exact List.map_id _
  have hmp : ((initFile xs).map Prod.fst).take 8192 = initBytes.take 8192 := by
    rw [hfst, List.take_append_of_le_length (by omega)]
  have hmp' : (((initFile xs).map Prod.fst).take 8192).take 8192 = initBytes.take 8192 := by
    rw [List.take_take, Nat.min_self, hmp]
  have hc := curMeta_init _ hmp'
  have hroot : curRoot (((initFile xs).map Prod.fst).take 8192) = 3 := by
    rw [curRoot, hc, initMeta_root]; decide
  have hpg : curPgid (((initFile xs).map Prod.fst).take 8192) = 4 := by
    rw [curPgid, hc, initMeta_pgid]; decide
  have hcl : ∀ k < 16384, ∃ b, (initFile xs)[k]? = some (b, true) := by
    intro k hk
    unfold initFile
    rw [List.getElem?_map, List.getElem?_append_left (by omega),
      List.getElem?_eq_getElem (by omega)]
    exact ⟨_, rfl⟩
  have hlen : (((initFile xs).map Prod.fst).take 8192).length = 8192 := by
    rw [hmp, List.length_take]; omega
  refine ⟨by simp only [initDoneMeta]; omega, by simp only [initDoneMeta]; omega,
    metaPagesOk_init _ hmp' hlen, ?_, ?_, ?_,
    fun k hk => hcl k (by omega), fun k hk => hcl _ (by rw [hroot]; omega)⟩
  · unfold curInSlot
    rw [hc, initMeta_txid, show (W64 ((1 : Nat) : Int)).toNat % 2 = 1 by decide,
      initMetas _ hmp' 1 (by decide)]
  · rw [hpg]; simp only [initDoneMeta]; omega
  · rw [hc, hroot, hfst, List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by simp only [List.length_drop]; omega)]
    have : (initBytes.drop (4096 * 3)).take 4096 = emptyPageBytes (W64 3) (W16 2) := by
      have h0 := metaPageBytes_length 0
      have h1 := metaPageBytes_length 1
      have h2 := emptyPageBytes_length (W64 2) (W16 16)
      have h3 := emptyPageBytes_length (W64 3) (W16 2)
      simp only [pageBytes] at h0 h1 h2 h3
      unfold initBytes
      rw [List.drop_append_of_le_length (by simp only [List.length_append]; omega)]
      rw [List.drop_eq_nil_of_le (by simp only [List.length_append]; omega), List.nil_append,
        List.take_of_length_le (by omega)]
    rw [this, initRoot_val, initMeta_txid]
    exact .inl ⟨by decide, rfl⟩

end pure

section preds
variable [GooseExts] [GooseSemantics] [GooseInterp] [HasExt osFsExt]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : Assumptions]

/-- The writer's part of the file, with the mapping in the state `st`, as a state of the crash
invariant `γc` (see the file header): `writerFile`'s, with `csOwn` for the `OsMeta` and bytes,
and the state `dbOk` whatever the mappings (for `munmap` once failed, when `commitClean` may no
longer hold). -/
def writerFileC (γc : GName) (db f : Loc) (fd : w64) (p : GoString) (mp : List w8) (fl : Bool)
    (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)) : IProp GF :=
  iprop(∃ fsz : Nat,
    db.[DB, go!"filesz"] ↦ W64 fsz ∗ db.[DB, go!"datasz"] ↦ W64 (mapLen st) ∗
    os.ownFile (GF := GF) f fd p (DFrac.own (1 : Qp).half) ∗
    osFd (GF := GF) fd (DFrac.own (1 : Qp).half) ⟨p, true, true⟩ ∗
    csOwn (GF := GF) p γc (some ⟨m, bs, 8192, 4096 * hwm, .idle⟩) ∗
    ⌜2 ≤ hwm ∧ 4096 * hwm ≤ m.size ∧
      (∀ M : GMap Loc Nat, dbOk p (some ⟨{ m with maps := M }, bs, 8192, 4096 * hwm, .idle⟩)) ∧
      (fl = false → (bs.map Prod.fst).take 8192 = mp ∧ commitClean m bs ∧ fsz = m.size ∧
        0 ≤ fd.toInt ∧ 4 * 4096 ≤ m.size ∧ m.size ≤ 2 ^ 30 ∧ mapLen st ≤ 2 ^ 30)⌝)

/-- `metalock`'s resource over the crash invariant: `metaR` without the meta-page bytes. -/
def metaRC (γ : DBNames) (db : Loc) (p : GoString) : IProp GF :=
  iprop(∃ (b : Bool) (mp : List w8) (hwm : Nat) (c : Bool) (T : GMap Nat (Option w64)),
    db.[DB, go!"failed"] ↦ b ∗ ghostVar γ.cur (1 : Qp).half (mp, b, hwm) ∗
    ghostVar γ.cls (1 : Qp).half c ∗
    ghostMapAuth γ.txs 1 T ∗ ghostVar γ.out (1 : Qp).half.half false ∗
    match b with
    | true => monoNatAuthOwn γ.fail 1 1 ∗ ∃ t : Nat, ghostVar γ.own (1 : Qp).half (t, 0)
    | false =>
      monoNatAuthOwn γ.fail 1 0 ∗ ⌜metaPagesOk mp ∧ hwm = curPgid mp ∧
        ∀ k, (curMeta mp).txid'.toNat < k → T !! k = none⌝ ∗
      monoNatAuthOwn γ.last 1 (curMeta mp).txid'.toNat ∗
      ghostVar γ.own (1 : Qp).half ((curMeta mp).txid'.toNat, hwm) ∗
      ∃ B, pageIs (GF := GF) p (curRoot mp) B ∗ dbTx γ (curMeta mp).txid'.toNat (pageVal B) ∗
        ⌜T !! (curMeta mp).txid'.toNat = some (pageVal B)⌝)

/-- `rwlock`'s resource over the crash invariant `γc`: `rwR`'s, with `writerFileC`. -/
def rwRC (γ : DBNames) (γc : GName) (db f : Loc) (fd : w64) (p : GoString) : IProp GF :=
  iprop((∃ (mp : List w8) (fl : Bool) (hwm : Nat) (st : MapSt) (m : OsMeta) (bs : List (w8 × Bool)),
    ghostVar γ.cur (1 : Qp).half.half (mp, fl, hwm) ∗ ghostVar γ.map (1 : Qp).half st ∗
    ghostVar γ.out (1 : Qp).half.half false ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st ∗
    writerFileC (GF := GF) γc db f fd p mp fl hwm st m bs ∗ ghostVar γ.cls (1 : Qp).half false ∗
    ⌜fl = false → m.ok = true⌝ ∗
    match st with
    | some (base, len, γm) =>
      ⌜m.maps = {[base := len]} ∧ m.size ≤ len ∧ 0 < base.addr ∧ len ≤ 2 ^ 41⌝ ∗
      ghostVar γm (1 : Qp).half () ∗ mapInv (GF := GF) γ p base len γm ∗
      writerCells (GF := GF) base hwm len
    | none => dbFailed (GF := GF) γ ∗ writerExtra (GF := GF) γ f fd p mp fl hwm) ∨
   ((∃ x : Nat × Nat, ghostVar γ.own (1 : Qp).half x) ∗ ghostVar γ.cls (1 : Qp).half true ∗
     ∃ st, ghostVar γ.map (1 : Qp).half st ∗ mapFields (GF := GF) db (DFrac.own (1 : Qp).half) st))

/-- The persistent part of an open database over the crash invariant `γc` of its file: `isDB`'s,
with `rwRC` and `metaRC`, the crash invariant, and the client's predicate on transactions
implying `BootMinibolt`'s check (`vpBoot`). -/
def isDBC (γ : DBNames) (γc : GName) (db : Loc) : IProp GF :=
  iprop((∃ (f : Loc) (fd : w64) (p : GoString),
    pkgFacts (GF := GF) ∗ osInv (GF := GF) ∗ db.[DB, go!"file"] ↦□ f ∗ db.[DB, go!"path"] ↦□ p ∗
    csInv (GF := GF) dbCrashN p γc (dbOk p) ∗
    sync.isMutex db.[DB, go!"rwlock"] (rwRC (GF := GF) γ γc db f fd p) ∗
    sync.isMutex db.[DB, go!"metalock"] (metaRC (GF := GF) γ db p) ∗
    sync.isRWMutexGuard db.[DB, go!"mmaplock"] (mapR (GF := GF) γ db f fd p)) ∗
    ⌜∀ t vo, γ.vp t vo → bootOk t vo⌝ ∗
    ∃ γp : GName, threadPool.isThreadPool dbPoolN γp (dbReader (GF := GF) γ db))

instance isDBC_persistent (γ : DBNames) (γc : GName) (db : Loc) :
    Persistent (isDBC (GF := GF) γ γc db) := by
  unfold isDBC; infer_instance

end preds

end bboltfs
end EtcdGrove
end Perennial
