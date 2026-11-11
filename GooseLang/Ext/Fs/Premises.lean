/-
Premises a client's theorem may state on its executions, beyond the Linux file extension's
semantics (`Impl.lean`) [Trusted definitions!]: the semantics restricted by a premise `SQ` on
steps and a premise `Q` on crashes (`fsSemWithS SQ Q`: step `FsStep ∧ SQ`, crash `OsCrash ∧ Q`). A
theorem proved over it holds of the executions that satisfy both: an assumption on the environment,
which the theorem states, and which none of the semantics' own rules make.

`SectorWhole` is the one such premise defined here: a known limitation, assumed only for etcd's
WAL (`notes/STATUS.md`, "Known limitations"; `nonissues/etcd-wal-torn-tail-mid-sector.md`).
-/
module

public import GooseLang.Ext.Fs.Impl

@[expose] public section

noncomputable section

namespace Perennial
namespace Fs

/-- A premise on the extension's steps: of the operation `op` on `v`, from `st` to `st'` with the
result `e'`. -/
abbrev StepPrem := ∀ [GooseExts] [GoGlobalContext], String → val → OsState → Expr → OsState → Prop

/-- The semantics whose steps are `FsStep`s satisfying `SQ` and whose crashes are `OsCrash`es
satisfying `Q`. -/
@[instance_reducible] def fsSemWithS (SQ : StepPrem) (Q : OsState → OsState → Prop) :
    ExtSemantics fsExt where
  step o v h st g e' h' st' g' := FsStep o v h st g e' h' st' g' ∧ SQ o v st e' st'
  crash st st' := OsCrash st st' ∧ Q st st'

/-- **SectorWhole** for the files at the paths `covers` holds, at a crash from `st` to `st'`: each
512-byte sector of such a file that holds a byte below its crash size comes back as one state of
that sector, as of some change `m` (each byte its candidate as of `m`, `valAt`): a crash never
mixes, within one sector, two changes, or a change's prefix with what was there before.

What it assumes, exactly: changes on a file never overlap in time (at most one is in flight, the
semantics' rule), so `valAt · m` is the page cache right after change `m` *when each change landed
all it announced*. A change that landed short (a short `pwrite`, or one that failed part way)
leaves the page cache in a state that is no stamp's, and this premise excludes a crash that keeps
such a state in a covered sector, as it excludes a sector torn by writeback.

A premise on executions, not a property of Linux: on configuration C one `pwrite` can reach disk
torn mid-sector (`notes/axiom-review/fs-v2-r6/e2e/`, mechanisms A and B). It is assumed only where
a client relies on it, etcd's WAL (`decoder.go`'s `isTornEntry` takes a torn tail to leave whole
sectors of zeros), as a known limitation (`notes/STATUS.md`, "Known limitations";
`nonissues/etcd-wal-torn-tail-mid-sector.md`; `examples/osfs/semantics/premise_sector_whole.go`).
For the WAL (one appender, each `pwrite` over preallocated zeros, a short write retried by Go's
loop) it says what `isTornEntry` needs: a torn tail sector is a sector of zeros or one write's.
Evidence: none that it holds; the WAL test on C (`notes/axiom-review/fs-v2-r6/wal/`) caught no
tail torn mid-sector on disk in 202 crash images, but the mechanisms that would tear one are
present in the WAL's code. A crash that keeps every covered byte as of its last sync satisfies it
(`m = 0`), so it never leaves a state without a crash. -/
def SectorWhole (covers : GoString → Prop) (st st' : OsState) : Prop :=
  ∀ p i f f', covers p → st.lookup p = some (.file i) → st.fs.files !! i = some f →
    st'.fs.files !! i = some f' → ∀ n, 512 * n < f'.size →
      ∃ m, ∀ j < 512, f'.cache (512 * n + j) = valAt (f.cand (512 * n + j)) m

end Fs
end Perennial

end
