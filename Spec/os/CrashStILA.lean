/-
`syscall.Fdatasync.specCrashILA`: `syscall.Fdatasync.specCrashIL` (`Spec/os/CrashStIL.lean`) with the
crash invariant's value moving from `a` to `a'` as the sync lands (`Ok a'` of the synced state; the
value stays `a` on an error). For bbolt's second `fdatasync` of a commit, which ends the commit
phase. Proved in `Proof/os/CrashStILASpec.lean`. Lean-first (no Rocq counterpart).
-/
module

public import Spec.os.CrashStIL

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

variable [syscall.Assumptions] in
/-- `syscall.Fdatasync.specCrashIL`, the value moving to `a'` with the sync (see the file header). -/
abbrev syscall.Fdatasync.specCrashILA : Prop :=
  ∀ {A : Type} [Pos.Countable A] (fd : w64) (dq : DFrac) (d : OsFd) (N : Namespace) (i : Ino)
    (γ γa γc : GName) (Ok : A → CSt → Prop) (a a' : A) (m : OsMeta) (bs : List ByteG)
    (c : Nat → Bool),
  d.ino = i → ↑osN ⊆ (⊤ : CoPset) \ ↑N →
  (∀ b, b < m.size → m.dlo ≤ b → b < m.dhi → c b = true ∨ ∃ x, bs[b]? = some x ∧ x = durB x.1) →
  Ok a' (csSynced m [] [] bs 0 0) →
  {{ osInv (GF := GF) ∗ csInvI (GF := GF) N i γ γa γc Ok ∗ osFd (GF := GF) fd dq d ∗
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
