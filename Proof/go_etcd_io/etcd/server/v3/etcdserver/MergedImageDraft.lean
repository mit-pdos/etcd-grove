/-
**Draft: `merged_image` restated** (`notes/merged-image-plan.md`; `notes/decisions.md`,
"`merged_image` is false with compaction on"). Imported by nothing; no `axiom`, no `sorry`. Nothing
here is switched: `SnapSendBranch.lean`'s `merged_image` is unchanged.

- `srvRaftLogInv_fresh`: the server's raft names are the fresh start's (`srvRaftLogInv`'s
  `pre = []` and `ai0 = pre.length`), a law for `SrvRaftLog.lean` beside `srvRaftLogInv_facts`.
- `merged_image'`: `merged_image` with one premise more, `E.cmp = false` (with compaction on the
  image can hold `Meta`'s `scheduledCompactRev` and lack compacted keys, and `srvImage` says
  neither). Proved; the fresh start's names come from `isServer` (`srvRaftLogInv_fresh`).

(Review round 1 removed the draft's `hraft` premise and the two ways of carrying it to `applyAll`'s
batch case, `specBatchR` and the `isServerApplyAll` conjunct: `isServer` already gives it.)
-/
module

public import Proof.go_etcd_io.etcd.server.v3.etcdserver.SnapSendBranch
public import Proof.go_etcd_io.etcd.server.v3.etcdserver.KVChainOff
public import Spec.go_etcd_io.etcd.server.v3.etcdserver.EtcdServer__applyAll

@[expose] public section

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace EtcdGrove

open Iris Iris.BI Iris.ProofMode go_etcd_io.etcd.server.v3.etcdserver

section draft
variable [GooseExts] [GooseSemantics] [GooseInterp]
variable [go_gctx : GoGlobalContext]
variable {GF : BundledGFunctors} [hG : HeapGS HasLC.hasLC GF]
variable [sem : go.Semantics]
variable [package_sem : go_etcd_io.etcd.server.v3.etcdserver.Assumptions]

/-- **The server's raft names are the fresh start's** (`srvRaftLogInv`: the start log empty, the
start index its length). For `SrvRaftLog.lean`, beside `srvRaftLogInv_facts`. -/
theorem srvRaftLogInv_fresh (γ : ServerRaftNames) :
    srvRaftLogInv (GF := GF) γ ⊢ ⌜γ = ⟨γ.raft, [], W64 0⟩⌝ := by
  unfold srvRaftLogInv
  iintro ⟨-, -, -, %ha, %hp, -⟩
  ipureintro
  have ha0 : γ.ai0 = W64 0 := by
    rw [hp] at ha; simp only [List.length_nil] at ha
    word
  cases γ; simp only at hp ha0 ⊢; rw [hp, ha0]

/-- **Draft of `merged_image`** (the merged snapshot's image certificate, `srvNet`'s `img`), with
the compaction mode off (`hcmp`), the one premise added. The image is
`srvImage` of the apply thread's KV names: `kvApplied` gives the committed `A` and
`x.log = kvModel γr.kv A`; `mergedObs`'s exact `Key` clause and `noCmpData` (both at `cmp = false`)
give `keyImage`; its `Meta` and rest clauses the rest of `imageAt`; the KV invariant the start
chain (`kvInv_ch0_off`), the raft log's invariant the fresh start's names (`srvRaftLogInv_fresh`). -/
theorem merged_image' (s : Loc) (γ : ApplyNames) (ci : Loc) (TM : MetaCI → IProp GF)
    (E : apply.AEnv GF) (ρ : ReqNames) (γr : ReadNames) (ai : w64) (A : List EntryModel)
    (x : apply.ApplyKV) (D : backend.Data) (hlen : uint.Z ai = A.length)
    (h0 : γr.kv.c0 = W64 0 ∧ γr.kv.log0 = [[], []])
    (hcmp : E.cmp = false) :
    ⌜mergedObs γr E.cmp ai A x.log D⌝ ∗ isServer s γ ci TM E ρ γr ∗ kvApplied γr.raft γr.kv A x ⊢
      |={⊤}=> kvApplied γr.raft γr.kv A x ∗ □ (srvNet (GF := GF) γr.raft.raft).img ai D := by
  iintro ⟨%hobs, #Hsrv, Hka⟩
  rw [hcmp] at hobs
  obtain ⟨-, hkey, hnc, hci, hterm, hrest, hwf⟩ := hobs
  iunfold isServer at Hsrv
  icases Hsrv with ⟨-, -, -, Hat, -, -⟩
  iunfold srvAtomics at Hat
  icases Hat with ⟨-, -, Hki⟩
  iunfold srvKVInvs at Hki
  icases Hki with ⟨#Hki, -, #Hrl, -⟩
  ihave %hraft := srvRaftLogInv_fresh γr.raft $$ Hrl
  imod (kvInv_ch0_off γr.raft γr.kv) $$ Hki with %hch
  iunfold kvApplied at Hka
  icases Hka with ⟨Hka, %hx⟩
  iunfold kvAppliedL at Hka
  icases Hka with ⟨#HA, Hhi, Hcert, %hlog⟩
  imodintro
  isplitl [Hhi Hcert]
  · iunfold kvApplied
    iunfold kvAppliedL
    iframe HA Hhi Hcert
    ipureintro; exact ⟨hlog, hx⟩
  ihave #HA' : srvRLogLb (GF := GF) ⟨γr.raft.raft, [], W64 0⟩ A $$ []
  · rw [← hraft]; iexact HA
  iintro !>
  simp only [srvNet]
  iapply (srvImage_of_dbImage (γk := γr.kv) h0.1 hch h0.2)
  iunfold dbImage
  iexists A
  iframe HA'
  ipureintro
  have hpre : γr.raft.pre = [] := by rw [hraft]
  rw [hlog] at hkey hwf
  have hz : uint.Z (W64 0) = 0 := rfl
  refine ⟨by simp only []; omega, ⟨⟨hkey rfl, (hnc rfl).1, (hnc rfl).2⟩, hci, hterm, ?_, hwf⟩⟩
  simpa [hpre] using hrest

end draft

end EtcdGrove
end Perennial
